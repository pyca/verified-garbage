module

public import VerifiedGarbage.Proof.AesCcm.AArch64.Env
public import VerifiedGarbage.Impl.AesCcm.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32

/-!
# AES-CCM on AArch64: checking a received tag (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` pads the `tl` bytes of
the received tag at `T` (in `x12`) and of the computed one at `W + 96` with
zeros, and
leaves 0 in `x10` if they are equal, 1 if not (`cmp_ok`), as AES-GCM's
`cmpSeg` does; `mask` ANDs every byte of the data with `x10 − 1`, sixteen at
a time (`maskVLoop_ok`) and then the last `n mod 16` one at a time
(`maskLoop_ok`): it keeps the data if the tags are equal, and overwrites it
with zeros if not (`mask_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok loopRegs Others add_ofNat_assoc eval_zero eval_nonzero
  words_eq pad_bytes carry_val in_of_covers succ_ofNat bytesAt_succ read_one writeBytes_frame' in_left)
open VG.Proof.AesCcm (length_bytesAt)

/-- `cmp`: 0 in `x10` iff the first `tl` bytes of the tag at `W + 96` are
those at `T`, in `x12`. -/
theorem cmp_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) (hx12 : s.gpr .x12 = c.T) :
    WP isa cmp s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64
        (if bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem c.T c.tl then 0 else 1) ∧
      Env c s' ∧ Others [.x9, .x10, .x11, .x12, .x13, .x14, .x15] s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem := by
  have ht4 := L.t4
  have ht16 := L.t16
  have w (d : Nat) (h : d + 8 ≤ 2560) := E.perm.wW h
  obtain ⟨s₁, run₁, hm₁, x11₁, x12₁, x13₁, og₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [imm .x9 0,
      .str .x .x9 .x19 vO, .str .x .x9 .x19 (vO + 8), .str .x .x9 .x19 rO, .str .x .x9 .x19 (rO + 8),
      ptr .x11 .x19 rO, mov .x13 .x20] s = some s₁ ∧
      s₁.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 264)
        (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 280)
          (0 : BitVec 64) ∧
      s₁.gpr .x11 = c.W + BitVec.ofNat 64 272 ∧ s₁.gpr .x12 = c.T ∧ s₁.gpr .x13 = BitVec.ofNat 64 c.tl ∧
      Others [.x9, .x11, .x13] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [E.x19, w 256 (by decide), w 264 (by decide), w 272 (by decide), w 280 (by decide)], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E.x19]
    · simp [gpr_write, hx12]
    · simp [gpr_write, E.x20]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq ?_
  have E₁ : Env c s₁ := E.others og₁ (by decide) sp₁ rd₁ wr₁
  have dW : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 272, c.tl⟩ :=
    L.t_w.sub_right (Lay.wSub (by omega_arith))
  have lp : LoopPre s₁ c.T (c.W + BitVec.ofNat 64 272) c.tl :=
    ⟨by omega_arith, E₁.perm.t, E₁.perm.wC (by omega_arith), dW⟩
  refine WP.mono (copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega_arith) lp) fun s₂ ⟨hm₂, _, _, og₂, sp₂, rd₂, wr₂⟩ => ?_
  have E₂ : Env c s₂ := E₁.others og₂ (by decide) sp₂ rd₂ wr₂
  refine WP.seq ?_
  obtain ⟨s₃, run₃, hm₃, x11₃, x12₃, x13₃, og₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [ptr .x11 .x19 vO,
      ptr .x12 .x19 uO, mov .x13 .x20] s₂ = some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x11 = c.W + BitVec.ofNat 64 256 ∧ s₃.gpr .x12 = c.W + BitVec.ofNat 64 96 ∧
      s₃.gpr .x13 = BitVec.ofNat 64 c.tl ∧
      Others [.x11, .x12, .x13] s₂ s₃ ∧ s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by carun [E₂.x19], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, E₂.x20]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have E₃ : Env c s₃ := E₂.others og₃ (by decide) sp₃ rd₃ wr₃
  have dU : (⟨c.W + BitVec.ofNat 64 96, c.tl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 256, c.tl⟩ :=
    L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have lp₃ : LoopPre s₃ (c.W + BitVec.ofNat 64 96) (c.W + BitVec.ofNat 64 256) c.tl :=
    ⟨by omega_arith, E₃.perm.wCR (by omega_arith), E₃.perm.wC (by omega_arith), dU⟩
  refine WP.seq (WP.mono (copyLoop_ok s₃ x12₃ x11₃ x13₃ (by omega_arith) lp₃)
    fun s₄ ⟨hm₄, _, _, og₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ : Env c s₄ := E₃.others og₄ (by decide) sp₄ rd₄ wr₄
  have r (d : Nat) (h : d + 8 ≤ 2560) := E₄.perm.wR h
  obtain ⟨s₅, run₅, x10₅, og₅, sp₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x9 .x19 vO, .ldr .x .x10 .x19 rO,
      .logic .eor .x .x9 .x9 .x10, .ldr .x .x10 .x19 (vO + 8), .ldr .x .x11 .x19 (rO + 8),
      .logic .eor .x .x10 .x10 .x11, .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1,
      .adds .x .x9 .x9 .x12, .adcs .x .x10 .x11 .x11] s₄ = some s₅ ∧
      s₅.gpr .x10 = BitVec.ofNat 64 (if (s₄.mem.readW (c.W + BitVec.ofNat 64 256) 64 ^^^
        s₄.mem.readW (c.W + BitVec.ofNat 64 272) 64) ||| (s₄.mem.readW (c.W + BitVec.ofNat 64 264) 64 ^^^
        s₄.mem.readW (c.W + BitVec.ofNat 64 280) 64) = 0 then 0 else 1) ∧
      Others [.x9, .x10, .x11, .x12] s₄ s₅ ∧ s₅.sp = s₄.sp ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by carun [E₄.x19, r 256 (by decide), r 264 (by decide), r 272 (by decide), r 280 (by decide),
      gpr_addWithCarry, c_addWithCarry, mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry,
      c_write], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, Size.bits, Nat.reduceAdd,
        show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv, Nat.reduceMul]
      exact carry_val _
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, gpr_addWithCarry, hr]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have e8 (a : Nat) : c.W + BitVec.ofNat 64 (a + 8) = c.W + BitVec.ofNat 64 a + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc c.W a 8).symm
  have hm₁' : s₁.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272)
        (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [hm₁, ← e8, ← e8]
  have fa := Proof.Cmac.frame_store2 (m := s.mem) (c.W + BitVec.ofNat 64 256) 0 0
  have fb := Proof.Cmac.frame_store2 (m := (s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) (c.W + BitVec.ofNat 64 272) 0 0
  have sR (d n : Nat) (h₁ : 256 ≤ d) (h₂ : d + n ≤ 288) :
      ∃ r' ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], Region.Sub ⟨c.W + BitVec.ofNat 64 d, n⟩ r' :=
    ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₁.mem := by
    rw [hm₁']
    refine (fa.sub fun r hr => ?_).trans (fb.sub fun r hr => ?_) <;>
      (simp only [List.mem_singleton] at hr; subst hr)
    · exact sR 256 16 (by decide) (by decide)
    · exact sR 272 16 (by decide) (by decide)
  have z₁ : bytesAt s₁.mem (c.W + BitVec.ofNat 64 272) 16 = zeros 16 := by
    rw [hm₁', Proof.Cmac.bytesAt_store2]; rfl
  have z₀ : bytesAt s₁.mem (c.W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [hm₁', Proof.AesGcm.AArch64.bytesAt_frame fb (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), Proof.Cmac.bytesAt_store2]; rfl
  have f₂ : Frame [⟨c.W + BitVec.ofNat 64 272, c.tl⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have f₄ : Frame [⟨c.W + BitVec.ofNat 64 256, c.tl⟩] s₂.mem s₄.mem := by
    rw [hm₄, hm₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have f₁₂ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₂.mem :=
    f₁.trans (f₂.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 272 c.tl (by decide) (by omega_arith))
  have f₁₄ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₄.mem :=
    f₁₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 256 c.tl (by decide) (by omega_arith))
  have hA : bytesAt s₁.mem c.T c.tl = bytesAt s.mem c.T c.tl :=
    Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.t_w.sub_right (Lay.wSub (by decide))) (by omega_arith)
  have hB : bytesAt s₂.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl :=
    Proof.AesGcm.AArch64.bytesAt_frame f₁₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by omega_arith)
  have p₁ : bytesAt s₂.mem (c.W + BitVec.ofNat 64 272) 16 = bytesAt s.mem c.T c.tl ++ zeros (16 - c.tl) := by
    rw [hm₂, pad_bytes z₁ _ (by rw [length_bytesAt]; omega_arith), length_bytesAt, hA]
    rfl
  have z₀' : bytesAt s₂.mem (c.W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by omega_arith))
      (by decide), z₀]
  have p₀ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 256) 16 =
      bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl ++ zeros (16 - c.tl) := by
    rw [hm₄, hm₃, pad_bytes z₀' _ (by rw [length_bytesAt]; omega_arith), length_bytesAt, hB]
    rfl
  have q₁ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 272) 16 = bytesAt s₂.mem (c.W + BitVec.ofNat 64 272) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega_arith)) (by decide) (by omega_arith))
      (by decide)
  have key : ((s₄.mem.readW (c.W + BitVec.ofNat 64 256) 64 ^^^ s₄.mem.readW (c.W + BitVec.ofNat 64 272) 64) |||
      (s₄.mem.readW (c.W + BitVec.ofNat 64 264) 64 ^^^ s₄.mem.readW (c.W + BitVec.ofNat 64 280) 64) = 0) ↔
      bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem c.T c.tl := by
    rw [show (264 : Nat) = 256 + 8 from rfl, show (280 : Nat) = 272 + 8 from rfl, e8 256, e8 272, words_eq, p₀,
      q₁, p₁]
    exact ⟨List.append_cancel_right, fun h => by rw [h]⟩
  have og : Others [.x9, .x10, .x11, .x12, .x13, .x14, .x15] s s₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h10, h11, h12, h13, h14, h15⟩ := hr
    have hl : r ∉ loopRegs := by simp [loopRegs, h11, h12, h13, h14, h15]
    rw [og₅ r (by simp [h9, h10, h11, h12]), og₄ r hl, og₃ r (by simp [h11, h12, h13]), og₂ r hl,
      og₁ r (by simp [h9, h11, h13])]
  refine ⟨by rw [x10₅]; simp only [key], E₄.others og₅ (by decide) sp₅ rd₅ wr₅, og, ?_⟩
  rw [m₅]; exact f₁₄

/-- The bytes at `D`, each ANDed with `b`. -/
def maskBytes (m : Mem) (D : Addr) (b : Byte) (n : Nat) : List Byte := (bytesAt m D n).map (· &&& b)

theorem length_maskBytes (m : Mem) (D : Addr) (b : Byte) (n : Nat) : (maskBytes m D b n).length = n := by
  simp [maskBytes, length_bytesAt]

theorem maskBytes_succ (m : Mem) (D : Addr) (b : Byte) (i : Nat) :
    maskBytes m D b (i + 1) = maskBytes m D b i ++ [m (D + BitVec.ofNat 64 i) &&& b] := by
  simp [maskBytes, bytesAt_succ]

theorem byte_and (a : BitVec (8 * 1)) (x : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) &&& BitVec.setWidth 32 x))) =
      a &&& x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 64 by omega_arith, show i < 32 by omega_arith,
    hi, decide_true, Bool.true_and]

/-- A byte at `D + i`, not yet written by a write of `i` bytes at `D`. -/
theorem writeBytes_at_len (m : Mem) (D : Addr) (xs : List Byte) {i : Nat} (hxs : xs.length = i)
    (hi : i < 2 ^ 64) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.lt_irrefl, ite_false]

abbrev maskRegs : List Reg := [.x12, .x13, .x14]

theorem maskStep_ok (s : State) {A : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A)
    (w : InRegions s.wr A 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧ s'.mem = s.mem.writeW A (s.mem A &&& (s.gpr .x11).setWidth 8) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      (∀ r, r ∉ maskRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wa := in_left (rd := s.rd) w
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, ha, w, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, byte_and, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
    done
  · simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    simp [gpr_write, h₁, h₂, h₃]

/-- The loop: the `n` (at least 1) bytes at `D` (`x12`) ANDed with the low
byte of `x11`. -/
theorem maskLoop_ok (s : State) {D : Addr} {n : Nat} (hD : s.gpr .x12 = D) (hn : s.gpr .x13 = BitVec.ofNat 64 n)
    (hpos : 0 < n) (hlt : n < 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block maskBody) (.nonzero .x .x13)) s fun s' =>
      s'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) n) ∧
      (∀ r, r ∉ maskRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = D + BitVec.ofNat 64 i ∧
      t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) i) ∧
      (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hpos, by rw [hD]; simp, by rw [hn, Nat.sub_zero],
      by simp [maskBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x13', g', sp', rd', wr'⟩ := maskStep_ok t
    (A := D + BitVec.ofNat 64 i) (by rw [x12, BitVec.add_zero])
    (by rw [wr]; exact in_of_covers hw hi hlt)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := length_maskBytes s.mem D ((s.gpr .x11).setWidth 8) i
  have x11t : t.gpr .x11 = s.gpr .x11 := g .x11 (by decide)
  have hmem : t'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) (i + 1)) := by
    rw [mem', mem, writeBytes_at_len _ _ _ hlen (by omega_arith), x11t, maskBytes_succ,
      writeBytes_snoc s.mem D _ _ (by rw [hlen]; omega_arith), hlen]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  have ev := eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega_arith)
  have gg : ∀ r, r ∉ maskRegs → t'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega_arith, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith,
      by rw [x12', x12, BitVec.add_assoc, succ_ofNat], x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩

theorem mask_byte {ok : Bool} :
    ((BitVec.ofNat 64 (if ok then 0 else 1) - 1 : BitVec 64).setWidth 8 : Byte) = if ok then 0xff else 0 := by
  cases ok <;> decide

/-! ## Sixteen bytes at a time -/

theorem vbyte_and (a b : BitVec 128) (i : Nat) : vbyte (a &&& b) i = vbyte a i &&& vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [vbyte, BitVec.getLsbD_extractLsb', hj]

/-- Sixteen bytes masked in place: `writeBytes` of them masked. -/
theorem writeW_mask (m : Mem) (A : Addr) (kb : Byte) :
    m.writeW A (m.readW A 128 &&& ofVBytes fun _ => kb) = writeBytes m A ((bytesAt m A 16).map (· &&& kb)) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, List.length_map, length_bytesAt, Nat.reduceDiv, Nat.reduceMul,
    BitVec.setWidth_eq]
  split
  · rename_i h
    have hb := Proof.Cmac.getD_bytesAt m A (n := 16) h
    have hl : (x - A).toNat < (bytesAt m A 16).length := by rw [length_bytesAt]; exact h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at hb
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
      Option.getD_some, hb]
    show vbyte _ _ = _
    rw [vbyte_and, Proof.Aes.AArch64.Aese.vbyte_readW _ _ h, VG.AArch64.vbyte_ofVBytes _ h]
  · rfl

theorem maskVStep_ok (s : State) {A : Addr} (ha : s.gpr .x12 = A) (w : InRegions s.wr A 16) :
    WP isa (.block maskV) s fun s' => s'.mem = s.mem.writeW A (s.mem.readW A 128 &&& s.v .v16) ∧
      s'.gpr .x12 = A + BitVec.ofNat 64 16 ∧ s'.gpr .x14 = s.gpr .x14 - 1 ∧ s'.v .v16 = s.v .v16 ∧
      Others [.x12, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wa := in_left (rd := s.rd) w
  simp only [maskV]
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq (t := .v17) (off := 0) (by decide) (by decide)
    (by rw [ha, BitVec.add_zero]; exact wa), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq (t := .v17) (off := 0) (by decide) (by decide)
    (by simpa only [gpr_setV, wr_setV, ha, BitVec.add_zero] using w), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, mem_setV, gpr_setV, v_setV_self, ha, BitVec.add_zero, Mem.writeW, Mem.readW,
      BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul, v_setV_of_ne _ _ (show VReg.v16 ≠ VReg.v17 by decide)]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, State.read, BitVec.setWidth_eq, Size.bits]
    show s.gpr .x12 + _ = _
    rw [ha]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, State.read, BitVec.setWidth_eq, Size.bits]
    rfl
  · simp only [v_write, v_setV_of_ne _ _ (show VReg.v16 ≠ VReg.v17 by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]
    rfl

/-- The bytes past what `writeBytes` wrote. -/
theorem bytesAt_writeBytes_after (m : Mem) (D : Addr) (xs : List Byte) (k : Nat) (h : xs.length + k < 2 ^ 64) :
    bytesAt (writeBytes m D xs) (D + BitVec.ofNat 64 xs.length) k = bytesAt m (D + BitVec.ofNat 64 xs.length) k := by
  apply List.ext_getElem (by simp [length_bytesAt])
  intro j h₁ h₂
  have hj : j < k := by rw [length_bytesAt] at h₂; exact h₂
  have e₁ := Proof.Cmac.getD_bytesAt (writeBytes m D xs) (D + BitVec.ofNat 64 xs.length) hj
  have e₂ := Proof.Cmac.getD_bytesAt m (D + BitVec.ofNat 64 xs.length) hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some] at e₁
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at e₂
  rw [e₁, e₂, Offset.add_add]
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show xs.length + j < 2 ^ 64 by omega_arith)]
  rw [ite_eq_right (by omega_arith)]

theorem maskVLoop_ok (s : State) {D : Addr} {q : Nat} {kb : Byte} (hd : s.gpr .x12 = D)
    (hq : s.gpr .x14 = BitVec.ofNat 64 q) (hq1 : 1 ≤ q) (hql : 16 * q < 2 ^ 64) (hv : s.v .v16 = ofVBytes fun _ => kb)
    (hw : Covers [⟨D, 16 * q⟩] s.wr) :
    WP isa (.loop (.block maskV) (.nonzero .x .x14)) s fun s' =>
      s'.mem = writeBytes s.mem D (maskBytes s.mem D kb (16 * q)) ∧ s'.gpr .x12 = D + BitVec.ofNat 64 (16 * q) ∧
      Others [.x12, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskV) (c := .nonzero .x .x14)
    (fun (k : Nat) (t : State) => ∃ i, k = q - i ∧ i < q ∧ t.gpr .x12 = D + BitVec.ofNat 64 (16 * i) ∧
      t.gpr .x14 = BitVec.ofNat 64 (q - i) ∧ t.mem = writeBytes s.mem D (maskBytes s.mem D kb (16 * i)) ∧
      t.v .v16 = s.v .v16 ∧ Others [.x12, .x14] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (q - 0) _
    ⟨0, rfl, by omega_arith, by rw [hd]; simp, by rw [hq, Nat.sub_zero], by simp [maskBytes, bytesAt, writeBytes_nil],
      rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x14, mem, v16, g, sp, rd, wr⟩
  refine WP.mono (maskVStep_ok t (A := D + BitVec.ofNat 64 (16 * i)) x12
    (by rw [wr]; exact Proof.AesGcm.AArch64.in_off hw (show 16 * i + 16 ≤ 16 * q by omega_arith) hql))
    fun t' ⟨mem', x12', x14', v16', g', sp', rd', wr'⟩ => ?_
  have hlen : (maskBytes s.mem D kb (16 * i)).length = 16 * i := length_maskBytes _ _ _ _
  have hmem : t'.mem = writeBytes s.mem D (maskBytes s.mem D kb (16 * (i + 1))) := by
    have hb := bytesAt_writeBytes_after s.mem D (maskBytes s.mem D kb (16 * i)) 16 (by rw [hlen]; omega_arith)
    have hap := writeBytes_append s.mem D (maskBytes s.mem D kb (16 * i))
      ((bytesAt s.mem (D + BitVec.ofNat 64 (16 * i)) 16).map (· &&& kb)) (by simp [length_maskBytes, length_bytesAt]; omega_arith)
    rw [hlen] at hb hap
    rw [mem', v16, hv, writeW_mask, mem, hb, hap]
    simp only [maskBytes]
    rw [show 16 * (i + 1) = 16 * i + 16 by omega_arith, Proof.Cmac.bytesAt_add, List.map_append]
  have x14'' : t'.gpr .x14 = BitVec.ofNat 64 (q - (i + 1)) := by
    rw [x14', x14, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  have ev := eval_nonzero (r := .x14) (a := q - (i + 1)) x14'' (by omega_arith)
  have gg : Others [.x12, .x14] s t' := fun r hr => by rw [g' r hr, g r hr]
  have x12'' : t'.gpr .x12 = D + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [x12', Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega_arith]
  by_cases he : i + 1 = q
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x12'', he], gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, q - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, x12'', x14'', hmem,
      by rw [v16', v16], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The mask -/

/-- `mask`: the data kept if `x10` is 0, zeros if it is 1. -/
theorem mask_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) {ok : Bool}
    (h10 : s.gpr .x10 = BitVec.ofNat 64 (if ok then 0 else 1)) :
    WP isa mask s fun s' =>
      bytesAt s'.mem c.D c.n = (if ok then bytesAt s.mem c.D c.n else zeros c.n) ∧
      Env c s' ∧ Others [.x11, .x12, .x13, .x14] s s' ∧ Frame [⟨c.D, c.n⟩] s.mem s'.mem := by
  have hn := L.n_lt
  have hq16 : 16 * (c.n / 16) ≤ c.n := Nat.mul_div_le _ _
  let kb : Byte := (BitVec.ofNat 64 (if ok then 0 else 1) - 1 : BitVec 64).setWidth 8
  have hkb : kb = if ok then 0xff else 0 := mask_byte
  have hres : ∀ m : Mem, (if ok then bytesAt m c.D c.n else zeros c.n) = maskBytes m c.D kb c.n := fun m => by
    rw [hkb]
    cases ok
    · simp only [maskBytes, Bool.false_eq_true, ite_false]
      apply List.ext_getElem (by simp [length_bytesAt, zeros])
      intro i h₁ h₂; simp [zeros]
    · simp only [maskBytes, ite_true]
      apply List.ext_getElem (by simp [length_bytesAt])
      intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_zipWith]
      generalize (bytesAt m c.D c.n)[i] = x
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (255 : BitVec 8).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt x.isLt]
  -- What `mask` leaves: the data masked.
  have fin : ∀ s', s'.mem = writeBytes s.mem c.D (maskBytes s.mem c.D kb c.n) → Env c s' →
      Others [.x11, .x12, .x13, .x14] s s' →
      bytesAt s'.mem c.D c.n = (if ok then bytesAt s.mem c.D c.n else zeros c.n) ∧
      Env c s' ∧ Others [.x11, .x12, .x13, .x14] s s' ∧ Frame [⟨c.D, c.n⟩] s.mem s'.mem := fun s' hm E' o' => by
    refine ⟨?_, E', o', by rw [hm]; exact writeBytes_frame' _ (length_maskBytes _ _ _ _)⟩
    rw [hm, Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [length_maskBytes]) hn,
      length_maskBytes, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil, hres]
  -- The mask, the pointer and the counts.
  have hpre : WP isa (.block [.subImm .x .x11 .x10 1, mov .x12 .x27, .vop (.dup .b16 .v16 .x11),
      .lsr .x .x14 .x28 4, .lsl .x .x13 .x14 4, .sub .x .x13 .x28 .x13]) s fun s₁ =>
      s₁.gpr .x11 = BitVec.ofNat 64 (if ok then 0 else 1) - 1 ∧ s₁.gpr .x12 = c.D ∧
      s₁.gpr .x14 = BitVec.ofNat 64 (c.n / 16) ∧ s₁.gpr .x13 = BitVec.ofNat 64 (c.n - 16 * (c.n / 16)) ∧
      s₁.v .v16 = (ofVBytes fun _ => kb) ∧ Others [.x11, .x12, .x13, .x14] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    rw [show ([.subImm .x .x11 .x10 1, mov .x12 .x27, .vop (.dup .b16 .v16 .x11),
        .lsr .x .x14 .x28 4, .lsl .x .x13 .x14 4, .sub .x .x13 .x28 .x13] : List Instr) =
        [.subImm .x .x11 .x10 1, mov .x12 .x27] ++
        (.vop (.dup .b16 .v16 .x11) :: [.lsr .x .x14 .x28 4, .lsl .x .x13 .x14 4, .sub .x .x13 .x28 .x13]) from rfl,
      WP.block_append_iff]
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun u hu => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun u₂ hu₂ => ?_⟩
    subst hu hu₂
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, gpr_setV, State.read, h10]
    · simp [gpr_write, gpr_setV, E.x27]
    · simp [gpr_write, gpr_setV, State.read, E.x28, Proof.AesGcm.AArch64.lsr_ofNat _ _ hn]
    · simp only [gpr_write, gpr_setV, ite_true, ite_false, reduceCtorEq, State.read, BitVec.setWidth_eq, Size.bits,
        E.x28]
      rw [Proof.AesGcm.AArch64.lsr_ofNat _ _ hn, Proof.AesGcm.AArch64.lsl4_ofNat,
        Proof.AesGcm.AArch64.ofNat_sub (by omega_arith) hn]
    · simp [v_write, gpr_write, State.read, kb, h10]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, gpr_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  refine WP.seq (WP.mono hpre fun s₁ ⟨x11₁, x12₁, x14₁, x13₁, v16₁, o₁, hm₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : Env c s₁ := E.others o₁ (by decide) sp₁ rd₁ wr₁
  -- Sixteen bytes at a time.
  have hvec : WP isa (.ite (.zero .x .x14) (.block []) (.loop (.block maskV) (.nonzero .x .x14))) s₁ fun s₂ =>
      s₂.mem = writeBytes s.mem c.D (maskBytes s.mem c.D kb (16 * (c.n / 16))) ∧
      s₂.gpr .x12 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧ Others [.x12, .x14] s₁ s₂ ∧ s₂.sp = s₁.sp ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine WP.ite (decide (c.n / 16 = 0)) (eval_zero x14₁ (by omega_arith)) (fun h => ?_) (fun h => ?_)
    · have h0 : c.n / 16 = 0 := by simpa using h
      refine WP.block_nil ⟨?_, by rw [x12₁, h0]; simp, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [h0, hm₁]; simp [maskBytes, bytesAt, writeBytes_nil]
    · have h1 : 1 ≤ c.n / 16 := by simp at h; omega_arith
      exact WP.mono (maskVLoop_ok s₁ x12₁ x14₁ h1 (by omega_arith) v16₁
        (Proof.AesGcm.AArch64.covers_prefix E₁.perm.d hq16)) fun s₂ ⟨m₂, x12₂, o₂, sp₂, rd₂, wr₂⟩ =>
          ⟨by rw [m₂, hm₁], x12₂, o₂, sp₂, rd₂, wr₂⟩
  refine WP.seq (WP.mono hvec fun s₂ ⟨m₂, x12₂, o₂, sp₂, rd₂, wr₂⟩ => ?_)
  have O₂ : Others [.x11, .x12, .x13, .x14] s s₂ := fun r hr => by
    rw [o₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.2.1, hr.2.2.2⟩),
      o₁ r hr]
  have E₂ : Env c s₂ := E.others O₂ (by decide) (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have x13₂ : s₂.gpr .x13 = BitVec.ofNat 64 (c.n - 16 * (c.n / 16)) := by rw [o₂ _ (by decide), x13₁]
  have x11₂ : s₂.gpr .x11 = s₁.gpr .x11 := o₂ _ (by decide)
  have hlq : (maskBytes s.mem c.D kb (16 * (c.n / 16))).length = 16 * (c.n / 16) := length_maskBytes _ _ _ _
  -- The last bytes, one at a time.
  refine WP.ite (decide (c.n - 16 * (c.n / 16) = 0)) (eval_zero x13₂ (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have h0 : c.n - 16 * (c.n / 16) = 0 := by simpa using h
    refine WP.block_nil (fin s₂ ?_ E₂ O₂)
    rw [m₂, show 16 * (c.n / 16) = c.n by omega_arith]
  · have h1 : 1 ≤ c.n - 16 * (c.n / 16) := by simp at h; omega_arith
    refine WP.mono (maskLoop_ok s₂ x12₂ x13₂ h1 (by omega_arith)
      (by rw [wr₂, wr₁]; exact Proof.AesGcm.AArch64.covers_off E.perm.d (by omega_arith) hn))
      fun s₃ ⟨m₃, o₃, sp₃, rd₃, wr₃⟩ => ?_
    have O₃ : Others [.x11, .x12, .x13, .x14] s s₃ := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [o₃ r (by simp [maskRegs, hr.2.1, hr.2.2.1, hr.2.2.2]), O₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
    refine fin s₃ ?_ (E.others O₃ (by decide) (by rw [sp₃, sp₂, sp₁]) (by rw [rd₃, rd₂, rd₁])
      (by rw [wr₃, wr₂, wr₁])) O₃
    have hb := bytesAt_writeBytes_after s.mem c.D (maskBytes s.mem c.D kb (16 * (c.n / 16)))
      (c.n - 16 * (c.n / 16)) (by rw [hlq]; omega_arith)
    have hap := writeBytes_append s.mem c.D (maskBytes s.mem c.D kb (16 * (c.n / 16)))
      ((bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n - 16 * (c.n / 16))).map (· &&& kb))
      (by simp [length_maskBytes, length_bytesAt]; omega_arith)
    rw [hlq] at hb hap
    have k₁ : (s₁.gpr .x11).setWidth 8 = kb := by rw [x11₁]
    rw [m₃, m₂, x11₂, k₁]
    simp only [maskBytes] at hb hap ⊢
    rw [hb, hap, ← List.map_append, ← Proof.Cmac.bytesAt_add, show 16 * (c.n / 16) + (c.n - 16 * (c.n / 16)) = c.n by
      omega_arith]

end VG.Proof.AesCcm.AArch64
