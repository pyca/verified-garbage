module

public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.AesXts.AArch64Unit
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.TCB.AArch64.Target
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesXts.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCbc.Mem
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Contract

/-!
# XTS-AES of data units on AArch64: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_ok`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

theorem save_eq : save = Spill.saveCode .x6 saved := rfl

theorem restore_eq : restore = Spill.restoreCode .x24 saved := rfl

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem shr4_shl4 (x : BitVec 64) : (x >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.reducePow]
  omega

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [show 8 * 0 = 0 from rfl, BitVec.extractLsb'_eq_self, show BitVec.ofNat 64 0 = 0#64 from rfl,
    BitVec.add_zero] at this
  exact this

theorem byte_rt (b : Byte) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem write_one (m : Mem) (a : Addr) (b : Byte) : m.write a 1 b = m.writeW a b := by simp [Mem.writeW]

theorem eval_nz {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.nonzero .x r) s = some (!decide (a = 0)) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  show some (BitVec.ofNat 64 a != 0#64) = _
  by_cases h0 : a = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 a ≠ 0#64 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this)
    simp [this, h0]

theorem eval_z {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero .x r) s = some (decide (a = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  show some (BitVec.ofNat 64 a == 0#64) = _
  by_cases h0 : a = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 a ≠ 0#64 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this)
    simp [this, h0]

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x9 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem setup_ok (s : State) :
    ∃ s', runBlock isa setup s = some s' ∧
      s'.gpr .x24 = s.gpr .x6 ∧ s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x2 ∧
      s'.gpr .x23 = s.gpr .x4 ∧ s'.gpr .x22 = s.gpr .x5 ∧
      (∀ r, r ≠ .x24 → r ≠ .x19 → r ≠ .x20 → r ≠ .x23 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [setup], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ => ?_, rfl, rfl, rfl, rfl⟩
  simp [gpr_write, h₁, h₂, h₃, h₄, h₅]

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem := (m.writeW c (0 : BitVec 64)).writeW (c + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem zero2_frame (m : Mem) (c : Addr) : Frame [⟨c, 16⟩] m (zero2 m c) := AesCbc.frame_store2 _ _ _

theorem zero2_bytes (m : Mem) (c : Addr) : bytesAt (zero2 m c) c 16 = List.replicate 16 0 := by
  rw [zero2, Proof.Cmac.bytesAt_store2]; decide

theorem zeroZ_ok (s : State) {Z : Addr} (hz : s.gpr .x24 + BitVec.ofNat 64 zO = Z)
    (hz8 : s.gpr .x24 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa zeroZ s = some s' ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = zero2 s.mem Z ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [zO] at hz hz8
  refine ⟨_, by crun [zeroZ, zO, hz, hz8, w0, w8], ?_⟩
  refine ⟨fun r h => by simp [gpr_write, h], rfl, ?_, rfl, rfl⟩
  simp only [zero2, Mem.writeW, BitVec.setWidth_eq]
  rfl

theorem tArgs_ok (s : State) :
    ∃ s', runBlock isa tArgs s = some s' ∧
      s'.gpr .x0 = s.gpr .x1 ∧ s'.gpr .x1 = s.gpr .x20 ∧
      s'.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 zO ∧ s'.gpr .x3 = s.gpr .x24 + BitVec.ofNat 64 tO ∧
      s'.gpr .x4 = BitVec.ofNat 64 1 ∧ s'.gpr .x5 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [tArgs, zO, tO], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write, zO], by simp [gpr_write, tO],
    by simp [gpr_write], by simp [gpr_write], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, -⟩ := preserved_ne r hr
  simp [gpr_write, h₀, h₁, h₂, h₃, h₄, h₅]

theorem argsAll_ok (s : State) :
    ∃ s', runBlock isa argsAll s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧
      s'.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 tO ∧ s'.gpr .x3 = s.gpr .x23 ∧
      s'.gpr .x4 = BitVec.ofNat 64 ((s.gpr .x22).toNat / 16) ∧ s'.gpr .x5 = s.gpr .x24 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [argsAll, tO], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write, tO], by simp [gpr_write],
    by simp [gpr_write, shr4], by simp [gpr_write], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, -⟩ := preserved_ne r hr
  simp [gpr_write, h₀, h₁, h₂, h₃, h₄, h₅]

theorem argsHead_ok (s : State) (hm : 1 ≤ (s.gpr .x22).toNat / 16) :
    ∃ s', runBlock isa argsHead s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧
      s'.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 tO ∧ s'.gpr .x3 = s.gpr .x23 ∧
      s'.gpr .x4 = BitVec.ofNat 64 ((s.gpr .x22).toNat / 16 - 1) ∧ s'.gpr .x5 = s.gpr .x24 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ := argsAll_ok s
  refine ⟨_, by
    rw [argsHead, runBlock_append, run₁, Option.bind_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, sp₁, mem₁, rd₁, wr₁⟩
  · simp [gpr_write, x0₁]
  · simp [gpr_write, x1₁]
  · simp [gpr_write, x2₁]
  · simp [gpr_write, x3₁]
  · simp only [gpr_write, ite_true, State.read, BitVec.setWidth_eq, x4₁]
    exact Offset.ofNat_sub_ofNat hm
  · simp [gpr_write, x5₁]
  · obtain ⟨-, -, -, -, h₄, -, -⟩ := preserved_ne r hr
    rw [gpr_write_of_ne (s := s₁) _ _ h₄]; exact cs₁ r hr

theorem split_ok (s : State) :
    ∃ s', runBlock isa split s = some s' ∧
      s'.gpr .x9 = BitVec.ofNat 64 (16 * ((s.gpr .x22).toNat / 16)) ∧
      s'.gpr .x10 = BitVec.ofNat 64 ((s.gpr .x22).toNat % 16) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have e : s.gpr .x22 - BitVec.ofNat 64 (16 * ((s.gpr .x22).toNat / 16)) =
      BitVec.ofNat 64 ((s.gpr .x22).toNat % 16) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .x22).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega)]
    omega
  refine ⟨_, by crun [split], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, shr4_shl4]
  · simp [gpr_write, shr4_shl4, e]

theorem lastAddr_ok (s : State) :
    ∃ s', runBlock isa lastAddr s = some s' ∧ s'.gpr .x11 = s.gpr .x23 + s.gpr .x9 - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [lastAddr], ?_⟩
  exact ⟨by simp [gpr_write], fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : Addr) {m : Nat} (hm : 1 ≤ m) :
    p + BitVec.ofNat 64 (16 * m) - BitVec.ofNat 64 16 = p + BitVec.ofNat 64 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega, ← Offset.add_add]
  exact BitVec.add_sub_cancel _ _

theorem argsL_ok (s : State) {o : Nat} (ho : o < 4096) :
    ∃ s', runBlock isa (argsL o) s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧
      s'.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 o ∧ s'.gpr .x3 = s.gpr .x23 + s.gpr .x9 - BitVec.ofNat 64 16 ∧
      s'.gpr .x4 = BitVec.ofNat 64 1 ∧ s'.gpr .x5 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [argsL, ho], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, -⟩ := preserved_ne r hr
  simp [gpr_write, h₀, h₁, h₂, h₃, h₄, h₅]

/-! ## The swap -/

theorem swapStep_ok (s : State) {L : Addr} {k b : Nat} (hx : s.gpr .x11 = L + BitVec.ofNat 64 k)
    (hc : s.gpr .x10 = BitVec.ofNat 64 b) (hb : 1 ≤ b)
    (w₀ : InRegions s.wr (L + BitVec.ofNat 64 k) 1) (w₁ : InRegions s.wr (L + BitVec.ofNat 64 (16 + k)) 1) :
    ∃ s', runBlock isa swapBody s = some s' ∧
      s'.mem = (s.mem.writeW (L + BitVec.ofNat 64 k) (s.mem (L + BitVec.ofNat 64 (16 + k)))).writeW
        (L + BitVec.ofNat 64 (16 + k)) (s.mem (L + BitVec.ofNat 64 k)) ∧
      s'.gpr .x11 = L + BitVec.ofNat 64 (k + 1) ∧ s'.gpr .x10 = BitVec.ofNat 64 (b - 1) ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 k) 1 :=
    let ⟨r, hr, c⟩ := w₀; ⟨r, List.mem_append_right _ hr, c⟩
  have r₁ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 (16 + k)) 1 :=
    let ⟨r, hr, c⟩ := w₁; ⟨r, List.mem_append_right _ hr, c⟩
  have e16 : L + BitVec.ofNat 64 k + BitVec.ofNat 64 16 = L + BitVec.ofNat 64 (16 + k) := by
    rw [Offset.add_add, Nat.add_comm]
  refine ⟨_, by
    crun [swapBody, hx, e16, r₀, r₁, w₀, w₁, read_one, byte_rt, write_one]
    , ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  · simp only [mem_write]
  · simp [gpr_write, Offset.add_add]
  · simp only [gpr_write, ↓reduceIte, BitVec.setWidth_eq, hc]
    exact Offset.ofNat_sub_ofNat hb

theorem swap_ok (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hx : s.gpr .x11 = L)
    (hc : s.gpr .x10 = BitVec.ofNat 64 b) (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => s'.mem = swapMem s.mem L b ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .nonzero .x .x10)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .x11 = L + BitVec.ofNat 64 k ∧
      t.gpr .x10 = BitVec.ofNat 64 (b - k) ∧ t.mem = swapMem s.mem L k ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr) ?_ (b - 0) _
    ⟨0, rfl, hb₀, by rw [hx, BitVec.add_zero], hc, (Proof.AesXts.Unit.swapMem_zero _ _).symm,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨k, rfl, hk, x11, x10, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x11', x10', g', sp', rd', wr'⟩ := swapStep_ok t (k := k) (b := b - k) x11 x10
    (by omega) (by rw [wr]; exact hw k (by omega)) (by rw [wr]; exact hw (16 + k) (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega), swapMem_hi _ _ (Nat.le_refl k) (by omega),
      swapMem_step _ _ (by omega)]
  have hz := eval_nz (s := t') x10' (by omega)
  have gg : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega], by rw [hmem, he], gg, by rw [sp', sp],
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega], b - (k + 1), by omega, k + 1, rfl, by omega, x11',
      by rw [x10', show b - k - 1 = b - (k + 1) by omega], hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩

/-! ## The next tweak -/

theorem nextT_ok (s : State) {T Z : Addr} (ht : s.gpr .x24 + BitVec.ofNat 64 tO = T)
    (ht8 : s.gpr .x24 + BitVec.ofNat 64 (tO + 8) = T + BitVec.ofNat 64 8)
    (hz : s.gpr .x24 + BitVec.ofNat 64 zO = Z) (hz8 : s.gpr .x24 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (hd : (⟨Z, 16⟩ : Region).Disjoint ⟨T, 16⟩)
    (r0 : InRegions (s.rd ++ s.wr) T 8) (r8 : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa nextT s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x21 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      Frame [⟨Z, 16⟩] s.mem s'.mem ∧ bytesAt s'.mem Z 16 = Spec.Xts.mulAlpha (bytesAt s.mem T 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have rz0 : InRegions (s.rd ++ s.wr) Z 8 := let ⟨r, hr, c⟩ := w0; ⟨r, List.mem_append_right _ hr, c⟩
  have rz8 : InRegions (s.rd ++ s.wr) (Z + BitVec.ofNat 64 8) 8 :=
    let ⟨r, hr, c⟩ := w8; ⟨r, List.mem_append_right _ hr, c⟩
  obtain ⟨s₁, run₁, x21₁⟩ : ∃ s₁, runBlock isa [.addImm .x .x21 .x24 zO] s = some s₁ ∧ s₁ = s.write .x .x21 Z := by
    refine ⟨_, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
    simp only [State.read, BitVec.setWidth_eq, hz]
  subst x21₁
  have g24 : (s.write .x .x21 Z).gpr .x24 = s.gpr .x24 := gpr_write_of_ne _ _ _ (by decide)
  obtain ⟨s₂, run₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ := AesCbc.AArch64.copy_ok (s.write .x .x21 Z) (dst := .x24)
    (src := .x24) (d := zO) (e := tO) (P := Z) (Q := T) (by rw [g24, hz])
    (by rw [g24, hz8]) (by rw [g24, ht]) (by rw [g24, ht8]) r0 r8 w0 w8 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := Proof.AesXts.AArch64.mulA_ok s₂ (Q := Z)
    (by rw [g₂ _ (by decide), gpr_write_self]; rfl) (by rw [rd₂, wr₂]; exact rz0) (by rw [rd₂, wr₂]; exact rz8)
    (by rw [wr₂]; exact w0) (by rw [wr₂]; exact w8)
  refine ⟨s₃, by
    rw [nextT, runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
      Option.bind_some, run₃], ?_⟩
  refine ⟨fun r h₉ h₁₀ h₁₁ h₁₂ h₂₁ => ?_, by rw [sp₃, sp₂]; rfl, ?_, ?_, by rw [rd₃, rd₂]; rfl,
    by rw [wr₃, wr₂]; rfl⟩
  · rw [g₃ r h₉ h₁₀ h₁₁ h₁₂, g₂ r h₉]; exact gpr_write_of_ne _ _ _ h₂₁
  · rw [mem₃, mem₂]
    exact (AesCbc.copyMem_frame _ _ _).trans (Proof.AesXts.AArch64.alphaMem_frame _ _)
  · rw [mem₃, Proof.AesXts.AArch64.alphaMem_bytes, mem₂, AesCbc.copyMem_bytes _ hd]; rfl

end VG.Proof.AesXts.AArch64.Unit
