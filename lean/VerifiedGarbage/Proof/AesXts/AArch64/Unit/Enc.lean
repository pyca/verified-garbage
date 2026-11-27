module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Impl.AesXts.AArch64Unit
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.AesXts.AArch64.Steps

/-! ### `AesXts.AArch64.Unit.Steps`, which this module and modules that import it used -/

section

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
    Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

theorem shr4_shl4 (x : BitVec 64) : (x >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  simp only [Nat.reducePow]
  omega_using []

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
  omega_using []

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
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega_using []),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega_using [])]
    omega_using []
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
  rw [show 16 * m = 16 * (m - 1) + 16 by omega_using [hm], ← Offset.add_add]
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
    (by omega_using [hk]) (by rw [wr]; exact hw k (by omega_using [hk])) (by rw [wr]; exact hw (16 + k) (by omega_using [hk]))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega_using [hb, hk]), swapMem_hi _ _ (Nat.le_refl k) (by omega_using [hb, hk]),
      swapMem_step _ _ (by omega_using [hb, hk])]
  have hz := eval_nz (s := t') x10' (by omega_using [hb])
  have gg : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega_using [he]], by rw [hmem, he], gg, by rw [sp', sp],
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega_using [hk, he]], b - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, he], x11',
      by rw [x10', show b - k - 1 = b - (k + 1) by omega_using []], hmem, gg, by rw [sp', sp], by rw [rd', rd],
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

end

end

/-! ### `AesXts.AArch64.Unit.Pre`, which this module and modules that import it used -/

section

/-! ### `AesXts.AArch64.Unit.Contract`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on AArch64: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean`, which imply `unitAArch64`
(`Verified.lean`): `(schedule = x0, tweak_schedule = x1, rounds = x2,
i = x3, data = x4, len = x5, scratch = x6)`. A call keeps its return
address in `x30`, so no stack is used.

`UPre` names the facts of the precondition; the regions of the scratch
buffer (`tR`, `zR`, `wkR`, the slots of the saved registers) are apart from
each other and from everything else.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : Addr := s.gpr .x0
abbrev K : Addr := s.gpr .x1
abbrev R : Nat := (s.gpr .x2).toNat
abbrev I : Addr := s.gpr .x3
abbrev D : Addr := s.gpr .x4
abbrev Len : Nat := (s.gpr .x5).toNat
abbrev S : Addr := s.gpr .x6

abbrev schR : Region := ⟨W s, 240⟩
abbrev tschR : Region := ⟨K s, 240⟩
abbrev iR : Region := ⟨I s, 16⟩
abbrev dataR : Region := ⟨D s, Len s⟩
abbrev scrR : Region := ⟨S s, 2432⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.AArch64Unit.tO, 16⟩
abbrev zR : Region := ⟨S s + BitVec.ofNat 64 Impl.AesXts.AArch64Unit.zO, 16⟩
abbrev wkR : Region := ⟨S s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := D s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, `rounds`
of 10, 12 or 14, and a data unit of 16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  s.rd = [schR s, tschR s, iR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧
    (I s).toNat + 16 ≤ 2 ^ 64 ∧ (D s).toNat + Len s ≤ 2 ^ 64 ∧ (S s).toNat + 2432 ≤ 2 ^ 64 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitAArch64 (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2).toNat key →
    xtsOf enc key (bytesAt s.mem (s.gpr .x3) 16) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      some (bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [schR s, tschR s, iR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  i_wrap : (I s).toNat + 16 ≤ 2 ^ 64
  data_wrap : (D s).toNat + Len s ≤ 2 ^ 64
  scr_wrap : (S s).toNat + 2432 ≤ 2 ^ 64
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega_using [this]

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega_using []

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨S s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨D s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.AArch64Unit.tO]; omega_using [])

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.AArch64Unit.zO]; omega_using [])

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.AArch64Unit.tO, Impl.AesXts.AArch64Unit.zO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.AArch64Unit.tO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.AArch64Unit.zO]; omega_using [])

omit hp in
/-- The slots of the saved registers. -/
theorem slot_sub (d : Nat) (h₁ : 2208 ≤ d) (h₂ : d + 8 ≤ 2264) :
    Region.Sub ⟨S s + BitVec.ofNat 64 d, 8⟩ ⟨S s + BitVec.ofNat 64 2208, 56⟩ :=
  Offset.sub _ h₁ (by omega_using [h₂])

/-- Everything the code writes but the slots lies within the data or the
first 2208 bytes of the scratch buffer. -/
theorem UPre.slots_disj {r : Region} (hr : Region.Sub r (dataR s) ∨ Region.Sub r ⟨S s, 2208⟩) :
    (⟨S s + BitVec.ofNat 64 2208, 56⟩ : Region).Disjoint r := by
  have slot : Region.Sub ⟨S s + BitVec.ofNat 64 2208, 56⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h
  · exact (hp.data_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])).sub_right h

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨S s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨S s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (D s).toNat + 16 * M s + B s ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := len_eq s; omega_arith

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨D s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega_using [h, this])

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.tl_eq : L s + 16 = D s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega_using [this]]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega_using [this])

theorem UPre.hd_lb : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega_arith)

theorem UPre.hd_l : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega_using []))

theorem UPre.hd_tl : (⟨D s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega_using []) (by have := hp.wrapD; omega_using [this])

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega_using [])

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨D s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega_using [this])

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨D s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.AArch64.Unit

end

end

/-! ### `AesXts.AArch64.Unit.Call`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on AArch64: a call of a whole-block function

`xts_call`: a call of `vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc`
true or false) for an implementation of the block functions, on `N` blocks
at `D`, from the tweak at `T`, with working space `S`, from its contract
(`WP.call`): the blocks are then XTS of them, the tweak the one after them,
and only the tweak, the blocks and `S` change. `xts_rel`: such calls, with
the same arguments in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64
open VG.Proof.AesCbc.AArch64 (modeAArch64 toNat_rounds)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : Addr) (N R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = T
  x3 : s.gpr .x3 = D
  x4 : s.gpr .x4 = BitVec.ofNat 64 N
  x5 : s.gpr .x5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 60
  wt : (⟨W, 240⟩ : Region).Disjoint ⟨T, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  td : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ts : (⟨T, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ds : (⟨D, 16 * N⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapT : T.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * N ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : Addr) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem D N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem W (16 * (R + 1)))) (bytesAt s.mem T 16)
      (Spec.Cbc.blocksAt s.mem D N)
  tw : bytesAt s'.mem T 16 = Spec.Xts.next (bytesAt s.mem T 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 60) : (BitVec.ofNat 64 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [h])

theorem callEntry_x5 (s : State) : s.callEntry.gpr .x5 = s.gpr .x5 := s.callEntry_gpr (by decide)

/-- The whole-block function's precondition, on entry to a call with the
regions it is given. -/
theorem XPre.mode_pre {enc : Bool} {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    (modeAArch64 (AesXts.xtsMode enc)).pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  simp only [modeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, AesCbc.AArch64.callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hN]
  exact ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, h.wrapT, h.wrapD, h.wrapS, h.rounds⟩

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s')
    (nf : c.noFrames = true)
    {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.call n c) s (XPost enc s W T D S N R) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  refine WP.call (k := modeAArch64 (AesXts.xtsMode enc)) ok (rd := [⟨W, 240⟩])
    (wr := [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) h.mode_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [modeAArch64, AesXts.xtsMode, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, AesCbc.AArch64.callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4, hR, hN,
    Proof.AesXts.Unit.length_blocksAt] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost.1, hpost.2⟩

/-- Calls of a whole-block function, with the same arguments in both runs,
are constant time. -/
theorem xts_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre (modeAArch64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, T, D, S, N, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.mode_pre (enc := enc), h₂.mode_pre (enc := enc), ?_, h₁.reads, h₁.writes, h₂.reads,
    h₂.writes⟩
  simp only [modeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, AesCbc.AArch64.callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.AArch64.Unit

end

end

/-!
# XTS-AES of data units on AArch64: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions
of the entry state and the call's arguments in its registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64
open VG.Impl.AesXts.AArch64Unit (tO zO)

theorem wrap_off (p : Addr) {d n k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d + n ≤ k) (hn : 0 < n := by decide) :
    (p + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [h, hd, hn]), Nat.mod_eq_of_lt (by omega_using [h, hd, hn])]
  omega_using [h, hd]

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
include hp hrd hwr

theorem xpre_tweak (x0 : s.gpr .x0 = K s₀) (x1 : s.gpr .x1 = BitVec.ofNat 64 (R s₀))
    (x2 : s.gpr .x2 = S s₀ + BitVec.ofNat 64 zO) (x3 : s.gpr .x3 = S s₀ + BitVec.ofNat 64 tO)
    (x4 : s.gpr .x4 = BitVec.ofNat 64 1) (x5 : s.gpr .x5 = S s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 64 zO) (S s₀ + BitVec.ofNat 64 tO) (S s₀) 1 (R s₀) where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := hp.rounds
  n := by decide
  wt := hp.tsch_scr.sub_right (sub_trans z_sub s_sub)
  wd := hp.tsch_scr.sub_right (sub_trans t_sub s_sub)
  ws := hp.tsch_scr.sub_right wk_sub
  td := hp.t_z.symm
  ts := hp.z_wk
  ds := hp.t_wk
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := wrap_off _ hp.scr_wrap (by decide)
  wrapS := by have := hp.scr_wrap; omega_using [this]
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (x0 : s.gpr .x0 = W s₀)
    (x1 : s.gpr .x1 = BitVec.ofNat 64 (R s₀)) (x2 : s.gpr .x2 = S s₀ + BitVec.ofNat 64 tO)
    (x3 : s.gpr .x3 = D s₀) (x4 : s.gpr .x4 = BitVec.ofNat 64 N) (x5 : s.gpr .x5 = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 tO) (D s₀) (S s₀) N (R s₀) where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := hp.rounds
  n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega_using [hN, this]
  wt := hp.sch_scr.sub_right (sub_trans t_sub s_sub)
  wd := hp.sch_data.sub_right (Region.sub_prefix hN)
  ws := hp.sch_scr.sub_right wk_sub
  td := (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right (Region.sub_prefix hN)
  ts := hp.t_wk
  ds := (hp.data_scr.sub_left (Region.sub_prefix hN)).sub_right wk_sub
  wrapT := wrap_off _ hp.scr_wrap (by decide)
  wrapD := by have := hp.data_wrap; omega_using [hN, this]
  wrapS := by have := hp.scr_wrap; omega_using [this]
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
    · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (x0 : s.gpr .x0 = W s₀)
    (x1 : s.gpr .x1 = BitVec.ofNat 64 (R s₀)) (x2 : s.gpr .x2 = S s₀ + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = L s₀) (x4 : s.gpr .x4 = BitVec.ofNat 64 1) (x5 : s.gpr .x5 = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀) := by
  have oS : Region.Sub ⟨S s₀ + BitVec.ofNat 64 o, 16⟩ ⟨S s₀, 2208⟩ := by
    rcases ho with rfl | rfl
    · exact t_sub
    · exact z_sub
  have oW : (⟨S s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have ol : o + 16 ≤ 2432 := by rcases ho with rfl | rfl <;> decide
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    x0 := x0
    x1 := x1
    x2 := x2
    x3 := x3
    x4 := x4
    x5 := x5
    rounds := hp.rounds
    n := by decide
    wt := hp.sch_scr.sub_right (sub_trans oS s_sub)
    wd := hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := (hp.data_scr.symm.sub_left (sub_trans oS s_sub)).sub_right lS
    ts := oW
    ds := (hp.data_scr.sub_left lS).sub_right wk_sub
    wrapT := wrap_off _ hp.scr_wrap ol
    wrapD := hp.l_wrap
    wrapS := by have := hp.scr_wrap; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simpa using ol⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

end

end VG.Proof.AesXts.AArch64.Unit

end

end

/-! ### `AesXts.AArch64.Unit.Run`, which only this module used -/

section

/-!
# XTS-AES of data units on AArch64: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps its arguments in `x19`, `x20`,
`x22`, `x23` and `x24`, its caller's callee-saved registers and its return
address in their slots, and changes memory only in the data and the scratch
buffer (`Inv.step`, for any code whose frame is in those). `tweak_wp`: the
prologue and the call enciphering the tweak value leave
`T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the epilogue
restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak. -/
abbrev Tp : Addr := S s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := S s₀ + BitVec.ofNat 64 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1))) (bytesAt s₀.mem (I s₀) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher := ciphOf enc (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  x19 : s.gpr .x19 = W s₀
  x20 : s.gpr .x20 = s₀.gpr .x2
  x22 : s.gpr .x22 = s₀.gpr .x5
  x23 : s.gpr .x23 = D s₀
  x24 : s.gpr .x24 = S s₀
  rest : ∀ r ∈ ([.x25, .x26, .x27, .x28] : List Reg), s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  saved : Spill.Saved (S s₀) s₀.gpr saved s.mem

theorem saved_bound : ∀ p ∈ saved, 2208 ≤ p.2 ∧ p.2 + 8 ≤ 2264 := by decide

/-- The registers `Inv` pins. -/
abbrev pinned : List Reg := [.x19, .x20, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

theorem rest_pinned : ∀ r ∈ ([.x25, .x26, .x27, .x28] : List Reg), r ∈ pinned := by decide

theorem pinned_pres : ∀ r ∈ pinned, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem x1_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .x2 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega_using [h])

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the registers and writes only within
`rs`, each in the data or the first 2208 bytes of the scratch buffer. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨S s₀, 2208⟩)
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  x19 := by rw [hg _ (by simp), h.x19]
  x20 := by rw [hg _ (by simp), h.x20]
  x22 := by rw [hg _ (by simp), h.x22]
  x23 := by rw [hg _ (by simp), h.x23]
  x24 := by rw [hg _ (by simp), h.x24]
  rest r hr := by
    rw [hg r (rest_pinned r hr), h.rest r hr]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ ⟨S s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ ⟨S s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨S s₀, 2176⟩]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr hT
      · exact hD
      · exact .inr (Region.sub_prefix (by decide)))
    hc.frame (fun r hr => hc.saved r (pinned_pres r hr).1 (pinned_pres r hr).2) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  rw [pro, List.append_assoc, List.append_assoc, List.append_assoc, save_eq]
  refine Spill.save_ok (l := saved) (b := .x6) (by decide) (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  rw [WP.block_append_iff]
  generalize hs₂ : ({ s₀ with mem := Spill.saveMem s₀.mem (s₀.gpr .x6) s₀.gpr saved } : State) = s₂
  have gpr₂ : s₂.gpr = s₀.gpr := by rw [← hs₂]
  have rd₂ : s₂.rd = s₀.rd := by rw [← hs₂]
  have wr₂ : s₂.wr = s₀.wr := by rw [← hs₂]
  have sp₂ : s₂.sp = s₀.sp := by rw [← hs₂]
  have mem₂ : s₂.mem = Spill.saveMem s₀.mem (S s₀) s₀.gpr saved := by rw [← hs₂]
  obtain ⟨s₃, run₃, x24₃, x19₃, x20₃, x23₃, x22₃, g₃, sp₃', mem₃', rd₃', wr₃'⟩ := setup_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [gpr₂] at x24₃ x19₃ x20₃ x23₃ x22₃
  have mem₃ : s₃.mem = Spill.saveMem s₀.mem (S s₀) s₀.gpr saved := by rw [mem₃', mem₂]
  have rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂]
  have wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂]
  have sp₃ : s₃.sp = s₀.sp := by rw [sp₃', sp₂]
  have k₃ : ∀ r, r ≠ .x24 → r ≠ .x19 → r ≠ .x20 → r ≠ .x23 → r ≠ .x22 → s₃.gpr r = s₀.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂]
  have rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  have wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  have cI0 : (iR s₀).Contains (I s₀) 8 := by
    simpa using Offset.contains_base (I s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  rw [WP.block_append_iff]
  have x3₃ : s₃.gpr .x3 = I s₀ := k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ := AesCbc.AArch64.copy_ok s₃ (dst := .x24) (src := .x3) (d := tO)
    (e := 0) (P := Tp s₀) (Q := I s₀) (by rw [x24₃]) (by rw [x24₃, ← Offset.add_add])
    (by rw [x3₃]; simp) (by rw [x3₃])
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) cI0)
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [wr₃'']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₃'', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [WP.block_append_iff]
  have wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  obtain ⟨s₅, run₅, g₅, sp₅, mem₅, rd₅, wr₅⟩ := zeroZ_ok s₄ (Z := Zp s₀)
    (by rw [g₄ _ (by decide), x24₃]) (by rw [g₄ _ (by decide), x24₃, ← Offset.add_add])
    (by rw [wr₄']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, x0₆, x1₆, x2₆, x3₆, x4₆, x5₆, cs₆, sp₆', mem₆, rd₆, wr₆⟩ := tArgs_ok s₅
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- The registers.
  have k₅ : ∀ r, r ≠ .x9 → s₅.gpr r = s₃.gpr r := fun r h => by rw [g₅ r h, g₄ r h]
  have x24₅ : s₅.gpr .x24 = S s₀ := by rw [k₅ _ (by decide), x24₃]
  have cs (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (preserved_ne r hr).2.2.2.2.2.2]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have sp₆ : s₆.sp = s₀.sp := by rw [sp₆', sp₅, sp₄, sp₃]
  -- The memory.
  have f₃ : Frame [scrR s₀] s₀.mem s₃.mem := by
    rw [mem₃]
    exact (Spill.saveMem_frame_base (n := 2264) (fun p hp' => (saved_bound p hp').2) (by decide) s₀.mem (S s₀)
      _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  have f₄ : Frame [⟨Tp s₀, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact AesCbc.copyMem_frame _ _ _
  have f₅ : Frame [⟨Zp s₀, 16⟩] s₄.mem s₅.mem := by rw [mem₅]; exact zero2_frame _ _
  have frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₃.trans ((f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  have sv₃ : Spill.Saved (S s₀) s₀.gpr saved s₃.mem := by
    rw [mem₃]; exact Spill.saveMem_saved (by decide) _ _ _
  have sdisj : ∀ (r : Region), Region.Sub r ⟨S s₀, 2208⟩ → ∀ p ∈ saved, ∀ r' ∈ [r],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj (.inr hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)
  have sv₆ : Spill.Saved (S s₀) s₀.gpr saved s₆.mem := by
    rw [mem₆]; exact (sv₃.frame f₄ (sdisj _ t_sub)).frame f₅ (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by simp [preserved]), x19₃], by rw [cs _ (by simp [preserved]), x20₃],
    by rw [cs _ (by simp [preserved]), x22₃], by rw [cs _ (by simp [preserved]), x23₃],
    by rw [cs _ (by simp [preserved]), x24₃], fun r hr => by
      have hr' : r ∈ preserved := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [cs r hr']
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), sp₆, rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · refine xpre_tweak hp rd₆' wr₆' ?_ ?_ (by rw [x2₆, x24₅]) (by rw [x3₆, x24₅]) x4₆ (by rw [x5₆, x24₅])
    · rw [x0₆, k₅ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [x1₆, k₅ _ (by decide), x20₃, x1_ofNat]
  · rw [mem₆, mem₅, Proof.Cmac.bytesAt_frame (zero2_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₄,
      AesCbc.copyMem_bytes _ (hp.i_scr.symm.sub_left (scr_sub (by simp [tO]))),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, mem₅, zero2_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s')
    (nf : c.noFrames = true) {s₂ : State} (h₂ : ProPost s₀ s₂) :
    WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nf h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp {f : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s')
    (nf : f.code.noFrames = true) :
    WP isa (tweak f) s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp ok nf h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem s.mem

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s')
    (nf : c.noFrames = true) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nf hpre) fun s' x => ?_
  have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  have eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  have eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.data_scr.sub_left dS) (by have := hp.data_wrap; omega_using [hN, this])
  refine ⟨Inv.call hp h.inv t_sub (.inl dS) x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eD]
  · rw [x.tw, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => hg r (pinned_pres r hr).1) hsp hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => GprAbi s₀ s' ∧ s'.mem = s.mem := by
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp (B := S s₀) h.x24 (by decide) (by decide) (fun p hp' => ?_) h.saved)
    fun s' r => ⟨⟨fun x hx => ?_, by rw [r.sp, h.sp]⟩, r.mem⟩
  · have := saved_bound p hp'
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact r.gpr_of (.inl (by decide))
      | exact r.gpr_of (.inr (h.rest _ (by simp)))

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub) hn

end

end VG.Proof.AesXts.AArch64.Unit

end

end


/-!
# XTS-AES of data units on AArch64: encryption

`encrypt_wp`: the tweak, the call on the whole blocks, and for a partial
block the swap and the call on the last whole block, then the epilogue,
for any implementation `f` of the whole-block encryption. The data unit is
`encWith` of the cipher and the tweak, which is `aesXtsEncrypt` of any key
whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (D s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s'

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  x9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (B s₀)

/-- `x23 + x9 − 16` is the last whole block. -/
theorem last_of {s : State} (h23 : s.gpr .x23 = D s₀) (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) :
    s.gpr .x23 + s.gpr .x9 - BitVec.ofNat 64 16 = L s₀ := by
  rw [h23, h9, last_eq _ hp.m_pos]

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) (h10 : s.gpr .x10 = BitVec.ofNat 64 (B s₀))
    (h11 : s.gpr .x11 = L s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have wr' : s.wr = [dataR s₀, scrR s₀] := by rw [hi.wr, hp.wr]
  refine WP.seq (WP.mono (swap_ok s (Nat.pos_of_ne_zero hB) hb h11 h10 (fun i hi' => by
      rw [wr']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi']) (by omega_using [hb, hi'])))))
    fun s₂ ⟨mem₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x0₃, x1₃, x2₃, x3₃, x4₃, x5₃, cs₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    argsL_ok s₂ (o := o) (by rcases ho with rfl | rfl <;> decide)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₂ (r : Reg) (hr : r ∈ pinned) : s₂.gpr r = s.gpr r := by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g₂ _ (by decide) (by decide) (by decide) (by decide)
  have inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₂ sp₂ rd₂ wr₂
  have inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₃]; exact Frame.refl _ _) (fun r hr => cs₃ r (pinned_pres r hr).1) sp₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr ho (by rw [x0₃, inv₂.x19])
    (by rw [x1₃, inv₂.x20, x1_ofNat]) (by rw [x2₃, inv₂.x24]) ?_ x4₃ (by rw [x5₃, inv₂.x24]), by rw [mem₃, mem₂]⟩
  rw [x3₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.x23 h9

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa (.call f.name f.code) s (Fin true s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  refine WP.mono (xts_call true ok nf h.pre) fun s₄ c => ?_
  have sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega_using [hb])
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l
      (sub_trans t_sub s_sub) c (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub s_sub) c
      (by dsimp only; omega_using [hb]), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .x11 = L s₀ → (∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block lastAddr) s Q := by
  obtain ⟨s', run', x11', g', sp', mem', rd', wr'⟩ := lastAddr_ok s
  exact WP.of_runBlock ⟨s', run', hq s' (by rw [x11']; exact last_of hp hi.x23 h9) g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_x11 {s s' : State} (hg : ∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) : ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => hg r (by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (lastAddr_wp hp h.all.inv h.x9 fun s₁ x11₁ g₁ sp₁ mem₁ rd₁ wr₁ => ?_))
  have h₁ := AllPost.keep hp h.all (keep_x11 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.x9])
    (by rw [g₁ _ (by decide), h.x10]) x11₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (encSteal f) s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp ok nf h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitAArch64 enc).post s₀ s' := by
  intro key hk
  have hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  have hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `x9`, and the bytes
after them in `x10`. -/
theorem split_wp {s : State} (h : Inv s₀ s) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .x9 = BitVec.ofNat 64 (16 * M s₀) → s'.gpr .x10 = BitVec.ofNat 64 (B s₀) →
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block split) s Q := by
  obtain ⟨s', run', x9', x10', g', sp', mem', rd', wr'⟩ := split_ok s
  rw [h.x22] at x9' x10'
  exact WP.of_runBlock ⟨s', run', hq s' x9' x10' g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_x9x10 {s s' : State} (hg : ∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) :
    ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) := by
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, x5₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := argsAll_ok s
  have h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr (N := M s₀)
    (by rw [len_eq s₀]; omega_using []) (by rw [x0₂, h.inv.x19]) (by rw [x1₂, h.inv.x20, x1_ofNat])
    (by rw [x2₂, h.inv.x24]) (by rw [x3₂, h.inv.x23]) (by rw [x4₂, h.inv.x22]) (by rw [x5₂, h.inv.x24])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  split_wp h.inv fun _ x9₄ x10₄ g₄ sp₄ mem₄ rd₄ wr₄ =>
    ⟨AllPost.keep hp h (keep_x9x10 g₄) sp₄ mem₄ rd₄ wr₄, x9₄, x10₄⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.gpr .x10 = BitVec.ofNat 64 (B s₀)) :
    isa.eval (.zero .x .x10) s = some (decide (B s₀ = 0)) :=
  eval_z h (by have : B s₀ < 16 := Nat.mod_lt _ (by decide); omega_using [this])

theorem encrypt_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true) :
    WP isa (Impl.AesXts.AArch64Unit.encrypt f) s₀ fun s' => GprAbi s₀ s' ∧ (unitAArch64 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp ok nf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true ok nf (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.x10)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp ok nf h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.AArch64.Unit
