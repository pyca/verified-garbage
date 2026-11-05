module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The FFDH controllers' words, zeros and tests (RISC-V)

What the controllers of `vg_ffdh_generate_key_search_cached`
(`Proof/Ffdh/RISCV64/Cached/SearchProof/`) and of the parameter search
(`Proof/Ffdh/RISCV64/Generation/Search/`) share: the registers their blocks
may write, the access to their words, a loop writing zeros, a block that
writes only those registers, and the values their tests compute.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.KeyGeneration

open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64

/-- The registers the controller's blocks may write, and the attempt too. -/
abbrev tmpRegs : List Reg :=
  [.ra, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]


/-- The loads and stores of the controller's words. -/
structure CtlAccess (s : State) (B : Addr) : Prop where
  ld : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  st : ∀ d, d + 8 ≤ 128 → InRegions s.wr (B + BitVec.ofNat 64 d) 8
  al : ∀ d, d + 8 ≤ 128 → d % 8 = 0 → (B + BitVec.ofNat 64 d).toNat % 8 = 0


theorem CtlAccess.of_scr {s : State} {B : Addr} (scr : Scr s B 128) : CtlAccess s B :=
  ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd, fun _ hd h8 => scr.al8 hd h8⟩


theorem ofs_off_self (o : Addr) {i : Nat} (h : i < 2 ^ 64) : Mont.ofs o (Mont.off o i) = i := by
  show (o + BitVec.ofNat 64 i - o).toNat = i
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]


/-- `p_len` zeros at `o` (`t0`), counted down in `t1`. -/
theorem zeroLoop_ok {s : State} {o : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32)
    (hx : ∀ i < k, InRegions s.wr (off o i) 1)
    (h0 : s.gpr .t0 = o) (h1 : s.gpr .t1 = BitVec.ofNat 64 k) (h2 : s.gpr .t2 = 0) :
    WP isa (Impl.Bignum.RISCV64.countLoop .t1 [.store .b .t2 .t0 0, .addi .t0 .t0 1]) s fun t =>
      ((∀ i < k, t.mem (off o i) = 0) ∧ Mont.Outside o 0 k s.mem t.mem) ∧ Keep [.t0, .t1] s t := by
  let Inv : Nat → State → Prop := fun j t => t.gpr .t0 = off o j ∧ t.gpr .t2 = 0 ∧
    Mont.Outside o 0 j s.mem t.mem ∧ (∀ i < j, t.mem (off o i) = 0) ∧ Keep [.t0, .t1] s t
  refine WP.mono (wp_countdown (cnt := .t1) (N := k) (by omega) (by omega) Inv
    (fun j hj t ⟨t0, t2, tout, tz, tk⟩ _ => ?_)
    ⟨by rw [h0]; simp only [off, BitVec.add_zero], h2, Mont.Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega), Keep.refl _ _⟩ h1)
    fun t ⟨_, _, tout, tz, kt⟩ => ⟨⟨tz, tout⟩, kt⟩
  have hst : InRegions t.wr (off o j) 1 := by rw [tk.2.2]; exact hx j hj
  refine WP.mono (WP.keep [.t0, .t1] (Q := fun u => u.gpr .t0 = off o (j + 1) ∧ u.gpr .t2 = 0 ∧
      u.gpr .t1 = t.gpr .t1 - BitVec.ofNat 64 1 ∧ u.mem = t.mem.write (off o j) 1 0) (by
    brun [t0, t2, hst, add_ofNat_zero]
    rfl) (by rfl) (by rfl)) fun u ⟨⟨u0, u2, u1, um⟩, ku⟩ =>
      ⟨⟨u0, u2, ?_, fun i hi => ?_, (tk.trans ku).mono (by decide)⟩, u1⟩
  · rw [um]
    exact (tout.mono (Nat.le_refl _) (by omega)).trans ((write1_outside t.mem o (d := j) _ (by omega)).mono
      (by omega) (by omega))
  · rw [um]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [write1_outside t.mem o (d := j) _ (by omega) _ (by rw [ofs_off_self o (by omega)]; omega)]
      exact tz i hi
    · exact write1_self _ _ _


/-- A block that writes only `tmpRegs` and the controller's words: what it
keeps of the state. -/
theorem WP.ctl {c : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block c) s Q)
    (hc : writesOnly tmpRegs (.block c) = true) :
    WP isa (.block c) s fun t => Q t ∧ Keep tmpRegs s t ∧ t.sp = s.sp :=
  WP.mono (WP.rdwr (WP.keep tmpRegs h hc rfl)) fun _ ⟨⟨hq, k⟩, _, _, hsp⟩ => ⟨hq, k, hsp⟩


theorem ofNat_pred {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt h]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega


theorem eval_ltu (s : State) (a b : Reg) : eval (.ltu a b) s = some (decide (s.gpr a < s.gpr b)) := rfl


theorem eval_zero' (s : State) (r : Reg) : eval (.zero r) s = some (s.gpr r == 0) := rfl


theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = decide (a < b) := by
  rw [decide_eq_decide, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]


/-- The low 32 bits of a register, by shifts. -/
theorem low32 {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    (x <<< 32) >>> 32 = BitVec.ofNat 64 st := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, ← h, BitVec.toNat_setWidth]
  have := x.isLt
  omega_arith


end VG.Proof.Ffdh.RISCV64.KeyGeneration
