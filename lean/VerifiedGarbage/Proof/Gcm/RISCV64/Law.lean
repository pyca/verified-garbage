module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Proof.Gcm.RISCV64.Holes
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# GHASH on RISC-V meets its contract

Untrusted: everything here is checked by Lean. What the blocks of
`Impl/Gcm/RISCV64.lean` compute, as the functions of `Holes.lean`: a 32-bit
product (`holes_ok`), a 64-bit one (`pm_ok`) and a block (`block_ok`). Then
the blocks (`blocks_loop`, from `block_ok` and `Holes.mulK_eq`) and the
function (`ghash_ok`): the registers saved, the key prepared (`prep_ok`), `Y`
in, the blocks, `Y` out, the registers restored and the frame zeroed. That is
`GhashLaw` (`Ghash.lean`), which the registration files import for the
callers' proofs.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Gcm.RISCV64
open VG.Proof.Gcm.RISCV64.Holes (holes pm)

/-- Closes what `mrun` leaves of a block's postcondition: equations by
`rfl`, and `Keep` by the registers' inequalities. -/
macro "glue_close" : tactic => `(tactic| (
  simp only [Keep]
  repeat' (first
    | rfl
    | exact True.intro
    | constructor
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
       simp only [hr, ite_false]))))

/-- The registers `holesCode` writes. -/
def holesRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s8, .a6, .a7]

/-- The masks are in their registers. -/
def Masks (s : State) : Prop := ∀ i < 4, s.gpr (Impl.Gcm.RISCV64.K i) = Holes.K i

/-- The doubleword at `FP + d`, readable and aligned. -/
def Rd8 (s : State) (d : Nat) : Prop :=
  d < 2048 ∧ (s.gpr FP + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions (s.rd ++ s.wr) (s.gpr FP + BitVec.ofNat 64 d) 8

/-- The doubleword at `FP + d`. -/
def fw (s : State) (d : Nat) : BitVec 64 := s.mem.readW (s.gpr FP + BitVec.ofNat 64 d) 64

theorem holes_ok (s : State) (off : Nat) (hK : Masks s) (h0 : Rd8 s off) (h1 : Rd8 s (off + 8))
    (h2 : Rd8 s (off + 16)) (h3 : Rd8 s (off + 24)) :
    WP isa (.block (holesCode off)) s fun t =>
      t.gpr (Z 0) = holes (s.gpr HA) (fun j => fw s (off + 8 * j)) ∧ Keep holesRegs s t ∧
      t.mem = s.mem ∧ t.sp = s.sp := by
  obtain ⟨k0, k1, k2, k3⟩ : s.gpr .s0 = Holes.K 0 ∧ s.gpr .s1 = Holes.K 1 ∧ s.gpr .s2 = Holes.K 2 ∧
    s.gpr .s3 = Holes.K 3 := ⟨hK 0 (by decide), hK 1 (by decide), hK 2 (by decide), hK 3 (by decide)⟩
  obtain ⟨a0, b0, c0⟩ := h0
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  obtain ⟨a3, b3, c3⟩ := h3
  rw [show holesCode off = ([.logic .and .t0 .s4 .s0,
      .logic .and .t1 .s4 .s1,
      .logic .and .t2 .s4 .s2,
      .logic .and .t3 .s4 .s3,
      .load .d .a6 .s9 off,
      .mul .t4 .t0 .a6,
      .mul .t5 .t1 .a6,
      .mul .t6 .t2 .a6,
      .mul .s8 .t3 .a6,
      .load .d .a6 .s9 (off + 8),
      .mul .a7 .t0 .a6,
      .logic .xor .t5 .t5 .a7,
      .mul .a7 .t1 .a6,
      .logic .xor .t6 .t6 .a7,
      .mul .a7 .t2 .a6,
      .logic .xor .s8 .s8 .a7,
      .mul .a7 .t3 .a6,
      .logic .xor .t4 .t4 .a7,
      .load .d .a6 .s9 (off + 16),
      .mul .a7 .t0 .a6,
      .logic .xor .t6 .t6 .a7,
      .mul .a7 .t1 .a6,
      .logic .xor .s8 .s8 .a7,
      .mul .a7 .t2 .a6,
      .logic .xor .t4 .t4 .a7,
      .mul .a7 .t3 .a6,
      .logic .xor .t5 .t5 .a7,
      .load .d .a6 .s9 (off + 24),
      .mul .a7 .t0 .a6,
      .logic .xor .s8 .s8 .a7,
      .mul .a7 .t1 .a6,
      .logic .xor .t4 .t4 .a7,
      .mul .a7 .t2 .a6,
      .logic .xor .t5 .t5 .a7,
      .mul .a7 .t3 .a6,
      .logic .xor .t6 .t6 .a7,
      .logic .and .t4 .t4 .s0,
      .logic .and .t5 .t5 .s1,
      .logic .and .t6 .t6 .s2,
      .logic .and .s8 .s8 .s3,
      .logic .or .t4 .t4 .t5,
      .logic .or .t4 .t4 .t6,
      .logic .or .t4 .t4 .s8] : List Instr) from rfl]
  simp only [FP, HA, Z] at *
  mrun [k0, k1, k2, k3, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3]
  refine ⟨?_, show Keep _ _ _ from ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [holes, Holes.zc, fw, FP, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd,
      Nat.reduceMod]
  · simp only [holesRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_false]

/-- `pm` with its three tables given. -/
def pmT (x : BitVec 64) (bl bh bm : ℕ → BitVec 64) : BitVec 64 × BitVec 64 :=
  let l := holes (Holes.lo32 x) bl
  let h := holes (Holes.hi32 x) bh
  let m := holes (Holes.lo32 x ^^^ Holes.hi32 x) bm ^^^ l ^^^ h
  (l ^^^ m <<< 32, h ^^^ m >>> 32)

theorem pmT_eq (x y : BitVec 64) :
    pmT x (fun j => Holes.lo32 y &&& Holes.K j) (fun j => Holes.hi32 y &&& Holes.K j)
      (fun j => (Holes.lo32 y ^^^ Holes.hi32 y) &&& Holes.K j) = pm x y := rfl

/-- The registers `pmCode` writes. -/
def pmRegs : List Reg := holesRegs ++ [.s4, .s5, .s6, .s7]

theorem Keep.masks {rs : List Reg} {s t : State} (h : Keep rs s t) (hm : Masks s)
    (hr : ∀ i < 4, Impl.Gcm.RISCV64.K i ∉ rs) : Masks t :=
  fun i hi => by rw [h.gpr (hr i hi)]; exact hm i hi

theorem Keep.rd8 {rs : List Reg} {s t : State} (h : Keep rs s t) (hr : FP ∉ rs) {d : Nat} (hd : Rd8 s d) :
    Rd8 t d := by
  obtain ⟨a, b, c⟩ := hd
  refine ⟨a, ?_, ?_⟩
  · rw [h.gpr hr]; exact b
  · rw [h.gpr hr, h.2.1, h.2.2]; exact c

theorem fw_congr {s t : State} (hm : t.mem = s.mem) (hf : t.gpr FP = s.gpr FP) (d : Nat) : fw t d = fw s d := by
  simp only [fw, hm, hf]

def pmG1 (X : Reg) : List Instr := [.shift .srl .d XH X 32, .shift .sll .d HA X 32, .shift .srl .d HA HA 32]
def pmG2 : List Instr := [.addi PL (Z 0) 0, .logic .xor HA HA XH]
def pmG3 : List Instr := [.addi PM (Z 0) 0, .addi HA XH 0]
def pmG4 : List Instr :=
  [.logic .xor PM PM PL, .logic .xor PM PM (Z 0),
   .shift .sll .d T PM 32, .logic .xor PL PL T, .shift .srl .d T PM 32, .logic .xor (Z 0) (Z 0) T]

theorem pmCode_eq (X : Reg) (off : Nat) : pmCode X off = pmG1 X ++ (holesCode off ++ (pmG2 ++
    (holesCode (off + 64) ++ (pmG3 ++ (holesCode (off + 32) ++ pmG4))))) := by
  simp only [pmCode, pmG1, pmG2, pmG3, pmG4, List.append_assoc, List.cons_append, List.nil_append]

theorem g1_ok (s : State) {X : Reg} (h5 : X ≠ .s5) :
    WP isa (.block (pmG1 X)) s fun t => t.gpr HA = Holes.lo32 (s.gpr X) ∧ t.gpr XH = Holes.hi32 (s.gpr X) ∧
      Keep [.s4, .s5] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  unfold pmG1
  simp only [HA, XH]
  mrun [h5, Ne.symm h5]
  glue_close

theorem g2_ok (s : State) :
    WP isa (.block pmG2) s fun t => t.gpr PL = s.gpr (Z 0) ∧ t.gpr HA = s.gpr HA ^^^ s.gpr XH ∧
      Keep [.s6, .s4] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  unfold pmG2
  simp only [HA, XH, PL, Z]
  mrun
  glue_close

theorem g3_ok (s : State) :
    WP isa (.block pmG3) s fun t => t.gpr PM = s.gpr (Z 0) ∧ t.gpr HA = s.gpr XH ∧
      Keep [.s7, .s4] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  unfold pmG3
  simp only [HA, XH, PM, Z]
  mrun
  glue_close

theorem g4_ok (s : State) :
    WP isa (.block pmG4) s fun t =>
      t.gpr PL = s.gpr PL ^^^ (s.gpr PM ^^^ s.gpr PL ^^^ s.gpr (Z 0)) <<< 32 ∧
      t.gpr (Z 0) = s.gpr (Z 0) ^^^ (s.gpr PM ^^^ s.gpr PL ^^^ s.gpr (Z 0)) >>> 32 ∧
      Keep [.s7, .a7, .s6, .t4] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  unfold pmG4
  simp only [PL, PM, T, Z]
  mrun
  glue_close

theorem pm_ok (s : State) {X : Reg} (hX : X ∉ pmRegs) (off : Nat) (hK : Masks s)
    (hR : ∀ k < 12, Rd8 s (off + 8 * k)) :
    WP isa (.block (pmCode X off)) s fun t =>
      t.gpr PL = (pmT (s.gpr X) (fun j => fw s (off + 8 * j)) (fun j => fw s (off + 32 + 8 * j))
        (fun j => fw s (off + 64 + 8 * j))).1 ∧
      t.gpr (Z 0) = (pmT (s.gpr X) (fun j => fw s (off + 8 * j)) (fun j => fw s (off + 32 + 8 * j))
        (fun j => fw s (off + 64 + 8 * j))).2 ∧
      Keep pmRegs s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  have hX' := hX
  simp only [pmRegs, holesRegs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hX'
  have mk : ∀ (rs : List Reg), Reg.s0 ∉ rs → Reg.s1 ∉ rs → Reg.s2 ∉ rs → Reg.s3 ∉ rs →
      ∀ i < 4, Impl.Gcm.RISCV64.K i ∉ rs := by
    intro rs a b c d i hi; interval_cases i; exacts [a, b, c, d]
  have fp : ∀ (rs : List Reg), Reg.s9 ∉ rs → FP ∉ rs := fun _ h => h
  rw [pmCode_eq]
  refine WP.block_append_iff.mpr (WP.mono (g1_ok s hX'.2.2.2.2.2.2.2.2.2.2.2.1) fun u1 ⟨e1, e2, k1, m1, p1⟩ => ?_)
  have K1 := Keep.masks k1 hK (mk _ (by decide) (by decide) (by decide) (by decide))
  have R1 : ∀ k < 12, Rd8 u1 (off + 8 * k) := fun k hk => Keep.rd8 k1 (fp _ (by decide)) (hR k hk)
  have F1 : ∀ d, fw u1 d = fw s d := fw_congr m1 (Keep.gpr k1 (by decide))
  refine WP.block_append_iff.mpr (WP.mono (holes_ok u1 off K1 (R1 0 (by decide)) (R1 1 (by decide))
    (R1 2 (by decide)) (R1 3 (by decide))) fun u2 ⟨e3, k2, m2, p2⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (g2_ok u2) fun u3 ⟨e4, e5, k3, m3, p3⟩ => ?_)
  have k23 := Keep.trans k2 k3
  have K3 := Keep.masks k23 K1 (mk _ (by decide) (by decide) (by decide) (by decide))
  have R3 : ∀ k < 12, Rd8 u3 (off + 8 * k) := fun k hk => Keep.rd8 k23 (fp _ (by decide)) (R1 k hk)
  have F3 : ∀ d, fw u3 d = fw s d := fun d => by rw [fw_congr (m3.trans m2) (Keep.gpr k23 (by decide)), F1]
  refine WP.block_append_iff.mpr (WP.mono (holes_ok u3 (off + 64) K3
    (by simpa using R3 8 (by decide)) (by simpa [Nat.add_assoc] using R3 9 (by decide))
    (by simpa [Nat.add_assoc] using R3 10 (by decide)) (by simpa [Nat.add_assoc] using R3 11 (by decide)))
    fun u4 ⟨e6, k4, m4, p4⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (g3_ok u4) fun u5 ⟨e7, e8, k5, m5, p5⟩ => ?_)
  have k45 := Keep.trans k4 k5
  have K5 := Keep.masks k45 K3 (mk _ (by decide) (by decide) (by decide) (by decide))
  have R5 : ∀ k < 12, Rd8 u5 (off + 8 * k) := fun k hk => Keep.rd8 k45 (fp _ (by decide)) (R3 k hk)
  have F5 : ∀ d, fw u5 d = fw s d := fun d => by rw [fw_congr (m5.trans m4) (Keep.gpr k45 (by decide)), F3]
  refine WP.block_append_iff.mpr (WP.mono (holes_ok u5 (off + 32) K5
    (by simpa using R5 4 (by decide)) (by simpa [Nat.add_assoc] using R5 5 (by decide))
    (by simpa [Nat.add_assoc] using R5 6 (by decide)) (by simpa [Nat.add_assoc] using R5 7 (by decide)))
    fun u6 ⟨e9, k6, m6, p6⟩ => ?_)
  refine WP.mono (g4_ok u6) fun t ⟨e10, e11, k7, m7, p7⟩ => ?_
  have F6 : ∀ d, fw u5 d = fw s d := F5
  have pl6 : u6.gpr PL = u3.gpr PL := by
    rw [Keep.gpr k6 (by decide), Keep.gpr k5 (by decide), Keep.gpr k4 (by decide)]
  have pm6 : u6.gpr PM = u5.gpr PM := Keep.gpr k6 (by decide)
  have ha2 : u2.gpr HA = u1.gpr HA := Keep.gpr k2 (by decide)
  have xh2 : u2.gpr XH = u1.gpr XH := Keep.gpr k2 (by decide)
  have xh4 : u4.gpr XH = u1.gpr XH := by
    rw [Keep.gpr k4 (by decide), Keep.gpr k3 (by decide), xh2]
  have hl : u3.gpr PL = holes (Holes.lo32 (s.gpr X)) (fun j => fw s (off + 8 * j)) := by
    rw [e4, e3, e1]; simp only [F1]
  have hm : u5.gpr PM = holes (Holes.lo32 (s.gpr X) ^^^ Holes.hi32 (s.gpr X)) (fun j => fw s (off + 64 + 8 * j)) := by
    rw [e7, e6, e5, ha2, xh2, e1, e2]; simp only [F3]
  have hh : u6.gpr (Z 0) = holes (Holes.hi32 (s.gpr X)) (fun j => fw s (off + 32 + 8 * j)) := by
    rw [e9, e8, xh4, e2]; simp only [F5]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e10, pl6, pm6, hl, hm, hh]; rfl
  · rw [e11, pl6, pm6, hl, hm, hh]; rfl
  · refine Keep.mono (Keep.trans k1 (Keep.trans k2 (Keep.trans k3 (Keep.trans k4 (Keep.trans k5
      (Keep.trans k6 k7)))))) ?_
    simp only [pmRegs, holesRegs]; decide
  · rw [m7, m6, m5, m4, m3, m2, m1]
  · rw [p7, p6, p5, p4, p3, p2, p1]

/-! ## The frame's slots -/

theorem slot_sep (b : Addr) {j k : Nat} (hj : 8 * j < 2 ^ 64) (hk : 8 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (b + BitVec.ofNat 64 (8 * j)) 8 (b + BitVec.ofNat 64 (8 * k)) 8 := by
  intro x h₁ h₂
  simp only [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - b).isLt
  omega

/-- A store to slot `k` keeps every other slot. -/
theorem fw_writeW {s : State} {m : Mem} (v : BitVec 64) {j k : Nat} (hj : j < 256) (hk : k < 256) (h : j ≠ k) :
    (m.writeW (s.gpr FP + BitVec.ofNat 64 (8 * k)) v).readW (s.gpr FP + BitVec.ofNat 64 (8 * j)) 64 =
      m.readW (s.gpr FP + BitVec.ofNat 64 (8 * j)) 64 :=
  Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) h) (by decide)

/-- The stores of `st2 k`: `PL` and `Z₀` to slots `k` and `k + 1`. -/
def st2 (k : Nat) : List Instr := [.store .d PL FP (slot k), .store .d (Z 0) FP (slot (k + 1))]

/-- The doubleword at `FP + d`, writable and aligned. -/
def Wr8 (s : State) (d : Nat) : Prop :=
  d < 2048 ∧ (s.gpr FP + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions s.wr (s.gpr FP + BitVec.ofNat 64 d) 8

theorem st2_ok (s : State) (k : Nat) (h0 : Wr8 s (slot k)) (h1 : Wr8 s (slot (k + 1))) :
    WP isa (.block (st2 k)) s fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = (s.mem.writeW (s.gpr FP + BitVec.ofNat 64 (slot k)) (s.gpr PL)).writeW
        (s.gpr FP + BitVec.ofNat 64 (slot (k + 1))) (s.gpr (Z 0)) := by
  obtain ⟨a0, b0, c0⟩ := h0
  obtain ⟨a1, b1, c1⟩ := h1
  unfold st2
  simp only [FP, PL, Z] at *
  mrun [a0, a1, b0, b1, c0, c1]

/-! ## Two big-endian words -/

/-- Two big-endian words read a byte at a time: `loadBE64` twice, into `d₀`
and `d₁` through `tmp`, from `n`. -/
theorem ld2_ok {d₀ d₁ tmp n : Reg} (h0n : d₀ ≠ n) (h1n : d₁ ≠ n) (htn : tmp ≠ n) (h0t : d₀ ≠ tmp)
    (h1t : d₁ ≠ tmp) (h01 : d₀ ≠ d₁) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr n) 16) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 d₀ tmp n 0 ++ Impl.Words.RISCV64.loadBE64 d₁ tmp n 8)) s
      fun t => t.gpr d₀ = ByteLoad.be64 s.mem (s.gpr n) 0 ∧ t.gpr d₁ = ByteLoad.be64 s.mem (s.gpr n) 8 ∧
        Keep [d₀, d₁, tmp] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  have hin8 : ∀ off, off + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8 :=
    fun off ho => CallLay.inRegions_sub hin ho (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok h0n htn h0t (by decide) (hin8 0 (by decide))) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (ByteLoad.loadBE64_ok h1n htn h1t (by decide) ?_) fun s₂ e₂ => ?_
  · simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, Ne.symm htn, Ne.symm h0n] using hin8 8 (by decide)
  · subst e₂
    refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [RegUpd.gpr_write, h01, h0t, Ne.symm h0n, Ne.symm htn]
    · simp [RegUpd.gpr_write, RegUpd.mem_write, Ne.symm h0n, Ne.symm htn]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2]
    · simp [RegUpd.rd_write]
    · simp [RegUpd.wr_write]
    · simp [RegUpd.mem_write]
    · simp [RegUpd.sp_write]

/-! ## A block -/

/-- The block's last instructions: the spilled products back, the four words
of the product and its reduction. -/
def bTail : List Instr :=
  [.load .d .t0 FP (slot 36), .load .d .t1 FP (slot 37), .load .d .t2 FP (slot 38), .load .d .t3 FP (slot 39),
   .logic .xor B (Z 0) .t1, .logic .xor B B .t3, .logic .xor B .t0 B,
   .logic .xor T PL .t0, .logic .xor T T .t2, .logic .xor T T .t3,
   .shift .sll .d .t4 .t2 63, .logic .xor T T .t4, .shift .sll .d .t4 .t2 62, .logic .xor T T .t4,
   .shift .sll .d .t4 .t2 57, .logic .xor T T .t4,
   .logic .xor B B .t2, .shift .srl .d .t4 .t2 1, .logic .xor B B .t4, .shift .srl .d .t4 .t2 2,
   .logic .xor B B .t4, .shift .srl .d .t4 .t2 7, .logic .xor B B .t4,
   .logic .xor Y0 .t1 T, .shift .srl .d .t4 T 1, .logic .xor Y0 Y0 .t4, .shift .srl .d .t4 T 2,
   .logic .xor Y0 Y0 .t4, .shift .srl .d .t4 T 7, .logic .xor Y0 Y0 .t4,
   .shift .sll .d .t4 T 63, .logic .xor Y1 B .t4, .shift .sll .d .t4 T 62, .logic .xor Y1 Y1 .t4,
   .shift .sll .d .t4 T 57, .logic .xor Y1 Y1 .t4,
   .addi DP DP 16, .addi N N (-1)]

/-- The block's first instructions: `x` loaded and `Y ⊕ X`. -/
def bXor : List Instr := [.logic .xor Y0 Y0 .t0, .logic .xor Y1 Y1 .t1]

theorem blockCode_eq : blockCode = Impl.Words.RISCV64.loadBE64 .t0 .t2 DP 0 ++
    Impl.Words.RISCV64.loadBE64 .t1 .t2 DP 8 ++ (bXor ++ (pmCode Y0 (slot 0) ++ (st2 36 ++
    (pmCode Y1 (slot 12) ++ (st2 38 ++ (([.logic .xor Y0 Y0 Y1] : List Instr) ++ (pmCode Y0 (slot 24) ++ bTail))))))) := by
  simp only [blockCode, bXor, st2, bTail, List.append_assoc, List.cons_append, List.nil_append]

/-- The registers `bTail` writes. -/
def tailRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .a6, .a7, .a4, .a5, .a2, .a3]

theorem bTail_ok (s : State) (h0 : Rd8 s (slot 36)) (h1 : Rd8 s (slot 37)) (h2 : Rd8 s (slot 38))
    (h3 : Rd8 s (slot 39)) :
    WP isa (.block bTail) s fun t =>
      t.gpr Y0 ++ t.gpr Y1 = Holes.reduce (fw s (slot 37))
        (fw s (slot 36) ^^^ (s.gpr (Z 0) ^^^ fw s (slot 37) ^^^ fw s (slot 39)))
        ((s.gpr PL ^^^ fw s (slot 36) ^^^ fw s (slot 38)) ^^^ fw s (slot 39)) (fw s (slot 38)) ∧
      t.gpr DP = s.gpr DP + 16 ∧ t.gpr N = s.gpr N - 1 ∧
      Keep tailRegs s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  obtain ⟨a0, b0, c0⟩ := h0
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  obtain ⟨a3, b3, c3⟩ := h3
  unfold bTail
  simp only [FP, PL, Z, B, T, Y0, Y1, DP, N, slot, fw] at *
  mrun [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3]
  simp only [Holes.reduce, Holes.foldLo, Holes.foldHi, tailRegs]
  glue_close

theorem bXor_ok (s : State) :
    WP isa (.block bXor) s fun t => t.gpr Y0 = s.gpr Y0 ^^^ s.gpr .t0 ∧ t.gpr Y1 = s.gpr Y1 ^^^ s.gpr .t1 ∧
      Keep [.a4, .a5] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  unfold bXor
  simp only [Y0, Y1]
  mrun
  glue_close

theorem bY_ok (s : State) :
    WP isa (.block [.logic .xor Y0 Y0 Y1]) s fun t => t.gpr Y0 = s.gpr Y0 ^^^ s.gpr Y1 ∧
      Keep [.a4] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  simp only [Y0, Y1]
  mrun
  glue_close

/-- The product of a block, the table given by the doubleword at each
offset of the frame. -/
def mulT (y0 y1 : BitVec 64) (f : ℕ → BitVec 64) : BitVec 128 :=
  let l := pmT y0 (fun j => f (slot 0 + 8 * j)) (fun j => f (slot 0 + 32 + 8 * j)) (fun j => f (slot 0 + 64 + 8 * j))
  let h := pmT y1 (fun j => f (slot 12 + 8 * j)) (fun j => f (slot 12 + 32 + 8 * j))
    (fun j => f (slot 12 + 64 + 8 * j))
  let m := pmT (y0 ^^^ y1) (fun j => f (slot 24 + 8 * j)) (fun j => f (slot 24 + 32 + 8 * j))
    (fun j => f (slot 24 + 64 + 8 * j))
  Holes.reduce l.2 (l.1 ^^^ (m.2 ^^^ l.2 ^^^ h.2)) ((m.1 ^^^ l.1 ^^^ h.1) ^^^ h.2) h.1

/-- What a block needs of its state. -/
structure BlkPre (s : State) : Prop where
  masks : Masks s
  rd : ∀ k < 40, Rd8 s (8 * k)
  wr : ∀ k, 36 ≤ k → k < 40 → Wr8 s (8 * k)
  dat : InRegions (s.rd ++ s.wr) (s.gpr DP) 16

/-- The registers a block writes. -/
def blockRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s8, .a6, .a7, .s4, .s5, .s6, .s7, .a4, .a5, .a2, .a3]

theorem Keep.wr8 {rs : List Reg} {s t : State} (h : Keep rs s t) (hr : FP ∉ rs) {d : Nat} (hd : Wr8 s d) :
    Wr8 t d := by
  obtain ⟨a, b, c⟩ := hd
  refine ⟨a, ?_, ?_⟩
  · rw [h.gpr hr]; exact b
  · rw [h.gpr hr, h.2.2]; exact c

theorem holes_congr (a : BitVec 64) {f g : ℕ → BitVec 64} (h : ∀ j < 4, f j = g j) : holes a f = holes a g := by
  simp only [holes, Holes.zc, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem pmT_congr (x : BitVec 64) {a b c a' b' c' : ℕ → BitVec 64} (ha : ∀ j < 4, a j = a' j)
    (hb : ∀ j < 4, b j = b' j) (hc : ∀ j < 4, c j = c' j) : pmT x a b c = pmT x a' b' c' := by
  simp only [pmT, holes_congr _ ha, holes_congr _ hb, holes_congr _ hc]

/-- The doubleword at `FP + 8 j` after stores to two other slots. -/
theorem fw_st2 {s t : State} {k j : Nat} (hm : t.mem = (s.mem.writeW (s.gpr FP + BitVec.ofNat 64 (slot k)) (s.gpr PL)).writeW
    (s.gpr FP + BitVec.ofNat 64 (slot (k + 1))) (s.gpr (Z 0))) (hf : t.gpr FP = s.gpr FP) (hk : k + 1 < 256)
    (hj : j < 256) (h0 : j ≠ k) (h1 : j ≠ k + 1) : fw t (8 * j) = fw s (8 * j) := by
  simp only [fw, hm, hf, slot]
  rw [fw_writeW (s := s) _ hj hk h1, fw_writeW (s := s) _ hj (by omega) h0]

theorem fw_st2_self {s t : State} {k : Nat} (hm : t.mem = (s.mem.writeW (s.gpr FP + BitVec.ofNat 64 (slot k)) (s.gpr PL)).writeW
    (s.gpr FP + BitVec.ofNat 64 (slot (k + 1))) (s.gpr (Z 0))) (hf : t.gpr FP = s.gpr FP) (hk : k + 1 < 256) :
    fw t (slot k) = s.gpr PL ∧ fw t (slot (k + 1)) = s.gpr (Z 0) := by
  simp only [fw, hm, hf, slot]
  refine ⟨?_, Mem.readW_writeW_self64 _ _ _⟩
  rw [fw_writeW (s := s) _ (by omega) hk (by omega), Mem.readW_writeW_self64]

theorem slot_contains (b : Addr) {k : Nat} (hk : 36 ≤ k) (hk' : k < 40) :
    (⟨b + BitVec.ofNat 64 288, 32⟩ : Region).Contains (b + BitVec.ofNat 64 (8 * k)) (64 / 8) := by
  simp only [Region.Contains]
  rw [Offset.sub_add_eq, Offset.add_sub_cancel_left, Offset.toNat_sub_ofNat]
  simp only [BitVec.toNat_ofNat]
  omega

theorem block_ok (s : State) (hp : BlkPre s) :
    WP isa (.block blockCode) s fun t =>
      t.gpr Y0 ++ t.gpr Y1 = mulT (s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0)
        (s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8) (fw s) ∧
      t.gpr DP = s.gpr DP + 16 ∧ t.gpr N = s.gpr N - 1 ∧ Keep blockRegs s t ∧ t.sp = s.sp ∧
      (∀ k < 36, fw t (8 * k) = fw s (8 * k)) ∧
      Frame [⟨s.gpr FP + BitVec.ofNat 64 288, 32⟩] s.mem t.mem := by
  obtain ⟨hK, hR, hW, hD⟩ := hp
  have mk : ∀ (rs : List Reg), Reg.s0 ∉ rs → Reg.s1 ∉ rs → Reg.s2 ∉ rs → Reg.s3 ∉ rs →
      ∀ i < 4, Impl.Gcm.RISCV64.K i ∉ rs := by
    intro rs a b c d i hi; interval_cases i; exacts [a, b, c, d]
  have mk' : ∀ (rs : List Reg), Reg.s0 ∉ rs → Reg.s1 ∉ rs → Reg.s2 ∉ rs → Reg.s3 ∉ rs → Reg.s9 ∉ rs →
      ∀ {u v : State}, Keep rs u v → v.mem = u.mem → Masks u → (∀ k < 40, Rd8 u (8 * k)) →
        (∀ k, 36 ≤ k → k < 40 → Wr8 u (8 * k)) →
        Masks v ∧ (∀ k < 40, Rd8 v (8 * k)) ∧ (∀ k, 36 ≤ k → k < 40 → Wr8 v (8 * k)) ∧
          (∀ d, fw v d = fw u d) := by
    intro rs a b c d e u v hk hm hKu hRu hWu
    exact ⟨Keep.masks hk hKu (mk rs a b c d), fun k hk' => Keep.rd8 hk e (hRu k hk'),
      fun k h1 h2 => Keep.wr8 hk e (hWu k h1 h2), fw_congr hm (Keep.gpr hk e)⟩
  have hR12 : ∀ {u : State} (o : Nat), (∀ k < 40, Rd8 u (8 * k)) → o + 12 ≤ 40 →
      ∀ k < 12, Rd8 u (slot o + 8 * k) := fun o h ho k hk => by
    rw [show slot o + 8 * k = 8 * (o + k) by simp only [slot]; omega]; exact h _ (by omega)
  rw [blockCode_eq, WP.block_append_iff]
  refine WP.mono (ld2_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s hD)
    fun u1 ⟨x0, x1, k1, m1, p1⟩ => ?_
  obtain ⟨K1, R1, W1, F1⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) k1 m1 hK hR hW
  rw [WP.block_append_iff]
  refine WP.mono (bXor_ok u1) fun u2 ⟨y0, y1, k2, m2, p2⟩ => ?_
  obtain ⟨K2, R2, W2, F2⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) k2 m2 K1 R1 W1
  rw [WP.block_append_iff]
  refine WP.mono (pm_ok u2 (X := Y0) (by decide) (slot 0) K2 (hR12 0 R2 (by decide)))
    fun u3 ⟨l1, l2, k3, m3, p3⟩ => ?_
  obtain ⟨K3, R3, W3, F3⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) k3 m3 K2 R2 W2
  rw [WP.block_append_iff]
  refine WP.mono (st2_ok u3 36 (W3 36 (by decide) (by decide)) (W3 37 (by decide) (by decide)))
    fun u4 ⟨g4, rd4, wr4, p4, m4⟩ => ?_
  have k4 : Keep [] u3 u4 := ⟨fun r _ => by rw [g4], rd4, wr4⟩
  have fp4 : u4.gpr FP = u3.gpr FP := by rw [g4]
  have K4 : Masks u4 := Keep.masks k4 K3 (mk _ (by decide) (by decide) (by decide) (by decide))
  have R4 : ∀ k < 40, Rd8 u4 (8 * k) := fun k hk => Keep.rd8 k4 (by decide) (R3 k hk)
  have W4 : ∀ k, 36 ≤ k → k < 40 → Wr8 u4 (8 * k) := fun k h1 h2 => Keep.wr8 k4 (by decide) (W3 k h1 h2)
  rw [WP.block_append_iff]
  refine WP.mono (pm_ok u4 (X := Y1) (by decide) (slot 12) K4 (hR12 12 R4 (by decide)))
    fun u5 ⟨h1, h2, k5, m5, p5⟩ => ?_
  obtain ⟨K5, R5, W5, F5⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) k5 m5 K4 R4 W4
  rw [WP.block_append_iff]
  refine WP.mono (st2_ok u5 38 (W5 38 (by decide) (by decide)) (W5 39 (by decide) (by decide)))
    fun u6 ⟨g6, rd6, wr6, p6, m6⟩ => ?_
  have k6 : Keep [] u5 u6 := ⟨fun r _ => by rw [g6], rd6, wr6⟩
  have fp6 : u6.gpr FP = u5.gpr FP := by rw [g6]
  have K6 : Masks u6 := Keep.masks k6 K5 (mk _ (by decide) (by decide) (by decide) (by decide))
  have R6 : ∀ k < 40, Rd8 u6 (8 * k) := fun k hk => Keep.rd8 k6 (by decide) (R5 k hk)
  rw [WP.block_append_iff]
  refine WP.mono (bY_ok u6) fun u7 ⟨e7, k7, m7, p7⟩ => ?_
  obtain ⟨K7, R7, -, F7⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) k7 m7 K6 R6
    (fun k h1 h2 => Keep.wr8 k6 (by decide) (W5 k h1 h2))
  rw [WP.block_append_iff]
  refine WP.mono (pm_ok u7 (X := Y0) (by decide) (slot 24) K7 (hR12 24 R7 (by decide)))
    fun u8 ⟨n1, n2, k8, m8, p8⟩ => ?_
  obtain ⟨-, R8, -, F8⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) k8 m8 K7 R7
    (fun k h1 h2 => Keep.wr8 k7 (by decide) (Keep.wr8 k6 (by decide) (W5 k h1 h2)))
  refine WP.mono (bTail_ok u8 (R8 36 (by decide)) (R8 37 (by decide)) (R8 38 (by decide)) (R8 39 (by decide)))
    fun t ⟨e, d, n, kt, mt, pt⟩ => ?_
  -- The frame pointer and the other registers through the steps.
  have fpS : ∀ {u v : State} {rs : List Reg}, Keep rs u v → Reg.s9 ∉ rs → v.gpr FP = u.gpr FP :=
    fun h hr => Keep.gpr h hr
  have f3 : u3.gpr FP = s.gpr FP := by
    rw [fpS k3 (by decide), fpS k2 (by decide), fpS k1 (by decide)]
  have f5 : u5.gpr FP = s.gpr FP := by rw [fpS k5 (by decide), fp4, f3]
  -- The slots after the stores.
  obtain ⟨s36, s37⟩ := fw_st2_self (k := 36) m4 fp4 (by decide)
  obtain ⟨s38, s39⟩ := fw_st2_self (k := 38) m6 fp6 (by decide)
  have st4 : ∀ j < 256, j ≠ 36 → j ≠ 37 → fw u4 (8 * j) = fw u3 (8 * j) :=
    fun j hj a b => fw_st2 (k := 36) m4 fp4 (by decide) hj a b
  have st6 : ∀ j < 256, j ≠ 38 → j ≠ 39 → fw u6 (8 * j) = fw u5 (8 * j) :=
    fun j hj a b => fw_st2 (k := 38) m6 fp6 (by decide) hj a b
  have F86 : ∀ d, fw u8 d = fw u6 d := fun d => by rw [F8, F7]
  have g36 : fw u8 (slot 36) = u3.gpr PL := by
    rw [F86, show slot 36 = 8 * 36 from rfl, st6 36 (by decide) (by decide) (by decide), F5, ← s36]; rfl
  have g37 : fw u8 (slot 37) = u3.gpr (Z 0) := by
    rw [F86, show slot 37 = 8 * 37 from rfl, st6 37 (by decide) (by decide) (by decide), F5, ← s37]; rfl
  have g38 : fw u8 (slot 38) = u5.gpr PL := by rw [F86, s38]
  have g39 : fw u8 (slot 39) = u5.gpr (Z 0) := by rw [F86, s39]
  -- `Y` through the steps.
  have ya : u2.gpr Y0 = s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0 := by
    rw [y0, Keep.gpr k1 (by decide), x0]
  have yb : u2.gpr Y1 = s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8 := by
    rw [y1, Keep.gpr k1 (by decide), x1]
  have y4 : u4.gpr Y1 = u2.gpr Y1 := by rw [g4, Keep.gpr k3 (by decide)]
  have y6a : u6.gpr Y0 = u2.gpr Y0 := by
    rw [g6, Keep.gpr k5 (by decide), g4, Keep.gpr k3 (by decide)]
  have y6b : u6.gpr Y1 = u2.gpr Y1 := by rw [g6, Keep.gpr k5 (by decide), y4]
  -- The tables.
  have T0 : ∀ o j, fw u2 (o + j) = fw s (o + j) := fun o j => by rw [F2, F1]
  have T12 : ∀ j < 12, fw u4 (slot 12 + 8 * j) = fw s (slot 12 + 8 * j) := fun j hj => by
    rw [show slot 12 + 8 * j = 8 * (12 + j) by simp only [slot]; omega, st4 _ (by omega) (by omega) (by omega),
      F3, F2, F1]
  have T24 : ∀ j < 12, fw u7 (slot 24 + 8 * j) = fw s (slot 24 + 8 * j) := fun j hj => by
    rw [show slot 24 + 8 * j = 8 * (24 + j) by simp only [slot]; omega, F7, st6 _ (by omega) (by omega) (by omega),
      F5, st4 _ (by omega) (by omega) (by omega), F3, F2, F1]
  have hl : pmT (u2.gpr Y0) (fun j => fw u2 (slot 0 + 8 * j)) (fun j => fw u2 (slot 0 + 32 + 8 * j))
      (fun j => fw u2 (slot 0 + 64 + 8 * j)) = pmT (s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0)
      (fun j => fw s (slot 0 + 8 * j)) (fun j => fw s (slot 0 + 32 + 8 * j)) (fun j => fw s (slot 0 + 64 + 8 * j)) := by
    rw [ya]; exact pmT_congr _ (fun j _ => T0 _ _) (fun j _ => T0 _ _) (fun j _ => T0 _ _)
  have hh : pmT (u4.gpr Y1) (fun j => fw u4 (slot 12 + 8 * j)) (fun j => fw u4 (slot 12 + 32 + 8 * j))
      (fun j => fw u4 (slot 12 + 64 + 8 * j)) = pmT (s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8)
      (fun j => fw s (slot 12 + 8 * j)) (fun j => fw s (slot 12 + 32 + 8 * j))
      (fun j => fw s (slot 12 + 64 + 8 * j)) := by
    rw [y4, yb]
    refine pmT_congr _ (fun j hj => T12 j (by omega)) (fun j hj => ?_) (fun j hj => ?_)
    · rw [show slot 12 + 32 + 8 * j = slot 12 + 8 * (4 + j) by simp only [slot]; omega]; exact T12 _ (by omega)
    · rw [show slot 12 + 64 + 8 * j = slot 12 + 8 * (8 + j) by simp only [slot]; omega]; exact T12 _ (by omega)
  have hm : pmT (u7.gpr Y0) (fun j => fw u7 (slot 24 + 8 * j)) (fun j => fw u7 (slot 24 + 32 + 8 * j))
      (fun j => fw u7 (slot 24 + 64 + 8 * j)) = pmT ((s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0) ^^^
        (s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8))
      (fun j => fw s (slot 24 + 8 * j)) (fun j => fw s (slot 24 + 32 + 8 * j))
      (fun j => fw s (slot 24 + 64 + 8 * j)) := by
    rw [e7, y6a, y6b, ya, yb]
    refine pmT_congr _ (fun j hj => T24 j (by omega)) (fun j hj => ?_) (fun j hj => ?_)
    · rw [show slot 24 + 32 + 8 * j = slot 24 + 8 * (4 + j) by simp only [slot]; omega]; exact T24 _ (by omega)
    · rw [show slot 24 + 64 + 8 * j = slot 24 + 8 * (8 + j) by simp only [slot]; omega]; exact T24 _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, g36, g37, g38, g39, n1, n2, l1, l2, h1, h2, hl, hh, hm]
    rfl
  · rw [d, Keep.gpr k8 (by decide), Keep.gpr k7 (by decide), g6, Keep.gpr k5 (by decide), g4,
      Keep.gpr k3 (by decide), Keep.gpr k2 (by decide), Keep.gpr k1 (by decide)]
  · rw [n, Keep.gpr k8 (by decide), Keep.gpr k7 (by decide), g6, Keep.gpr k5 (by decide), g4,
      Keep.gpr k3 (by decide), Keep.gpr k2 (by decide), Keep.gpr k1 (by decide)]
  · refine Keep.mono (Keep.trans k1 (Keep.trans k2 (Keep.trans k3 (Keep.trans k4 (Keep.trans k5
      (Keep.trans k6 (Keep.trans k7 (Keep.trans k8 kt)))))))) ?_
    simp only [pmRegs, holesRegs, tailRegs, blockRegs]; decide
  · rw [pt, p8, p7, p6, p5, p4, p3, p2, p1]
  · intro k hk
    rw [fw_congr mt (Keep.gpr kt (by decide)), F86, st6 k (by omega) (by omega) (by omega), F5,
      st4 k (by omega) (by omega) (by omega), F3, F2, F1]
  · rw [mt, m8, m7, m6, m5, m4, m3, m2, m1, f5, f3]
    have c : ∀ k, 36 ≤ k → k < 40 → (⟨s.gpr FP + BitVec.ofNat 64 288, 32⟩ : Region).Contains
        (s.gpr FP + BitVec.ofNat 64 (slot k)) (64 / 8) := fun k a b => slot_contains _ a b
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c 36 (by decide) (by decide))).writeW
      List.mem_cons_self _ (c (36 + 1) (by decide) (by decide))).writeW List.mem_cons_self _ (c 38 (by decide) (by decide))
      |>.writeW List.mem_cons_self _ (c (38 + 1) (by decide) (by decide))

/-! ## The key -/

/-- The arithmetic of `keyCode` after the loads. -/
def keyArith : List Instr :=
  [.shift .sll .d .t3 .t0 1, .shift .srl .d .t4 .t1 63, .logic .xor .t3 .t3 .t4,
   .shift .srl .d .t4 .t0 63, .li .t2 0, .sub .t4 .t2 .t4,
   .li .t5 (-62), .shift .sll .d .t5 .t5 56, .logic .and .t5 .t4 .t5, .logic .xor .t3 .t3 .t5,
   .shift .sll .d .t5 .t1 1, .logicImm .and .t6 .t4 1, .logic .xor .t5 .t5 .t6]

theorem keyCode_eq : keyCode = Impl.Words.RISCV64.loadBE64 .t0 .t2 HP 0 ++
    Impl.Words.RISCV64.loadBE64 .t1 .t2 HP 8 ++ keyArith := by
  simp only [keyCode, keyArith, List.append_assoc]

theorem poly_eq : (BitVec.ofInt 64 (-62)) <<< 56 = VG.Impl.Gcm.Clmul.poly := by decide

theorem keyArith_ok (s : State) :
    WP isa (.block keyArith) s fun t => t.gpr .t3 = Holes.key0 (s.gpr .t0) (s.gpr .t1) ∧
      t.gpr .t5 = Holes.key1 (s.gpr .t0) (s.gpr .t1) ∧ Keep [.t2, .t3, .t4, .t5, .t6] s t ∧ t.mem = s.mem ∧
      t.sp = s.sp := by
  unfold keyArith
  mrun
  simp only [Holes.key0, Holes.key1, ← poly_eq]
  glue_close

theorem maskCode_ok (s : State) :
    WP isa (.block maskCode) s fun t => Masks t ∧ Keep [.s0, .s1, .s2, .s3, .a7] s t ∧ t.mem = s.mem ∧
      t.sp = s.sp := by
  unfold maskCode
  simp only [Impl.Gcm.RISCV64.K, T]
  mrun
  refine ⟨fun i hi => ?_, ?_⟩
  · interval_cases i <;> simp only [Impl.Gcm.RISCV64.K, Holes.K, reduceCtorEq, ite_false, ite_true] <;> decide
  · glue_close

/-- A store to the frame keeps a doubleword at another offset. -/
theorem readW_wr_ne (m : Mem) (b : Addr) (v : BitVec 64) {a c : Nat} (ha : a % 8 = 0) (hc : c % 8 = 0)
    (hac : a ≠ c) (ha' : a < 2048) (hc' : c < 2048) :
    (m.writeW (b + BitVec.ofNat 64 a) v).readW (b + BitVec.ofNat 64 c) 64 = m.readW (b + BitVec.ofNat 64 c) 64 := by
  obtain ⟨i, rfl⟩ : ∃ i, a = 8 * i := ⟨a / 8, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, c = 8 * j := ⟨c / 8, by omega⟩
  exact Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) (by omega)) (by decide)

theorem readW_wr_ne0 (m : Mem) (b : Addr) (v : BitVec 64) {c : Nat} (hc : c % 8 = 0) (hac : 0 ≠ c)
    (hc' : c < 2048) : (m.writeW b v).readW (b + BitVec.ofNat 64 c) 64 = m.readW (b + BitVec.ofNat 64 c) 64 := by
  have := readW_wr_ne m b v (a := 0) (c := c) (by decide) hc hac (by decide) hc'
  simpa using this

theorem readW_wr_ne0' (m : Mem) (b : Addr) (v : BitVec 64) {a : Nat} (ha : a % 8 = 0) (hac : a ≠ 0)
    (ha' : a < 2048) : (m.writeW (b + BitVec.ofNat 64 a) v).readW b 64 = m.readW b 64 := by
  have := readW_wr_ne m b v (a := a) (c := 0) ha (by decide) hac ha' (by decide)
  simpa using this

/-- Operand `i` (of 9) of the prepared key `k₀, k₁`: of the word `k₀`, `k₁`
or `k₀ ⊕ k₁` (`i / 3`), its low half, high half or their sum (`i % 3`). -/
def opK (k0 k1 : BitVec 64) (i : Nat) : BitVec 64 :=
  let w := if i / 3 = 0 then k0 else if i / 3 = 1 then k1 else k0 ^^^ k1
  if i % 3 = 0 then Holes.lo32 w else if i % 3 = 1 then Holes.hi32 w else Holes.lo32 w ^^^ Holes.hi32 w

/-- The words of `prepWord w p`, for the word `W` in `w`. -/
def opW (W : BitVec 64) (q : Nat) : BitVec 64 :=
  if q = 0 then Holes.lo32 W else if q = 1 then Holes.hi32 W else Holes.lo32 W ^^^ Holes.hi32 W

theorem splitStore_eq (v : Reg) (i : Nat) : splitStore v i =
    [.logic .and T v (Impl.Gcm.RISCV64.K 0), .store .d T FP (slot (4 * i + 0)),
     .logic .and T v (Impl.Gcm.RISCV64.K 1), .store .d T FP (slot (4 * i + 1)),
     .logic .and T v (Impl.Gcm.RISCV64.K 2), .store .d T FP (slot (4 * i + 2)),
     .logic .and T v (Impl.Gcm.RISCV64.K 3), .store .d T FP (slot (4 * i + 3))] := rfl

set_option hygiene false in
macro "prep_word_tac" : tactic => `(tactic| (
  have W0 := W 0 (by decide); have W1 := W 1 (by decide); have W2 := W 2 (by decide); have W3 := W 3 (by decide)
  have W4 := W 4 (by decide); have W5 := W 5 (by decide); have W6 := W 6 (by decide); have W7 := W 7 (by decide)
  have W8 := W 8 (by decide); have W9 := W 9 (by decide); have W10 := W 10 (by decide); have W11 := W 11 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    at W0 W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11
  simp only [prepWord, splitStore_eq, slot, List.cons_append, List.nil_append, Impl.Gcm.RISCV64.K, B, HA, T, FP,
    Nat.reduceMul, Nat.reduceAdd]
  mrun [k0, k1, k2, k3, w6, wa6, ws4, wa7, Ne.symm w6, Ne.symm wa6, Ne.symm ws4, Ne.symm wa7,
    W0.1, W1.1, W2.1, W3.1, W4.1, W5.1, W6.1, W7.1, W8.1, W9.1, W10.1, W11.1,
    W0.2, W1.2, W2.2, W3.2, W4.2, W5.2, W6.2, W7.2, W8.2, W9.2, W10.2, W11.2]
  refine ⟨fun q hq j hj => ?_, fun k hk hk' => ?_, ?_, ?_⟩
  · interval_cases q <;> interval_cases j <;>
      simp (disch := omega) only [fw, FP, opW, Holes.lo32, Holes.hi32, reduceCtorEq, ite_false, ite_true,
        Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add, Nat.add_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, readW_wr_ne, readW_wr_ne0, readW_wr_ne0', Mem.readW_writeW_self64, Nat.reduceEqDiff]
  · simp (disch := omega) only [fw, FP, reduceCtorEq, ite_false, ite_true, Nat.mul_zero, Nat.zero_add,
      readW_wr_ne, readW_wr_ne0]
  · glue_close
  · repeat (first
      | exact Frame.refl _ _
      | refine Frame.writeW ?_ List.mem_cons_self _ (cn _ (by decide))
      | refine Frame.writeW ?_ List.mem_cons_self _ cn0)))

set_option linter.unusedSimpArgs false in
theorem prepWord0_ok (s : State) {w : Reg} (hw : w ∉ [.t6, .a6, .s4, .a7])  (hK : Masks s)
    (hW : ∀ k < 12, Wr8 s (8 * (12 * 0 + k))) :
    WP isa (.block (prepWord w 0)) s fun t =>
      (∀ q < 3, ∀ j < 4, fw t (8 * (4 * (3 * 0 + q) + j)) = opW (s.gpr w) q &&& Holes.K j) ∧
      (∀ k < 256, (k < 12 * 0 ∨ 12 * 0 + 12 ≤ k) → fw t (8 * k) = fw s (8 * k)) ∧
      Keep [.t6, .a6, .s4, .a7] s t ∧ t.sp = s.sp ∧ Frame [⟨s.gpr FP, 288⟩] s.mem t.mem := by
  obtain ⟨k0, k1, k2, k3⟩ : s.gpr .s0 = Holes.K 0 ∧ s.gpr .s1 = Holes.K 1 ∧ s.gpr .s2 = Holes.K 2 ∧
    s.gpr .s3 = Holes.K 3 := ⟨hK 0 (by decide), hK 1 (by decide), hK 2 (by decide), hK 3 (by decide)⟩
  have cn : ∀ a, a + 8 ≤ 288 → (⟨s.gpr FP, 288⟩ : Region).Contains (s.gpr FP + BitVec.ofNat 64 a) (64 / 8) :=
    fun a ha => by
      simp only [Region.Contains]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have cn0 : (⟨s.gpr FP, 288⟩ : Region).Contains (s.gpr FP) (64 / 8) := by
    simpa using cn 0 (by decide)
  simp only [FP] at cn cn0
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨w6, wa6, ws4, wa7⟩ := hw
  have W : ∀ k < 12, (8 * (12 * 0 + k) < 2048 ∧ (s.gpr .s9 + BitVec.ofNat 64 (8 * (12 * 0 + k))).toNat % 8 = 0) ∧
      InRegions s.wr (s.gpr .s9 + BitVec.ofNat 64 (8 * (12 * 0 + k))) 8 :=
    fun k hk => ⟨⟨(hW k hk).1, (hW k hk).2.1⟩, (hW k hk).2.2⟩
  prep_word_tac

set_option linter.unusedSimpArgs false in
theorem prepWord1_ok (s : State) {w : Reg} (hw : w ∉ [.t6, .a6, .s4, .a7])  (hK : Masks s)
    (hW : ∀ k < 12, Wr8 s (8 * (12 * 1 + k))) :
    WP isa (.block (prepWord w 1)) s fun t =>
      (∀ q < 3, ∀ j < 4, fw t (8 * (4 * (3 * 1 + q) + j)) = opW (s.gpr w) q &&& Holes.K j) ∧
      (∀ k < 256, (k < 12 * 1 ∨ 12 * 1 + 12 ≤ k) → fw t (8 * k) = fw s (8 * k)) ∧
      Keep [.t6, .a6, .s4, .a7] s t ∧ t.sp = s.sp ∧ Frame [⟨s.gpr FP, 288⟩] s.mem t.mem := by
  obtain ⟨k0, k1, k2, k3⟩ : s.gpr .s0 = Holes.K 0 ∧ s.gpr .s1 = Holes.K 1 ∧ s.gpr .s2 = Holes.K 2 ∧
    s.gpr .s3 = Holes.K 3 := ⟨hK 0 (by decide), hK 1 (by decide), hK 2 (by decide), hK 3 (by decide)⟩
  have cn : ∀ a, a + 8 ≤ 288 → (⟨s.gpr FP, 288⟩ : Region).Contains (s.gpr FP + BitVec.ofNat 64 a) (64 / 8) :=
    fun a ha => by
      simp only [Region.Contains]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have cn0 : (⟨s.gpr FP, 288⟩ : Region).Contains (s.gpr FP) (64 / 8) := by
    simpa using cn 0 (by decide)
  simp only [FP] at cn cn0
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨w6, wa6, ws4, wa7⟩ := hw
  have W : ∀ k < 12, (8 * (12 * 1 + k) < 2048 ∧ (s.gpr .s9 + BitVec.ofNat 64 (8 * (12 * 1 + k))).toNat % 8 = 0) ∧
      InRegions s.wr (s.gpr .s9 + BitVec.ofNat 64 (8 * (12 * 1 + k))) 8 :=
    fun k hk => ⟨⟨(hW k hk).1, (hW k hk).2.1⟩, (hW k hk).2.2⟩
  prep_word_tac

set_option linter.unusedSimpArgs false in
theorem prepWord2_ok (s : State) {w : Reg} (hw : w ∉ [.t6, .a6, .s4, .a7])  (hK : Masks s)
    (hW : ∀ k < 12, Wr8 s (8 * (12 * 2 + k))) :
    WP isa (.block (prepWord w 2)) s fun t =>
      (∀ q < 3, ∀ j < 4, fw t (8 * (4 * (3 * 2 + q) + j)) = opW (s.gpr w) q &&& Holes.K j) ∧
      (∀ k < 256, (k < 12 * 2 ∨ 12 * 2 + 12 ≤ k) → fw t (8 * k) = fw s (8 * k)) ∧
      Keep [.t6, .a6, .s4, .a7] s t ∧ t.sp = s.sp ∧ Frame [⟨s.gpr FP, 288⟩] s.mem t.mem := by
  obtain ⟨k0, k1, k2, k3⟩ : s.gpr .s0 = Holes.K 0 ∧ s.gpr .s1 = Holes.K 1 ∧ s.gpr .s2 = Holes.K 2 ∧
    s.gpr .s3 = Holes.K 3 := ⟨hK 0 (by decide), hK 1 (by decide), hK 2 (by decide), hK 3 (by decide)⟩
  have cn : ∀ a, a + 8 ≤ 288 → (⟨s.gpr FP, 288⟩ : Region).Contains (s.gpr FP + BitVec.ofNat 64 a) (64 / 8) :=
    fun a ha => by
      simp only [Region.Contains]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have cn0 : (⟨s.gpr FP, 288⟩ : Region).Contains (s.gpr FP) (64 / 8) := by
    simpa using cn 0 (by decide)
  simp only [FP] at cn cn0
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨w6, wa6, ws4, wa7⟩ := hw
  have W : ∀ k < 12, (8 * (12 * 2 + k) < 2048 ∧ (s.gpr .s9 + BitVec.ofNat 64 (8 * (12 * 2 + k))).toNat % 8 = 0) ∧
      InRegions s.wr (s.gpr .s9 + BitVec.ofNat 64 (8 * (12 * 2 + k))) 8 :=
    fun k hk => ⟨⟨(hW k hk).1, (hW k hk).2.1⟩, (hW k hk).2.2⟩
  prep_word_tac

theorem prepWord_ok (s : State) {w : Reg} (hw : w ∉ [.t6, .a6, .s4, .a7]) {p : Nat} (hp : p < 3) (hK : Masks s)
    (hW : ∀ k < 12, Wr8 s (8 * (12 * p + k))) :
    WP isa (.block (prepWord w p)) s fun t =>
      (∀ q < 3, ∀ j < 4, fw t (8 * (4 * (3 * p + q) + j)) = opW (s.gpr w) q &&& Holes.K j) ∧
      (∀ k < 256, (k < 12 * p ∨ 12 * p + 12 ≤ k) → fw t (8 * k) = fw s (8 * k)) ∧
      Keep [.t6, .a6, .s4, .a7] s t ∧ t.sp = s.sp ∧ Frame [⟨s.gpr FP, 288⟩] s.mem t.mem := by
  interval_cases p
  · exact prepWord0_ok s hw hK hW
  · exact prepWord1_ok s hw hK hW
  · exact prepWord2_ok s hw hK hW

/-! ## The prepared key -/

/-- The table of the prepared key `k₀, k₁`. -/
def Tab (k0 k1 : BitVec 64) (f : ℕ → BitVec 64) : Prop :=
  ∀ i < 9, ∀ j < 4, f (8 * (4 * i + j)) = opK k0 k1 i &&& Holes.K j

set_option linter.unusedSimpArgs false in
theorem mulT_tab {k0 k1 : BitVec 64} {f : ℕ → BitVec 64} (h : Tab k0 k1 f) (y0 y1 : BitVec 64) :
    mulT y0 y1 f = Holes.mulK y0 y1 k0 k1 := by
  have t : ∀ i < 9, ∀ j < 4, f (slot (4 * i) + 8 * j) = opK k0 k1 i &&& Holes.K j := fun i hi j hj => by
    rw [show slot (4 * i) + 8 * j = 8 * (4 * i + j) by simp only [slot]; omega]; exact h i hi j hj
  have e : ∀ (x : BitVec 64) (p : Nat), p < 3 → ∀ w, w = (if p = 0 then k0 else if p = 1 then k1 else k0 ^^^ k1) →
      pmT x (fun j => f (slot (12 * p) + 8 * j)) (fun j => f (slot (12 * p) + 32 + 8 * j))
        (fun j => f (slot (12 * p) + 64 + 8 * j)) = pm x w := by
    intro x p hp w hw
    rw [← pmT_eq]
    refine pmT_congr _ (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · rw [show slot (12 * p) = slot (4 * (3 * p + 0)) by simp only [slot]; omega, t _ (by omega) _ hj]
      simp only [opK, show (3 * p + 0) / 3 = p by omega, show (3 * p + 0) % 3 = 0 by omega, ↓reduceIte, hw]
      all_goals (try (interval_cases p <;> simp))
    · rw [show slot (12 * p) + 32 = slot (4 * (3 * p + 1)) by simp only [slot]; omega, t _ (by omega) _ hj]
      simp only [opK, show (3 * p + 1) / 3 = p by omega, show (3 * p + 1) % 3 = 1 by omega, ↓reduceIte, hw]
      all_goals (try (interval_cases p <;> simp))
    · rw [show slot (12 * p) + 64 = slot (4 * (3 * p + 2)) by simp only [slot]; omega, t _ (by omega) _ hj]
      simp only [opK, show (3 * p + 2) / 3 = p by omega, show (3 * p + 2) % 3 = 2 by omega, ↓reduceIte, hw]
      all_goals (try (interval_cases p <;> simp))
  have e0 := e y0 0 (by decide) k0 (by simp)
  have e1 := e y1 1 (by decide) k1 (by simp)
  have e2 := e (y0 ^^^ y1) 2 (by decide) (k0 ^^^ k1) (by simp)
  simp only [Nat.mul_zero, Nat.reduceMul] at e0 e1 e2
  simp only [mulT, Holes.mulK, e0, e1, e2]

theorem prep_eq : prep = Impl.Words.RISCV64.loadBE64 .t0 .t2 HP 0 ++ Impl.Words.RISCV64.loadBE64 .t1 .t2 HP 8 ++
    (keyArith ++ (maskCode ++ (prepWord .t3 0 ++ (prepWord .t5 1 ++ (([.logic .xor .t4 .t3 .t5] : List Instr) ++ prepWord .t4 2))))) := by
  simp only [prep, keyCode_eq, List.append_assoc]

theorem x45_ok (s : State) :
    WP isa (.block [.logic .xor .t4 .t3 .t5]) s fun t => t.gpr .t4 = s.gpr .t3 ^^^ s.gpr .t5 ∧
      Keep [.t4] s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  mrun
  glue_close

/-- The registers `prep` writes. -/
def prepRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .a7, .a6, .s4]

theorem prep_ok (s : State) (hH : InRegions (s.rd ++ s.wr) (s.gpr HP) 16) (hW : ∀ k < 36, Wr8 s (8 * k)) :
    WP isa (.block prep) s fun t => Masks t ∧
      Tab (Holes.key0 (ByteLoad.be64 s.mem (s.gpr HP) 0) (ByteLoad.be64 s.mem (s.gpr HP) 8))
        (Holes.key1 (ByteLoad.be64 s.mem (s.gpr HP) 0) (ByteLoad.be64 s.mem (s.gpr HP) 8)) (fw t) ∧
      Keep prepRegs s t ∧ t.sp = s.sp ∧ Frame [⟨s.gpr FP, 288⟩] s.mem t.mem := by
  rw [prep_eq, WP.block_append_iff]
  refine WP.mono (ld2_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s hH)
    fun u1 ⟨h0, h1, k1, m1, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (keyArith_ok u1) fun u2 ⟨e0, e1, k2, m2, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskCode_ok u2) fun u3 ⟨K3, k3, m3, p3⟩ => ?_
  have k13 := Keep.trans k1 (Keep.trans k2 k3)
  have fp3 : u3.gpr FP = s.gpr FP := Keep.gpr k13 (by decide)
  have W3 : ∀ k < 36, Wr8 u3 (8 * k) := fun k hk => Keep.wr8 k13 (by decide) (hW k hk)
  have W12 : ∀ {u : State}, (∀ k < 36, Wr8 u (8 * k)) → ∀ p < 3, ∀ k < 12, Wr8 u (8 * (12 * p + k)) :=
    fun h p hp k hk => h _ (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (prepWord_ok u3 (w := .t3) (by decide) (p := 0) (by decide) K3 (W12 W3 0 (by decide)))
    fun u4 ⟨t4, o4, k4, p4, f4⟩ => ?_
  have K4 := Keep.masks k4 K3 (fun i hi => by interval_cases i <;> decide)
  have W4 : ∀ k < 36, Wr8 u4 (8 * k) := fun k hk => Keep.wr8 k4 (by decide) (W3 k hk)
  rw [WP.block_append_iff]
  refine WP.mono (prepWord_ok u4 (w := .t5) (by decide) (p := 1) (by decide) K4 (W12 W4 1 (by decide)))
    fun u5 ⟨t5, o5, k5, p5, f5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (x45_ok u5) fun u6 ⟨e6, k6, m6, p6⟩ => ?_
  have K6 := Keep.masks (Keep.trans k5 k6) K4 (fun i hi => by interval_cases i <;> decide)
  have W6 : ∀ k < 36, Wr8 u6 (8 * k) := fun k hk => Keep.wr8 (Keep.trans k5 k6) (by decide) (W4 k hk)
  refine WP.mono (prepWord_ok u6 (w := .t4) (by decide) (p := 2) (by decide) K6 (W12 W6 2 (by decide)))
    fun t ⟨t7, o7, k7, p7, f7⟩ => ?_
  have K7 := Keep.masks k7 K6 (fun i hi => by interval_cases i <;> decide)
  -- The key words.
  have w3 : u3.gpr .t3 = Holes.key0 (ByteLoad.be64 s.mem (s.gpr HP) 0) (ByteLoad.be64 s.mem (s.gpr HP) 8) := by
    rw [Keep.gpr k3 (by decide), e0, h0, h1]
  have w5 : u4.gpr .t5 = Holes.key1 (ByteLoad.be64 s.mem (s.gpr HP) 0) (ByteLoad.be64 s.mem (s.gpr HP) 8) := by
    rw [Keep.gpr k4 (by decide), Keep.gpr k3 (by decide), e1, h0, h1]
  have w4 : u6.gpr .t4 = u3.gpr .t3 ^^^ u4.gpr .t5 := by
    rw [e6, Keep.gpr k5 (by decide), Keep.gpr k4 (by decide), Keep.gpr k5 (by decide)]
  have F6 : ∀ d, fw u6 d = fw u5 d := fw_congr m6 (Keep.gpr k6 (by decide))
  refine ⟨K7, fun i hi j hj => ?_, ?_, ?_, ?_⟩
  · have hq : i = 3 * (i / 3) + i % 3 := by omega
    have hp : i / 3 < 3 := by omega
    have hr : i % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : i / 3 = 0 ∨ i / 3 = 1 ∨ i / 3 = 2) with h | h | h
    · rw [o7 _ (by omega) (Or.inl (by omega)), F6, o5 _ (by omega) (Or.inl (by omega)),
        show 4 * i + j = 4 * (3 * 0 + i % 3) + j by omega, t4 _ hr _ hj, w3]
      simp only [opK, opW, h, ↓reduceIte]
    · rw [o7 _ (by omega) (Or.inl (by omega)), F6,
        show 4 * i + j = 4 * (3 * 1 + i % 3) + j by omega, t5 _ hr _ hj, w5]
      simp only [opK, opW, h, ↓reduceIte, show (1 : Nat) ≠ 0 by decide]
    · rw [show 4 * i + j = 4 * (3 * 2 + i % 3) + j by omega, t7 _ hr _ hj, w4, w3, w5]
      simp only [opK, opW, h, ↓reduceIte, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide]
  · refine Keep.mono (Keep.trans k13 (Keep.trans k4 (Keep.trans k5 (Keep.trans k6 k7)))) ?_
    simp only [prepRegs]; decide
  · rw [p7, p6, p5, p4, p3, p2, p1]
  · have fA : u4.gpr FP = s.gpr FP := by rw [Keep.gpr k4 (by decide), fp3]
    have fB : u6.gpr FP = s.gpr FP := by rw [Keep.gpr k6 (by decide), Keep.gpr k5 (by decide), fA]
    rw [fp3] at f4; rw [fA] at f5; rw [fB] at f7
    rw [m3, m2, m1] at f4
    rw [← m6] at f5
    exact f4.trans (f5.trans f7)

end VG.Proof.Gcm.RISCV64

/-! The function's proof, private to this file. -/

section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64 VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul ofBytes)

/-! ## The frame -/

/-- The frame of 2048 bytes at `B`, writable, 16-byte aligned, not wrapping. -/
structure FrameOk (B : Addr) (s : State) : Prop where
  al : B.toNat % 16 = 0
  fit : B.toNat + 2048 ≤ 2 ^ 64
  wr : (⟨B, 2048⟩ : Region) ∈ s.wr

theorem FrameOk.of_wr {B : Addr} {s s' : State} (h : FrameOk B s) (hw : s'.wr = s.wr) : FrameOk B s' :=
  ⟨h.al, h.fit, hw ▸ h.wr⟩

theorem FrameOk.al8 {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2048) :
    (B + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  Wp.al8 h.al hd (by omega)

theorem FrameOk.inW {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d + 8 ≤ 2048) :
    InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.wr, Offset.contains_base _ hd (by omega)⟩

theorem FrameOk.inR {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d + 8 ≤ 2048) :
    InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8 := by
  obtain ⟨r, hr, hc⟩ := h.inW hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The frame's slots, from a frame at `FP`. -/
theorem FrameOk.wr8 {s : State} (h : FrameOk (s.gpr FP) s) {k : Nat} (hk : k < 256) : Wr8 s (8 * k) :=
  ⟨by omega, h.al8 (by omega) (by omega), h.inW (by omega)⟩

theorem FrameOk.rd8 {s : State} (h : FrameOk (s.gpr FP) s) {k : Nat} (hk : k < 256) : Rd8 s (8 * k) :=
  ⟨by omega, h.al8 (by omega) (by omega), h.inR (by omega)⟩

/-! ## The blocks -/

/-- After `i` of the `n₀` blocks at `D`, from `sY`: `Y` is `GHASH_H` from
`Y₀` over them (`H` and the blocks from the memory `m₀`). -/
structure BlkInv (H Y₀ : Block) (D : Addr) (m₀ : Mem) (n₀ : Nat) (sY : State) (i : Nat) (s : State) : Prop where
  y : w2 (s.gpr Y0) (s.gpr Y1) = ghashFrom H Y₀ (blocksAt m₀ D i)
  dp : s.gpr DP = D + BitVec.ofNat 64 (16 * i)
  n : s.gpr N = BitVec.ofNat 64 (n₀ - i)
  keep : Keep blockRegs sY s
  sp : s.sp = sY.sp
  tab : ∀ k < 36, fw s (8 * k) = fw sY (8 * k)
  frame : Frame [⟨sY.gpr FP + BitVec.ofNat 64 288, 32⟩] sY.mem s.mem

/-- What the blocks need of the state they start from. -/
structure LoopPre (H : Block) (D : Addr) (m₀ : Mem) (n₀ : Nat) (sY : State) : Prop where
  frame : FrameOk (sY.gpr FP) sY
  masks : Masks sY
  key : ∃ h0 h1, H = h0 ++ h1 ∧ Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1) (fw sY)
  dat : ∀ i < n₀, InRegions (sY.rd ++ sY.wr) (D + BitVec.ofNat 64 (16 * i)) 16
  bytes : ∀ i < n₀, ∀ j < 16, ∀ m : Mem, Frame [⟨sY.gpr FP + BitVec.ofNat 64 288, 32⟩] sY.mem m →
    m (D + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 j) = m₀ (D + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 j)

theorem blk_step {H Y₀ : Block} {D : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hL : LoopPre H D m₀ n₀ sY)
    (hn₀ : n₀ < 2 ^ 64) {i : Nat} (hi : i < n₀) {s : State} (hs : BlkInv H Y₀ D m₀ n₀ sY i s) :
    WP isa (.block blockCode) s (BlkInv H Y₀ D m₀ n₀ sY (i + 1)) := by
  obtain ⟨hF, hK, ⟨h0, h1, hH, ht⟩, hd, hb⟩ := hL
  have fp : s.gpr FP = sY.gpr FP := Keep.gpr hs.keep (by decide)
  have hF' : FrameOk (s.gpr FP) s := by rw [fp]; exact hF.of_wr hs.keep.2.2
  have pre : BlkPre s := ⟨Keep.masks hs.keep hK (fun j hj => by interval_cases j <;> decide),
    fun k hk => hF'.rd8 (by omega), fun k _ h2 => hF'.wr8 (by omega),
    by rw [hs.dp, hs.keep.2.1, hs.keep.2.2]; exact hd i hi⟩
  refine WP.mono (block_ok s pre) fun t ⟨ey, ed, en, kt, pt, tt, ft⟩ => ?_
  have tabs : Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1) (fw s) := fun i' hi' j hj => by
    rw [hs.tab _ (by omega)]; exact ht i' hi' j hj
  -- The block, from the bytes at `DP`.
  have hx : ByteLoad.be64 s.mem (s.gpr DP) 0 ++ ByteLoad.be64 s.mem (s.gpr DP) 8 =
      blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) := by
    rw [show ByteLoad.be64 s.mem (s.gpr DP) 0 ++ ByteLoad.be64 s.mem (s.gpr DP) 8 = hOf s.mem (s.gpr DP) from rfl,
      ← blockAt_hOf, hs.dp]
    exact Proof.Gcm.blockAt_congr fun j hj => hb i hi j hj _ hs.frame
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ey.trans ?_
    rw [mulT_tab tabs, Holes.mulK_eq, ← hH, ← BitVec.xor_append, hx, Proof.Gcm.ghashFrom_blocksAt_succ]
    exact congrArg (fun v => mul (v ^^^ _) H) hs.y
  · rw [ed, hs.dp, BitVec.add_assoc, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    congr 2
  · rw [en, hs.n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (a := n₀ - i) (by omega)]
    omega
  · exact Keep.mono (Keep.trans hs.keep kt) (by simp only [blockRegs]; decide)
  · rw [pt, hs.sp]
  · intro k hk; rw [tt k hk, hs.tab k hk]
  · rw [fp] at ft; exact hs.frame.trans ft

theorem blocks_loop {H Y₀ : Block} {D : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hL : LoopPre H D m₀ n₀ sY)
    (hn₀ : n₀ < 2 ^ 64) (hpos : 0 < n₀) {s : State} (hs : BlkInv H Y₀ D m₀ n₀ sY 0 s) :
    WP isa (.loop (.block blockCode) (.nonzero N)) s (BlkInv H Y₀ D m₀ n₀ sY n₀) := by
  refine WP.loop (M := isa) (fun k s' => ∃ i, k = n₀ - i ∧ i < n₀ ∧ BlkInv H Y₀ D m₀ n₀ sY i s')
    (fun k s' ⟨i, hk, hi, hb⟩ => WP.mono (blk_step hL hn₀ hi hb) fun s'' hb' => ?_) n₀ s
    ⟨0, rfl, hpos, hs⟩
  have hev := eval_nonzero_ofNat s'' N (k := n₀ - (i + 1)) (by omega) hb'.n
  by_cases hl : i + 1 = n₀
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ hb'⟩
  · exact .inr ⟨by rw [hev]; simp; omega, n₀ - (i + 1), by omega, i + 1, rfl, by omega, hb'⟩

/-! ## The saved registers -/

/-- The registers `saved` lists. -/
def savedRegs : List Reg := saved.map Prod.fst

/-- The memory after the saves: each saved register at its slot. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (B + BitVec.ofNat 64 d) (g r)) m

theorem save_ok (s : State) (hF : FrameOk s.sp s) :
    WP isa (.block (.addSp .t0 0 :: saveRegs ++ ([.addSp FP 0] : List Instr))) s fun t =>
      t.gpr FP = s.sp ∧ Keep [.t0, .s9] s t ∧ t.sp = s.sp ∧ t.mem = saveMem s.mem s.sp s.gpr := by
  have W : ∀ k, 40 ≤ k → k < 50 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions s.wr (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega, hF.al8 (by omega) (by omega)⟩, hF.inW (by omega)⟩
  have W0 := W 40 (by decide) (by decide); have W1 := W 41 (by decide) (by decide)
  have W2 := W 42 (by decide) (by decide); have W3 := W 43 (by decide) (by decide)
  have W4 := W 44 (by decide) (by decide); have W5 := W 45 (by decide) (by decide)
  have W6 := W 46 (by decide) (by decide); have W7 := W 47 (by decide) (by decide)
  have W8 := W 48 (by decide) (by decide); have W9 := W 49 (by decide) (by decide)
  simp only [Nat.reduceMul] at W0 W1 W2 W3 W4 W5 W6 W7 W8 W9
  simp only [saveRegs, saved, slot, List.map, FP, List.cons_append, List.nil_append]
  mrun [W0.1, W1.1, W2.1, W3.1, W4.1, W5.1, W6.1, W7.1, W8.1, W9.1,
    W0.2, W1.2, W2.2, W3.2, W4.2, W5.2, W6.2, W7.2, W8.2, W9.2]
  simp only [saveMem, saved, slot, List.foldl, Nat.reduceMul]
  glue_close

theorem restore_ok (s : State) (hF : FrameOk s.sp s) (v : Reg → BitVec 64)
    (hm : ∀ p ∈ saved, s.mem.readW (s.sp + BitVec.ofNat 64 p.2) 64 = v p.1) :
    WP isa (.block (.addSp .t0 0 :: restoreRegs)) s fun t =>
      (∀ r ∈ savedRegs, t.gpr r = v r) ∧ Keep (.t0 :: savedRegs) s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  have R : ∀ k, 40 ≤ k → k < 50 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega, hF.al8 (by omega) (by omega)⟩, hF.inR (by omega)⟩
  have R0 := R 40 (by decide) (by decide); have R1 := R 41 (by decide) (by decide)
  have R2 := R 42 (by decide) (by decide); have R3 := R 43 (by decide) (by decide)
  have R4 := R 44 (by decide) (by decide); have R5 := R 45 (by decide) (by decide)
  have R6 := R 46 (by decide) (by decide); have R7 := R 47 (by decide) (by decide)
  have R8 := R 48 (by decide) (by decide); have R9 := R 49 (by decide) (by decide)
  simp only [Nat.reduceMul] at R0 R1 R2 R3 R4 R5 R6 R7 R8 R9
  have m0 := hm (.s0, 320) (by decide)
  have m1 := hm (.s1, 328) (by decide)
  have m2 := hm (.s2, 336) (by decide)
  have m3 := hm (.s3, 344) (by decide)
  have m4 := hm (.s4, 352) (by decide)
  have m5 := hm (.s5, 360) (by decide)
  have m6 := hm (.s6, 368) (by decide)
  have m7 := hm (.s7, 376) (by decide)
  have m8 := hm (.s8, 384) (by decide)
  have m9 := hm (.s9, 392) (by decide)
  simp only at m0 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [restoreRegs, saved, slot, List.map, Nat.reduceMul]
  mrun [R0.1, R1.1, R2.1, R3.1, R4.1, R5.1, R6.1, R7.1, R8.1, R9.1,
    R0.2, R1.2, R2.2, R3.2, R4.2, R5.2, R6.2, R7.2, R8.2, R9.2, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [savedRegs, saved, List.map]
    glue_close

/-! ## The function -/

/-- The saves, read back. -/
theorem readW_saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    ∀ p ∈ saved, (saveMem m B g).readW (B + BitVec.ofNat 64 p.2) 64 = g p.1 := by
  intro p hp
  simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceMul] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [saveMem, saved, slot, List.foldl, Nat.reduceMul, readW_wr_ne,
      Mem.readW_writeW_self64]

/-- The saves write inside the frame. -/
theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    Frame [⟨B, 2048⟩] m (saveMem m B g) := by
  have c : ∀ d, d + 8 ≤ 2048 → (⟨B, 2048⟩ : Region).Contains (B + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  simp only [saveMem, saved, slot, List.foldl, Nat.reduceMul]
  repeat (first
    | exact Frame.refl _ _
    | refine Frame.writeW ?_ List.mem_cons_self _ (c _ (by decide)))

/-- Two ranges of the frame at `B` that do not overlap. -/
theorem slot_disj (B : Addr) {d e n : Nat} (hd : d + 8 ≤ 2048) (h : e + n ≤ d) :
    (⟨B + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 e, n⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - B).isLt
  omega

theorem sub_disj {r R R' : Region} (hs : Region.Sub r R) (hd : R.Disjoint R') : r.Disjoint R' :=
  fun x hx => hd x (hs x hx)

/-- The frame zeroed. -/
theorem wipe50_ok (u : State) {B : Addr} (hR : (⟨B, 2048⟩ : Region) ∈ u.wr) (hsp : u.sp = B)
    (hal : B.toNat % 16 = 0) :
    WP isa (.block (Impl.StackScratch.RISCV64.wipe 50)) u fun u' => Frame [⟨B, 2048⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .t5 → r ≠ .t6 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp := by
  obtain ⟨u', he, hf, ho, hs, -, -⟩ := wipe_run ⟨B, 2048⟩ u 50 hR (by rw [hsp]; omega)
    (fun k hk => by rw [hsp]; exact Offset.contains_base _ (by omega) (by omega))
  exact ⟨_, _, Exec.block_iff.mpr he, hf, ho, hs⟩

/-- What the code has set up when the blocks start, from `s` and its frame `a`. -/
structure HeadPost (s a sY : State) : Prop where
  loop : LoopPre (blockAt s.mem (s.gpr .a0)) (s.gpr .a2) s.mem (s.gpr .a3).toNat sY
  inv : BlkInv (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1)) (s.gpr .a2) s.mem
    (s.gpr .a3).toNat sY 0 sY
  yp : sY.gpr YP = s.gpr .a1
  wr : sY.wr = a.wr
  sp : sY.sp = a.sp
  fp : sY.gpr FP = a.sp
  slots : ∀ p ∈ saved, sY.mem.readW (a.sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1
  fy : Frame [⟨a.sp, 2048⟩] s.mem sY.mem

/-- The pre-condition's facts on the frame, for `a := allocd 2048 s`. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 16⟩, ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩]
  wr : s.wr = [⟨s.gpr .a1, 16⟩, ⟨s.gpr .a4, 256⟩]
  sh : (⟨(allocd 2048 s).sp, 2048⟩ : Region).Disjoint ⟨s.gpr .a0, 16⟩
  sy : (⟨(allocd 2048 s).sp, 2048⟩ : Region).Disjoint ⟨s.gpr .a1, 16⟩
  sd : (⟨(allocd 2048 s).sp, 2048⟩ : Region).Disjoint ⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩
  fd : (s.gpr .a2).toNat + 16 * (s.gpr .a3).toNat ≤ 2 ^ 64
  frame : FrameOk (allocd 2048 s).sp (allocd 2048 s)

theorem head_ok (s : State) (hp : Pre s) :
    WP isa (.block (.addSp .t0 0 :: saveRegs ++ ([.addSp FP 0] : List Instr) ++ prep ++ loadY)) (allocd 2048 s)
      (HeadPost s (allocd 2048 s)) := by
  obtain ⟨hrd, hwr, hsh, hsy, hsd, hfd, hF⟩ := hp
  set a := allocd 2048 s with ha
  have ard : a.rd = s.rd := rfl
  have awr : a.wr = ⟨a.sp, 2048⟩ :: s.wr := rfl
  have agpr : a.gpr = s.gpr := rfl
  have amem : a.mem = s.mem := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (save_ok a hF) fun u1 ⟨f1, k1, p1, m1⟩ => ?_
  have hF1 : FrameOk (u1.gpr FP) u1 := by rw [f1]; exact hF.of_wr k1.2.2
  have hH : InRegions (u1.rd ++ u1.wr) (u1.gpr HP) 16 := by
    rw [k1.2.1, k1.2.2, Keep.gpr k1 (by decide)]
    exact ⟨⟨s.gpr .a0, 16⟩, List.mem_append_left _ (by rw [ard, hrd]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  refine WP.mono (prep_ok u1 hH fun k hk => hF1.wr8 (by omega)) fun u2 ⟨K2, T2, k2, p2, F2⟩ => ?_
  have hYr : InRegions (u2.rd ++ u2.wr) (u2.gpr YP) 16 := by
    rw [k2.2.1, k2.2.2, Keep.gpr k2 (by decide), k1.2.1, k1.2.2, Keep.gpr k1 (by decide)]
    exact ⟨⟨s.gpr .a1, 16⟩, List.mem_append_right _ (by rw [awr, hwr]; simp), Region.contains_self _ _⟩
  refine WP.mono (ld2_ok (d₀ := Y0) (d₁ := Y1) (tmp := .t2) (n := YP) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) u2 hYr) fun sY ⟨y0, y1, k3, m3, p3⟩ => ?_
  -- The memory before the blocks: the frame's changes only.
  have FY : Frame [⟨a.sp, 2048⟩] s.mem sY.mem := by
    rw [m3]
    have e1 : Frame [⟨a.sp, 2048⟩] s.mem u1.mem := by rw [m1, ← amem]; exact saveMem_frame _ _ _
    have e2 : Frame [⟨a.sp, 2048⟩] u1.mem u2.mem := by
      refine F2.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [f1]; simpa using Offset.sub_base a.sp (d := 0) (n := 288) (k := 2048) (by decide)
    exact e1.trans e2
  have kY : Keep (prepRegs ++ [.a4, .a5, .t2]) u1 sY := Keep.trans k2 k3
  have fpY : sY.gpr FP = a.sp := by rw [Keep.gpr kY (by decide), f1]
  have hFY : FrameOk (sY.gpr FP) sY := by rw [fpY]; exact hF.of_wr (by rw [kY.2.2, k1.2.2])
  have gY : ∀ r, r ∉ [.t0, .s9] ++ (prepRegs ++ [.a4, .a5, .t2]) → sY.gpr r = s.gpr r := fun r hr => by
    rw [Keep.gpr (Keep.trans k1 kY) hr]; rfl
  -- Bytes outside the frame.
  have out : ∀ {m : Mem}, Frame [⟨a.sp, 2048⟩] s.mem m → ∀ {R : Region}, (⟨a.sp, 2048⟩ : Region).Disjoint R →
      R.len ≤ 2 ^ 64 → ∀ i < R.len, m (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
    fun hm R hd hR i hi => hm _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact hd _ hc (Offset.contains_base _ (by omega) (by omega))
  have e1 : Frame [⟨a.sp, 2048⟩] s.mem u1.mem := by rw [m1, ← amem]; exact saveMem_frame _ _ _
  have hHk : blockAt s.mem (s.gpr .a0) =
      ByteLoad.be64 u1.mem (u1.gpr HP) 0 ++ ByteLoad.be64 u1.mem (u1.gpr HP) 8 := by
    have hk1 : u1.gpr HP = s.gpr .a0 := Keep.gpr k1 (by decide)
    rw [hk1]
    change blockAt s.mem (s.gpr .a0) = hOf u1.mem (s.gpr .a0)
    rw [← blockAt_hOf]
    exact (Proof.Gcm.blockAt_congr fun i hi => out e1 (R := ⟨s.gpr .a0, 16⟩) hsh (by simp) i hi).symm
  have hYk : blockAt s.mem (s.gpr .a1) = w2 (sY.gpr Y0) (sY.gpr Y1) := by
    rw [y0, y1, Keep.gpr k2 (by decide), Keep.gpr k1 (by decide),
      show w2 (ByteLoad.be64 u2.mem (a.gpr YP) 0) (ByteLoad.be64 u2.mem (a.gpr YP) 8) = hOf u2.mem (s.gpr .a1) from rfl,
      ← blockAt_hOf, ← m3]
    exact (Proof.Gcm.blockAt_congr fun i hi => out FY (R := ⟨s.gpr .a1, 16⟩) hsy (by simp) i hi).symm
  have hn₀ := (s.gpr .a3).isLt
  have hL : LoopPre (blockAt s.mem (s.gpr .a0)) (s.gpr .a2) s.mem (s.gpr .a3).toNat sY := by
    refine ⟨hFY, ?_, ⟨_, _, hHk, ?_⟩, ?_, ?_⟩
    · exact Keep.masks k3 K2 (fun i hi => by interval_cases i <;> decide)
    · intro i hi j hj
      rw [fw_congr m3 (Keep.gpr k3 (by decide))]; exact T2 i hi j hj
    · intro i hi
      rw [kY.2.1, kY.2.2, k1.2.1, k1.2.2, ard]
      exact ⟨⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩, List.mem_append_left _ (by rw [hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩
    · intro i hi j hj m hm
      have hm' : Frame [⟨a.sp, 2048⟩] s.mem m := FY.trans (hm.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; rw [fpY]; exact Offset.sub_base _ (by decide)⟩)
      have := out hm' hsd (by simp; omega) (16 * i + j) (by simp; omega)
      rwa [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hB0 : BlkInv (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1)) (s.gpr .a2) s.mem
      (s.gpr .a3).toNat sY 0 sY := by
    refine ⟨?_, ?_, ?_, Keep.refl _ _, rfl, fun _ _ => rfl, Frame.refl _ _⟩
    · rw [Proof.Gcm.ghashFrom_blocksAt_zero, hYk]
    · rw [gY _ (by decide)]; simp; rfl
    · rw [gY _ (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine ⟨hL, hB0, by rw [gY _ (by decide)]; rfl, by rw [kY.2.2, k1.2.2], by rw [p3, p2, p1], fpY,
    fun p hp => ?_, FY⟩
  have hd : 320 ≤ p.2 ∧ p.2 + 8 ≤ 400 := by
    simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have c : (⟨a.sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains (a.sp + BitVec.ofNat 64 p.2) 8 :=
    Region.contains_self _ _
  simp only [Mem.readW]
  rw [m3, Frame.read F2 c (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [f1]; simpa using slot_disj a.sp (e := 0) (n := 288) (by omega) (by omega)) (by decide), m1]
  have := readW_saveMem a.mem a.sp a.gpr p hp
  simp only [Mem.readW] at this
  rw [this, agpr]

theorem tail_ok (s : State) (hp : Pre s) (u : State) {Y : Block} (hy : w2 (u.gpr Y0) (u.gpr Y1) = Y)
    (hyp : u.gpr YP = s.gpr .a1) (hwrU : u.wr = (allocd 2048 s).wr) (hsp : u.sp = (allocd 2048 s).sp)
    (hslot : ∀ p ∈ saved, u.mem.readW ((allocd 2048 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1) :
    WP isa (.block (storeY ++ (.addSp .t0 0 :: restoreRegs) ++ Impl.StackScratch.RISCV64.wipe 50)) u
      fun t => blockAt t.mem (s.gpr .a1) = Y ∧ (∀ r ∈ savedRegs, t.gpr r = s.gpr r) ∧ t.sp = u.sp := by
  obtain ⟨hrd, hwr, hsh, hsy, hsd, hfd, hF⟩ := hp
  set a := allocd 2048 s with ha
  have awr : a.wr = ⟨a.sp, 2048⟩ :: s.wr := rfl
  have hwy : ∀ off, off ≤ 8 → ∀ j < 8, InRegions u.wr (s.gpr .a1 + BitVec.ofNat 64 (off + j)) 1 :=
    fun off ho j hj => ⟨⟨s.gpr .a1, 16⟩, by rw [hwrU, awr, hwr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff, WP.block_append_iff, storeY, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (s := u) (v := Y0) (tmp := .t2) (n := YP) (off := 0) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hyp]; exact hwy 0 (by decide)))
    fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (ByteLoad.storeBE_ok (v := Y1) (tmp := .t2) (n := YP) (off := 8) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; show ∀ j < 8, InRegions u.wr _ 1
        rw [hyp]; exact hwy 8 (by decide)))
    fun s₂ e₂ => ?_
  subst e₂
  simp only [RegUpd.gpr_write_of_ne _ _ (show YP ≠ .t2 by decide), RegUpd.gpr_write_of_ne _ _ (show Y1 ≠ .t2 by decide),
    hyp]
  have Fy : Frame [⟨s.gpr .a1, 16⟩] u.mem
      (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0) (ByteLoad.beBytes 8 (u.gpr Y0)))
        (s.gpr .a1 + BitVec.ofNat 64 8) (ByteLoad.beBytes 8 (u.gpr Y1))) :=
    (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide))).trans
      (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide)))
  have hm : ∀ p ∈ saved, (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0)
      (ByteLoad.beBytes 8 (u.gpr Y0))) (s.gpr .a1 + BitVec.ofNat 64 8)
        (ByteLoad.beBytes 8 (u.gpr Y1))).readW (a.sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    have hd : 320 ≤ p.2 ∧ p.2 + 8 ≤ 400 := by
      simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have c : (⟨a.sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains (a.sp + BitVec.ofNat 64 p.2) 8 :=
      Region.contains_self _ _
    simp only [Mem.readW]
    rw [Frame.read Fy c (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          exact sub_disj (Offset.sub_base _ (by omega)) hsy) (by decide)]
    have := hslot p hp
    simp only [Mem.readW] at this
    exact this
  refine WP.mono (restore_ok _ ?_ s.gpr ?_) fun s₃ ⟨r3, k4, m4, p4⟩ => ?_
  · simp only [RegUpd.sp_write, RegUpd.wr_write]; rw [hsp]; exact hF.of_wr hwrU
  · simp only [RegUpd.sp_write, RegUpd.mem_write]; rw [hsp]; exact hm
  have sp3 : s₃.sp = a.sp := by rw [p4]; simp only [RegUpd.sp_write]; exact hsp
  have hRw : (⟨a.sp, 2048⟩ : Region) ∈ s₃.wr := by
    rw [k4.2.2]; simp only [RegUpd.wr_write]; rw [hwrU, awr]; exact List.mem_cons_self
  refine WP.mono (wipe50_ok s₃ hRw sp3 hF.al) fun t ⟨ft, gt, pt⟩ => ?_
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · have hyb : blockAt t.mem (s.gpr .a1) = blockAt s₃.mem (s.gpr .a1) :=
      Proof.Gcm.blockAt_congr fun i hi => ft _ fun r hr hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact hsy _ hc (Offset.contains_base _ (by omega) (by omega))
    rw [hyb, m4]
    simp only [RegUpd.mem_write]
    rw [blockAt_store, hy]
  · have h56 : r ≠ .t5 ∧ r ≠ .t6 := by
      simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h56.1 h56.2, r3 r hr]
  · rw [pt, p4]; simp only [RegUpd.sp_write]

theorem ghash_ok (s : State) (hp : ghashX.pre s) :
    WP isa ghash s fun s' => ghashX.post s s' ∧ ∀ r ∈ savedRegs, s'.gpr r = s.gpr r := by
  obtain ⟨hrd, hwr, hyd, hsh, hsy, hsd, hfy, hfd, hal, hsp⟩ := hp
  refine WP.ite _ (eval_zero s N) (fun h0 => WP.block_nil ⟨?_, fun _ _ => rfl⟩) (fun h0 => ?_)
  · have hn : (s.gpr .a3).toNat = 0 := by
      have := beq_iff_eq.mp h0; simp [N] at this; simp [this]
    show blockAt s.mem (s.gpr .a1) = _
    rw [hn]; rfl
  have hpos : 0 < (s.gpr .a3).toNat := by
    have := beq_eq_false_iff_ne.mp h0
    refine Nat.pos_of_ne_zero fun h => this ?_
    exact BitVec.eq_of_toNat_eq (by simpa [N] using h)
  have hF : FrameOk (allocd 2048 s).sp (allocd 2048 s) :=
    ⟨by show (s.sp - BitVec.ofNat 64 2048).toNat % 16 = 0; rw [toNat_sub_ofNat' hsp]; omega,
     by show (s.sp - BitVec.ofNat 64 2048).toNat + 2048 ≤ 2 ^ 64; rw [toNat_sub_ofNat' hsp]; have := s.sp.isLt; omega,
     List.mem_cons_self⟩
  have P : Pre s := ⟨hrd, hwr, hsh, hsy, hsd, hfd, hF⟩
  unfold frameBytes
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ hsp ?_
  unfold body
  refine WP.seq (WP.mono (head_ok s P) fun sY hH => ?_)
  refine WP.seq (WP.mono (blocks_loop hH.loop (s.gpr .a3).isLt hpos hH.inv) fun sL hBL => ?_)
  have hfp := hH.fp
  have hslot : ∀ p ∈ saved, sL.mem.readW ((allocd 2048 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    have hd : 320 ≤ p.2 ∧ p.2 + 8 ≤ 400 := by
      simp only [saved, slot, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have c : (⟨(allocd 2048 s).sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains
        ((allocd 2048 s).sp + BitVec.ofNat 64 p.2) 8 := Region.contains_self _ _
    have := hH.slots p hp
    simp only [Mem.readW] at this ⊢
    rw [Frame.read hBL.frame c (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [hfp]; exact slot_disj _ (by omega) (by omega)) (by decide)]
    exact this
  have hyp : sL.gpr YP = s.gpr .a1 := by rw [Keep.gpr hBL.keep (by decide), hH.yp]
  have hwrL : sL.wr = (allocd 2048 s).wr := by rw [hBL.keep.2.2, hH.wr]
  have hspL : sL.sp = (allocd 2048 s).sp := by rw [hBL.sp, hH.sp]
  have T := tail_ok s P sL hBL.y hyp hwrL hspL hslot
  refine WP.mono T fun t h => ?_
  refine ⟨?_, fun r hr => h.2.1 r hr⟩
  have h1 := h.1
  simp only [ghashX, freed]
  exact h1

end VG.Proof.Gcm.RISCV64

end

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64

/-! ## The function -/

/-- The registers the code writes: no preserved register but those it saves and restores, nor `ra`. -/
def written : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a2, .a3, .a4, .a5, .a6, .a7,
  .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9]

theorem law_correct (s : State) (hs : ghashX.pre s) :
    ∃ t s', Exec isa ghash s t s' ∧ abiPreserved s s' ∧ ghashX.post s s' := by
  obtain ⟨tr, t, he, ⟨hpost, hsv⟩, hkeep⟩ := WP.keep written (ghash_ok s hs) (by lit_decide) (by lit_decide)
  refine ⟨tr, t, he, ⟨fun r hr => ?_, Exec.sp he, hkeep.gpr (by decide)⟩, hpost⟩
  by_cases h : r ∈ saved.map Prod.fst
  · exact hsv r h
  · exact hkeep.gpr (by revert hr h; revert r; decide)

instance : GhashLaw := ⟨law_correct⟩

def ghashSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_verified : Verified RISCV64.target ghash (Proof.Gcm.ghashContract RISCV64.abi 2048) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Proof.Gcm.ghashContract, Proof.Gcm.ghashSig, ghashX, RISCV64.abi, RISCV64.argRegs]
      [ghashSat]
      using ghashSat)

end VG.Proof.Gcm.RISCV64
