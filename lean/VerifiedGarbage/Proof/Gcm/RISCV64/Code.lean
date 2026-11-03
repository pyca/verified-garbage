module

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

/-!
# GHASH on RISC-V: the straight-line code

Untrusted: everything here is checked by Lean. What the blocks of
`Impl/Gcm/RISCV64.lean` compute, as the functions of `Holes.lean`: a 32-bit
product (`holes_ok`), a 64-bit one (`pm_ok`) and a block (`block_ok`).
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
    intro rs a b c d i hi; interval_cases i <;> assumption
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
    (pmCode Y1 (slot 12) ++ (st2 38 ++ ([.logic .xor Y0 Y0 Y1] ++ (pmCode Y0 (slot 24) ++ bTail))))))) := by
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
    intro rs a b c d i hi; interval_cases i <;> assumption
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
    (keyArith ++ (maskCode ++ (prepWord .t3 0 ++ (prepWord .t5 1 ++ ([.logic .xor .t4 .t3 .t5] ++ prepWord .t4 2))))) := by
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
