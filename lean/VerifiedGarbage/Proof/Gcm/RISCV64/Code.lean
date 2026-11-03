module

public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Proof.Gcm.RISCV64.Holes
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

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

end VG.Proof.Gcm.RISCV64
