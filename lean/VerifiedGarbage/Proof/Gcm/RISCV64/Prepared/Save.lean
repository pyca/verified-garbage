module

public import VerifiedGarbage.Impl.Gcm.RISCV64.Prepared
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Gcm.Spec

/-! # Preserve the GHASH caller in a 112-byte frame -/

@[expose] public section
namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64 VG.WriteBytes
structure CompactFrame (B : Addr) (s : State) : Prop where
  al : B.toNat % 16 = 0
  fit : B.toNat + 112 ≤ 2 ^ 64
  wr : (⟨B,112⟩ : Region) ∈ s.wr
theorem CompactFrame.of_wr {B : Addr} {s t : State} (h : CompactFrame B s) (z : t.wr = s.wr) : CompactFrame B t :=
  ⟨h.al,h.fit,z ▸ h.wr⟩
theorem CompactFrame.al8 {B : Addr} {s : State} (h : CompactFrame B s) {d : Nat} (hd : d % 8 = 0) (hd' : d < 112) :
    (B + BitVec.ofNat 64 d).toNat % 8 = 0 := Wp.al8 h.al hd (by omega_using [hd'])
theorem CompactFrame.inW {B : Addr} {s : State} (h : CompactFrame B s) {d : Nat} (hd : d + 8 ≤ 112) :
    InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
theorem CompactFrame.inR {B : Addr} {s : State} (h : CompactFrame B s) {d : Nat} (hd : d + 8 ≤ 112) :
    InRegions (s.rd++s.wr) (B + BitVec.ofNat 64 d) 8 := by
  obtain ⟨r,hr,hc⟩ := h.inW hd
  exact ⟨r,List.mem_append_right _ hr,hc⟩
def compactSaveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) : Mem :=
  compactSaved.foldl (fun m (r, d) => m.writeW (B + BitVec.ofNat 64 d) (g r)) m

theorem compact_save_ok (s : State) (hF : CompactFrame s.sp s) :
    WP isa (.block (.addSp .t0 0 :: compactSave ++ ([.addi FP HP 0, .addSp HP 0] : List Instr))) s fun t =>
      t.gpr FP = s.gpr HP ∧ t.gpr HP = s.sp ∧ Keep [.t0, .s9, .a0] s t ∧ t.sp = s.sp ∧ t.mem = compactSaveMem s.mem s.sp s.gpr := by
  obtain W : ∀ k, 4 ≤ k → k < 14 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions s.wr (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega_using [h2], hF.al8 (by omega_using []) (by omega_using [h2])⟩, hF.inW (by omega_using [h2])⟩
  obtain W0 := W 4 (by decide) (by decide); have W1 := W 5 (by decide) (by decide)
  obtain W2 := W 6 (by decide) (by decide); have W3 := W 7 (by decide) (by decide)
  obtain W4 := W 8 (by decide) (by decide); have W5 := W 9 (by decide) (by decide)
  obtain W6 := W 10 (by decide) (by decide); have W7 := W 11 (by decide) (by decide)
  obtain W8 := W 12 (by decide) (by decide); have W9 := W 13 (by decide) (by decide)
  simp only [Nat.reduceMul] at W0 W1 W2 W3 W4 W5 W6 W7 W8 W9
  simp only [compactSave, compactSaved, saved, slot, List.map, FP, HP, Nat.reduceMul, Nat.reduceSub, List.cons_append, List.nil_append, Nat.reduceMul, Nat.reduceSub]
  mrun [W0.1, W1.1, W2.1, W3.1, W4.1, W5.1, W6.1, W7.1, W8.1, W9.1,
    W0.2, W1.2, W2.2, W3.2, W4.2, W5.2, W6.2, W7.2, W8.2, W9.2]
  simp only [compactSaveMem, compactSaved, saved, slot, List.map, List.foldl, Nat.reduceMul, Nat.reduceSub]
  glue_close

theorem compact_restore_ok (s : State) (hF : CompactFrame s.sp s) (v : Reg → BitVec 64)
    (hm : ∀ p ∈ compactSaved, s.mem.readW (s.sp + BitVec.ofNat 64 p.2) 64 = v p.1) :
    WP isa (.block (.addSp .t0 0 :: compactRestore)) s fun t =>
      (∀ r ∈ savedRegs, t.gpr r = v r) ∧ Keep (.t0 :: savedRegs) s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  obtain R : ∀ k, 4 ≤ k → k < 14 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega_using [h2], hF.al8 (by omega_using []) (by omega_using [h2])⟩, hF.inR (by omega_using [h2])⟩
  obtain R0 := R 4 (by decide) (by decide); have R1 := R 5 (by decide) (by decide)
  obtain R2 := R 6 (by decide) (by decide); have R3 := R 7 (by decide) (by decide)
  obtain R4 := R 8 (by decide) (by decide); have R5 := R 9 (by decide) (by decide)
  obtain R6 := R 10 (by decide) (by decide); have R7 := R 11 (by decide) (by decide)
  obtain R8 := R 12 (by decide) (by decide); have R9 := R 13 (by decide) (by decide)
  simp only [Nat.reduceMul] at R0 R1 R2 R3 R4 R5 R6 R7 R8 R9
  obtain m0 := hm (.s0, 32) (by decide)
  obtain m1 := hm (.s1, 40) (by decide)
  obtain m2 := hm (.s2, 48) (by decide)
  obtain m3 := hm (.s3, 56) (by decide)
  obtain m4 := hm (.s4, 64) (by decide)
  obtain m5 := hm (.s5, 72) (by decide)
  obtain m6 := hm (.s6, 80) (by decide)
  obtain m7 := hm (.s7, 88) (by decide)
  obtain m8 := hm (.s8, 96) (by decide)
  obtain m9 := hm (.s9, 104) (by decide)
  simp only at m0 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [compactRestore, compactSaved, saved, slot, List.map, Nat.reduceMul, Nat.reduceSub]
  mrun [R0.1, R1.1, R2.1, R3.1, R4.1, R5.1, R6.1, R7.1, R8.1, R9.1,
    R0.2, R1.2, R2.2, R3.2, R4.2, R5.2, R6.2, R7.2, R8.2, R9.2, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [savedRegs, saved, List.map]
    glue_close

/-! ## The function -/

/-- The saves, read back. -/
theorem readW_compactSaveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    ∀ p ∈ compactSaved, (compactSaveMem m B g).readW (B + BitVec.ofNat 64 p.2) 64 = g p.1 := by
  intro p hp
  simp only [compactSaved, saved, slot, List.map, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceMul, Nat.reduceSub] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega_using []) only [compactSaveMem, compactSaved, saved, slot, List.map, List.foldl, Nat.reduceMul, Nat.reduceSub, readW_wr_ne,
      Mem.readW_writeW_self64]

/-- The saves write inside the frame. -/
theorem compactSaveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    Frame [⟨B, 112⟩] m (compactSaveMem m B g) := by
  obtain c : ∀ d, d + 8 ≤ 112 → (⟨B, 112⟩ : Region).Contains (B + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega_using [hd])
  simp only [compactSaveMem, compactSaved, saved, slot, List.map, List.foldl, Nat.reduceMul, Nat.reduceSub]
  repeat (first
    | exact Frame.refl _ _
    | refine Frame.writeW ?_ List.mem_cons_self _ (c _ (by decide)))


end VG.Proof.Gcm.RISCV64
