module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Mont.X86.Rt.Step

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Callee-saved registers in the prepared scratch prefix -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def SavedAt (m : Mem) (W : Addr) (S : Nat) (g : Reg → BitVec 32) : Prop :=
  m.readW (off W S) 32 = g .ebx ∧ m.readW (off W (S + 4)) 32 = g .esi ∧
    m.readW (off W (S + 8)) 32 = g .ebp ∧ m.readW (off W (S + 12)) 32 = g .edi

def saveMem (m : Mem) (W : Addr) (S : Nat) (g : Reg → BitVec 32) : Mem :=
  (((m.writeW (off W S) (g .ebx)).writeW (off W (S + 4)) (g .esi)).writeW
    (off W (S + 8)) (g .ebp)).writeW (off W (S + 12)) (g .edi)

theorem saveMem_saved (m : Mem) (W : Addr) (S L : Nat) (g : Reg → BitVec 32)
    (nowrap : W.toNat + L ≤ 2 ^ 32) (fit : S + 16 ≤ L) : SavedAt (saveMem m W S g) W S g := by
  have r : ∀ (m : Mem) (o d : Nat) (v : BitVec 32), d + 4 ≤ o ∨ o + 4 ≤ d → o + 4 ≤ L → d + 4 ≤ L →
      (m.writeW (off W o) v).readW (off W d) 32 = m.readW (off W d) 32 := fun m o d v sep ho hd =>
    Mem.readW_writeW_sep (Offset.sep W sep (by omega) (by omega)) (by decide)
  unfold SavedAt saveMem
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r _ _ _ _ (by omega) (by omega) (by omega), r _ _ _ _ (by omega) (by omega) (by omega),
      r _ _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [r _ _ _ _ (by omega) (by omega) (by omega), r _ _ _ _ (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [r _ _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem saveMem_outside (m : Mem) (W : Addr) (S L : Nat) (g : Reg → BitVec 32)
    (nowrap : W.toNat + L ≤ 2 ^ 32) (fit : S + 16 ≤ L) : Outside W S 16 m (saveMem m W S g) := by
  have o : ∀ (m : Mem) (d : Nat) (v : BitVec 32), S ≤ d → d + 4 ≤ S + 16 →
      Outside W S 16 m (m.writeW (off W d) v) := fun m d v low high =>
    ((writeW32_outside m W v (by omega)).mono low (by omega))
  exact (((o _ _ _ (by omega) (by omega)).trans (o _ _ _ (by omega) (by omega))).trans
    (o _ _ _ (by omega) (by omega))).trans (o _ _ _ (by omega) (by omega))

theorem SavedAt.of_outs {m m' : Mem} {W : Addr} {S : Nat} {g : Reg → BitVec 32} {rs : List (Nat × Nat)}
    (h : SavedAt m W S g) (O : Outs W rs m m')
    (apart : ∀ r ∈ rs, S + 16 ≤ r.1 ∨ r.1 + r.2 ≤ S) (fit : S + 16 ≤ 2 ^ 32) : SavedAt m' W S g := by
  have k : ∀ d, S ≤ d → d + 4 ≤ S + 16 → m'.readW (off W d) 32 = m.readW (off W d) 32 := by
    intro d low high
    exact Mem.readW_congr fun i hi => O _ fun r hr => by
      rw [show off W d + BitVec.ofNat 64 i = off W (d + i) by simp only [off, Offset.add_add],
        ofs_off0 W (by omega)]
      have := apart r hr
      have : i < 4 := hi
      omega
  exact ⟨(k _ (by omega) (by omega)).trans h.1, (k _ (by omega) (by omega)).trans h.2.1,
    (k _ (by omega) (by omega)).trans h.2.2.1, (k _ (by omega) (by omega)).trans h.2.2.2⟩

def saveCode : List Instr := [.store (at_ .ecx 0) .ebx, .store (at_ .ecx 4) .esi,
  .store (at_ .ecx 8) .ebp, .store (at_ .ecx 12) .edi]

theorem saveCode_ok {s : State} {W : Addr} {L S : Nat} (hw : Ws s W L)
    (pointer : PtrAt s W .ecx S) (fit : S + 16 ≤ L) :
    WP isa (.block saveCode) s fun t =>
      t.mem = saveMem s.mem W S s.gpr ∧ SavedAt t.mem W S s.gpr ∧
      Outside W S 16 s.mem t.mem ∧ Keeps [] s t := by
  have st : ∀ (t : State) (d : Nat), t.gpr .ecx = s.gpr .ecx → t.wr = s.wr → d + 4 ≤ 16 →
      t.ea (at_ .ecx d) = off W (S + d) ∧ InRegions t.wr (off W (S + d)) 4 := by
    intro t d reg wr hd
    have wt := hw.of_wr wr
    have pt : PtrAt t W .ecx S := by rw [PtrAt, reg]; exact pointer
    exact ⟨ea_ptr wt pt (by omega), ws_write wt (by omega)⟩
  unfold saveCode
  obtain ⟨a1, w1⟩ := st s 0 rfl rfl (by decide)
  refine wp_storeS a1 w1 fun s1 m1 => ?_
  obtain ⟨a2, w2⟩ := st s1 4 (by rw [m1.gpr]) m1.wr (by decide)
  refine wp_storeS a2 w2 fun s2 m2 => ?_
  obtain ⟨a3, w3⟩ := st s2 8 (by rw [m2.gpr, m1.gpr]) (by rw [m2.wr, m1.wr]) (by decide)
  refine wp_storeS a3 w3 fun s3 m3 => ?_
  obtain ⟨a4, w4⟩ := st s3 12 (by rw [m3.gpr, m2.gpr, m1.gpr]) (by rw [m3.wr, m2.wr, m1.wr]) (by decide)
  refine wp_storeS a4 w4 fun t m4 => WP.block_nil ?_
  have mem : t.mem = saveMem s.mem W S s.gpr := by
    rw [m4.mem, m3.mem, m2.mem, m1.mem, m3.gpr, m2.gpr, m1.gpr]
    rfl
  exact ⟨mem, mem ▸ saveMem_saved s.mem W S L s.gpr hw.nowrap fit,
    mem ▸ saveMem_outside s.mem W S L s.gpr hw.nowrap fit,
    (m1.keeps []).trans ((m2.keeps []).trans ((m3.keeps []).trans (m4.keeps [])))⟩

end VG.Proof.Mont.X86.PreparedSquare
