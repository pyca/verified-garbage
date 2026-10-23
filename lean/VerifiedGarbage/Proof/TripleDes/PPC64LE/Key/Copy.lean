module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Load
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.PPC64LE.Isa

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .r8)
    (hsrc : src ≠ .r0) (hdst : dst ≠ .r0)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a < 32768 ∧ a % 4 = 0 := by decide)
    (hb : b < 32768 ∧ b % 4 = 0 := by decide) :
    ∃ s', runBlock isa [.load .d .r8 src a, .store .d .r8 dst b] s = some s' ∧
      Kept [.r8] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  let s₁ := s.write .r8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)
  have hd : s₁.gpr dst = s.gpr dst := gpr_write_of_ne _ _ hne
  have hw : InRegions s₁.wr (s₁.gpr dst + BitVec.ofNat 64 b) 8 := by
    rw [hd]; exact writable
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr dst + BitVec.ofNat 64 b) (s₁.gpr .r8) }, by
    rw [runBlock_cons, exec_load_d hsrc ha readable, runStep_some,
      runBlock_cons, exec_store_d hdst hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .r8 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ hn
  · change s.mem.writeW (s₁.gpr dst + BitVec.ofNat 64 b) (s₁.gpr .r8) = _
    rw [hd, gpr_write_self]
  · rfl
  · rfl

def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.load .d .r8 .r5 (8 * j), .store .d .r8 .r5 (256 + 8 * j)]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r8 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (copyCode n)) s (CopyPost (s.gpr .r5) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have hbase : s₁.gpr .r5 = s.gpr .r5 := h₁.reg .r5 (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r5 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega)
    have writable : InRegions s₁.wr (s₁.gpr .r5 + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := copy64_ok s₁ .r5 .r5
      (8 * n) (256 + 8 * n) (by decide) (by decide) (by decide) readable writable (by omega)
      (by omega)
    have source : s₁.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .r5 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .r5) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .r5 + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .r5) (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.keys i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .r5 + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.PPC64LE.Key
