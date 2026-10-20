module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialTable
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The initialized trial table contains the exact divisors and reciprocals -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen

theorem trialTableEntry_ok {s : State} {base : Addr} (hs : Scr s base 8192) {i : Nat} (hi : i < 1024) :
    WP isa (.block (trialTableEntry i)) s fun t =>
      t.mem = (s.mem.writeW (off base (8 * i)) (BitVec.ofNat 32 (tabEntry i))).writeW
        (off base (8 * i + 4)) (BitVec.ofNat 32 (2 ^ 32 / tabEntry i)) ∧ Keeps [.eax] s t := by
  unfold trialTableEntry
  refine wp_movS rfl fun a sa _ => ?_
  have ha := hs.of_keeps sa.keeps (by decide)
  refine wp_storeS (ha.ea (by omega)) (ha.write (by omega)) fun b ab => wp_movS rfl fun c bc _ => ?_
  have kc : Keeps [.eax] s c := (sa.keeps.trans (ab.keeps _)).trans bc.keeps
  have hc := hs.of_keeps kc (by decide)
  refine wp_storeS (hc.ea (by omega)) (hc.write (by omega)) fun t ct => WP.block_nil ⟨?_, kc.trans (ct.keeps _)⟩
  rw [ct.mem, bc.gpr, bc.mem, ab.mem, sa.gpr, sa.mem]

structure TrialTableReady (m : Mem) (base : Addr) (n : Nat) : Prop where
  prime : ∀ i < n, m.readW (off base (8 * i)) 32 = BitVec.ofNat 32 (tabEntry i)
  reciprocal : ∀ i < n, m.readW (off base (8 * i + 4)) 32 = BitVec.ofNat 32 (2 ^ 32 / tabEntry i)

theorem trialTable_ok {s : State} {base : Addr} (hs : Scr s base 8192) (n : Nat) (hn : n ≤ 1024) :
    WP isa (trialTable n) s fun t => TrialTableReady t.mem base n ∧
      Frame [⟨base, 8192⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨⟨by intro i hi; omega, by intro i hi; omega⟩, Frame.refl _ _, Keeps.refl _ _⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun a ⟨table, frame, ka⟩ => ?_)
    refine WP.mono (trialTableEntry_ok (hs.of_keeps ka (by decide)) (by omega : n < 1024)) fun t ⟨mem, kt⟩ => ?_
    have readApart {m : Mem} {o d : Nat} {v : BitVec 32} (ho : o + 4 ≤ 8192) (hd : d + 4 ≤ 8192)
        (sep : d + 4 ≤ o ∨ o + 4 ≤ d) :
        (m.writeW (off base o) v).readW (off base d) 32 = m.readW (off base d) 32 :=
      Mem.readW_writeW_sep (Offset.sep base sep (by have := hs.nowrap; omega) (by have := hs.nowrap; omega)) (by decide)
    refine ⟨⟨?_, ?_⟩, ?_, ka.trans kt⟩
    · intro i hi
      rw [mem, readApart (by omega) (by omega) (Or.inl (by omega))]
      by_cases eq : i = n
      · subst i; exact Mem.readW_writeW_self32 _ _ _
      · rw [readApart (by omega) (by omega) (Or.inl (by omega))]
        exact table.prime i (by omega)
    · intro i hi
      rw [mem]
      by_cases eq : i = n
      · subst i; exact Mem.readW_writeW_self32 _ _ _
      · rw [readApart (by omega) (by omega) (Or.inl (by omega)), readApart (by omega) (by omega) (Or.inl (by omega))]
        exact table.reciprocal i (by omega)
    · rw [mem]
      exact (frame.write (by simp) _ (Scr.contains hs.nowrap (by omega))).write
        (by simp) _ (Scr.contains hs.nowrap (by omega))
end VG.Proof.Dsa.X86.Generation
