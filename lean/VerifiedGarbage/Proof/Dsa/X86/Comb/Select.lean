module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Mont.X86.CombScan

/-! Instantiate the shared private lookup in the five DSA working layouts. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem scan_layout {n e : Nat} (h : Supported n e) :
    CombScanLay n (context n+16*n) (slot n 7) (slot n 1) (layout n e).size ∧
    8 ≤ slot n 1 ∧ slot n 1+128 ≤ context n+16*n := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    constructor
  all_goals first
    | exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    | decide

theorem private_select_ok {s : State} {base : Addr} {n e : Nat}
    (h : Supported n e) (hs : Scr s base (layout n e).size) (hw : w32 s.mem base 4 < 32) :
    WP isa (VG.Impl.Mont.X86.Comb.wordSelect n (context n+16*n) (slot n 7)) s fun t =>
      Outs base [(slot n 1, 128), (slot n 7, 8*n)] s.mem t.mem ∧
      wordsVal t.mem base (slot n 7) n =
        wordsVal s.mem base (entry n (context n+16*n) (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ebx, .ecx, .ebp] s t := by
  obtain ⟨L, header, sep⟩ := scan_layout h
  exact wordSelectBody_ok hs L header hw (.inl sep)

end VG.Proof.Dsa.X86.Comb
