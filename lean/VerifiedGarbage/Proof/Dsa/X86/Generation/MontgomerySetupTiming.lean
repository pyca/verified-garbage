module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySetup
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySeedTiming
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySquaresTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The fast setup schedule depends on public widths, including for distinct moduli. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure SetupInput (base : Addr) (sp : BitVec 32) (n bits m : Nat) (s : State) : Prop where
  scr : Scr s base montgomeryBytes
  room : CallRoom (s.gpr .esp) base montgomeryBytes
  stack : s.gpr .esp = sp
  modulus : wordsVal s.mem base (slot n 0) n = m
  gt : 1 < m
  odd : m % 2 = 1
  top : 2 ^ (bits - 1) ≤ m

theorem setup_prefix_ready {base : Addr} {sp : BitVec 32} {n bits m : Nat} {s : State}
    (H : SetupInput base sp n bits m s) (hn : 0 < n) (hn' : n ≤ 48)
    (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n) :
    WP isa (.seq (contextStart n) (montgomerySeed n bits)) s (SquareReady base sp n m) := by
  have fits : contextBytes n ≤ montgomeryBytes := by
    simp only [contextBytes, slot, stride, montgomeryBytes]; omega
  refine WP.seq (WP.mono (contextStart_ok H.scr hn fits H.modulus H.gt H.odd)
    fun u ⟨Cu, _, _, Ku⟩ => ?_)
  refine WP.mono (montgomery_seed Cu hn hn' bitsLow bitsHigh H.top H.odd)
    fun v ⟨Cv, value, _, _, Kv⟩ => ?_
  have K := Ku.trans Kv
  refine ⟨Cv, ?_, (K.1 .esp (by decide)).trans H.stack, ?_⟩
  · rw [K.1 .esp (by decide)]; exact H.room
  · rw [← wordsVal_eq_val32, value]
    exact Nat.mod_lt _ (by have := H.gt; omega)

theorem montgomery_setup_ct {base : Addr} {sp : BitVec 32} {n bits m₁ m₂ : Nat}
    (hn : 0 < n) (hn' : n ≤ 48) (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n) :
    RelCT isa (fun s t => SetupInput base sp n bits m₁ s ∧ SetupInput base sp n bits m₂ t)
      (montgomerySetup n bits) (fun _ _ => True) := by
  have prefixCT := (RelCT.seq (montgomery_start_ct n) (montgomery_seed_ct n bits)).mono
    (fun s t (H : SetupInput base sp n bits m₁ s ∧ SetupInput base sp n bits m₂ t) => by
      apply agree_regs
      intro r hr
      rw [List.mem_singleton.mp hr]
      apply BitVec.eq_of_toNat_eq
      rw [H.1.scr.edi_toNat, H.2.scr.edi_toNat]) (fun _ _ _ => trivial)
  have ready := prefixCT.wp (F₁ := SquareReady base sp n m₁) (F₂ := SquareReady base sp n m₂)
    (fun _ _ H => ⟨setup_prefix_ready H.1 hn hn' bitsLow bitsHigh,
      setup_prefix_ready H.2 hn hn' bitsLow bitsHigh⟩)
  exact RelCT.assoc (RelCT.seq ready ((montgomery_squares_ct 6 hn hn').mono
    (fun _ _ ⟨_, hs, ht⟩ => ⟨hs, ht⟩) (fun _ _ _ => trivial)))

end VG.Proof.Dsa.X86.Generation
