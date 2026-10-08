import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Core

/-! # Hashing a prepared buffer at the end of encryption -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

theorem accN_congr {X X' P P' : Nat → Block} (y : Block)
    (hx : ∀ i < 8, X i = X' i) (hp : ∀ i < 8, P i = P' i) (n : Nat) (hn : n ≤ 8) :
    accN X P y n = accN X' P' y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [accN_succ, accN_succ, ih (by omega)]
    have hk : (n + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [hashInput, hx _ hk, hp _ hk]

def hashClobbers : List XReg := ghRegs ++ [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11]

theorem hashBuffer_ok {s₀ s : State} {P X : Nat → Block} (hp : SPre s₀) (hlaw : HashLaw s₀ P)
    (hE : Env s₀ P s) (hB : ∀ i < 8, s.mem.readW (hashAddr s₀ i) 128 = X i) :
    WP isa (.block hash8) s fun t => Env s₀ P t ∧
      t.lane .xmm2 0 = Spec.Gcm.ghashFrom (hk s₀) (s.lane .xmm2 0) ((List.range 8).map X) ∧
      YFrame hashClobbers s t := by
  refine WP.mono (hash8_ok s
    (fun k hk => by
      rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
      exact in_rdwr (in_sub hp.p_in (by omega)))
    (fun k hk => by
      rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
      exact in_rdwr (in_sub hp.p_in (by omega)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
        exact in_rdwr (in_sub hp.p_in (off := 784) (by decide)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.r11]; exact hE.poly)) fun t ⟨ht, hf⟩ => ?_
  refine ⟨hE.yframe hf, ?_, hf⟩
  rw [ht, accN_congr (s.lane .xmm2 0) (fun i hi => ?_) (fun i hi => ?_) 8 (by decide), hlaw]
  · simp only [bufferBlock, ea_at, BitVec.ofInt_natCast, hE.r11]
    exact hB i hi
  · simp only [bufferPower, ea_at, BitVec.ofInt_natCast, hE.r11]
    rw [show 16 * (8 + i) = 128 + 16 * i by omega]
    exact hE.powers i hi

end VG.Proof.Gcm.X86_64.StitchAvx8
