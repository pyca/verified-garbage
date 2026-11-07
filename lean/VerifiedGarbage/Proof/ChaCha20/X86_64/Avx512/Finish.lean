module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Setup
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Finish

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen blocks, from the source into the destination
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (plus)

/-- Word `w` of block `j` of the output: the rounds' result (in `zmm w`) plus
the input state, with the counter increment `j` for word 12. -/
def outT (w j : Nat) : T :=
  if w = 12 then .add (.add (.reg 12 j) (.mem 0 12)) (.mem 1 (32 + j)) else .add (.reg w j) (.mem 0 w)

def finishCheck : Bool :=
  match Sym.init.runT true finish with
  | some σ => (List.range 256).all fun i => σ.mem 3 i == .xor (.mem 2 i) (outT (i % 16) (i / 16))
  | none => false

theorem finishCheck_eq : finishCheck = true := by decide +kernel

theorem finish_run : ∃ σ, Sym.init.runT true finish = some σ ∧
    ∀ i < 256, σ.mem 3 i = .xor (.mem 2 i) (outT (i % 16) (i / 16)) := by
  have e := finishCheck_eq
  unfold finishCheck at e
  split at e
  · rename_i σ h
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e⟩
  · cases e

/-- A byte, from the doubleword holding it. -/
theorem byte_dword (m : Mem) (a : Addr) (k : Nat) :
    m (a + BitVec.ofNat 64 k) = (m.readW (a + BitVec.ofNat 64 (4 * (k / 4))) 32).extractLsb' (8 * (k % 4)) 8 := by
  rw [byte_readW m _ (w := 32) (k := k % 4) (by omega), add_ofNat']
  congr 3; omega

theorem outT_eval {s : State} {vs : Nat → CState} (hz : ZH vs s) (hi : Incs s.mem (s.gpr .rcx)) {w j : Nat}
    (hw : w < 16) (hj : j < 16) :
    (outT w j).eval s = (plus vs (stateAt s.mem (s.gpr .rdi)) j)[w] := by
  have r := hz (zreg w) j hj
  simp only [xidx_zreg w hw] at r
  simp only [plus, Vector.getElem_zipWith, Avx2.ctr_get _ _ _ hw, outT]
  split
  · rename_i e; subst e
    simp only [T.eval, memBase_0, memBase_1, r, stateAt_get _ _ (show 12 < 16 by decide), hi j hj,
      BitVec.add_assoc]
  · simp only [T.eval, memBase_0, r, stateAt_get _ _ hw]

/-- The sixteen blocks, XORed with the 1024 bytes of the source at `rsi`
into the destination at `rsi + r11` (`dstR`). -/
theorem finish_ok {s : State} (hc : CtxT true s) (hi : Incs s.mem (s.gpr .rcx)) {vs : Nat → CState}
    (hz : ZH vs s) :
    WP isa (.block finish) s fun s' =>
      (∀ k < 1024, s'.mem ((dstR 256 s).base + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (stateAt s.mem (s.gpr .rdi)) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregsT true s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hm⟩ := finish_run
  refine WP.mono (srunT_ok hc finish (SRelT.init true s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
    h.rd, h.wr⟩
  have d := h.mem3 rfl (k / 4) (by omega)
  rw [hm _ (by omega)] at d
  simp only [T.eval, memBase_2] at d
  rw [show k / 4 % 16 = k % 64 / 4 by omega, show k / 4 / 16 = k / 64 by omega] at d
  rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
    serialize_getD _ (Nat.mod_lt _ (by decide)), outT_eval hz hi (by omega) (by omega),
    show k % 64 % 4 = k % 4 by omega]

end VG.Proof.ChaCha20.X86_64.Avx512
