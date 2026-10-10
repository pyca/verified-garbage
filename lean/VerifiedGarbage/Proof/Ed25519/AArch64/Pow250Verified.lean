import VerifiedGarbage.Proof.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Spec.X25519.Field64

/-!
# `vg_gf25519_r64_pow250` on AArch64, verified

The function meets `pow250Contract` of `Spec/X25519/Field64.lean`, with no
stack: the proof against `powF`, the contract's facts by register, from
`powFn_ok`. The chain's results are `a^(2^250 - 1)` in slot 15 (byte 544) and
`a^11` in slot 14 (byte 512) (`power250Env_eval`, `chainF_eq`), as residues of
the words' values (`val_of_env`, `valAt_fe`); the function writes only bytes
512 to 639 of `ws`. The callee-saved registers it writes are restored from
their lanes, and no instruction writes `v8`–`v15`. Constant time by taint
tracking: only the pointer, in `x0`, is public, and every address is `ws` plus
a constant.
-/

namespace VG.Proof.Ed25519.AArch64.Pow250

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Spec.X25519 (P)
open VG.Spec.X25519.Field64 (valAt zAt p250At p11At PowKeeps)

def powF : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 4096⟩] ∧ (s.gpr .x0).toNat + 4096 ≤ 2 ^ 64
  post s s' :=
    valAt s'.mem (s.gpr .x0) p250At % P = valAt s.mem (s.gpr .x0) zAt ^ (2 ^ 250 - 1) % P ∧
      valAt s'.mem (s.gpr .x0) p11At % P = valAt s.mem (s.gpr .x0) zAt ^ 11 % P ∧
      PowKeeps (s.gpr .x0) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- The spec's element at `o` is the slot's four words. -/
theorem valAt_fe (m : Mem) (base : Addr) (o : BitVec 32) : valAt m base o = fe m base o.toNat := by
  show (m.read (off base o.toNat) (8 * 4)).toNat = _
  rw [Mont.read_eq_wordsVal]
  simp only [fe, Word64.val4, word, off, Mont.wordsVal, Mont.word, Mont.off, Nat.mul_zero, Nat.add_zero]
  rw [show o.toNat + 8 + 8 = o.toNat + 16 by omega, show o.toNat + 16 + 8 = o.toNat + 24 by omega]
  simp only [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
  omega

theorem power250Env_eval (e : Env) :
    power250Env e 15 = (VG.Proof.X25519.chainF (e 2)).1 ∧
      power250Env e 14 = (VG.Proof.X25519.chainF (e 2)).2 := by
  simp only [power250Env, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

/-- A slot holding a power of another, as residues of the words' values. -/
theorem val_of_env {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : env m' b i = VG.Proof.X25519.pw (env m b j) e) :
    fe m' b (offset i) % P = fe m b (offset j) ^ e % P := by
  have := congrArg Fin.val h
  simp only [env, F, VG.Proof.X25519.toFe_val, VG.Proof.X25519.pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

theorem pow_arm (s : State) (hs : powF.pre s) :
    ∃ t s', Exec isa powFn s t s' ∧ abiPreserved s s' ∧ powF.post s s' := by
  obtain ⟨_, hwr, hn⟩ := hs
  obtain ⟨t, u, he, ⟨hg, _, _, hsp, hmem, hev⟩, hv⟩ := WP.preservedV
    (powFn_ok (s := s) (base := s.gpr .x0) ⟨rfl, by rw [hwr]; exact List.mem_singleton_self _, hn⟩)
    powFn_keepsV
  obtain ⟨h15, h14⟩ := power250Env_eval (env s.mem (s.gpr .x0))
  rw [VG.Proof.X25519.chainF_eq] at h15 h14
  rw [← hev] at h15 h14
  have v15 := val_of_env h15
  have v14 := val_of_env h14
  refine ⟨t, u, he, ⟨fun r hr => hg r (powFn_preserved r hr), hsp, hv⟩, ?_, ?_, ?_⟩
  · rw [valAt_fe, valAt_fe]
    generalize (2 ^ 250 - 1 : Nat) = n at v15 ⊢
    exact v15
  · rw [valAt_fe, valAt_fe]
    exact v14
  · intro i hi hown
    simp only [Spec.X25519.Field64.wsBytes, Spec.X25519.Field64.invOwnAt,
      Spec.X25519.Field64.invOwnEnd] at hi hown
    exact hmem _ (by rw [ofs_off' _ (by omega)]; omega)

theorem pow_ct : ConstantTime isa powF.pre powF.pub powFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => ⟨hp.2, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.1⟩) (by taint_decide)

/-- A state satisfying the precondition: `ws` at `0x1000`, and the stack at `0x10000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 4096⟩]

theorem powFn_verified :
    Verified AArch64.target powFn (Spec.X25519.Field64.pow250Contract AArch64.abi) :=
  Verified.of_correct pow_arm pow_ct (by
    sig_implies [Spec.X25519.Field64.pow250Contract, Spec.X25519.Field64.invSig, AArch64.abi,
      AArch64.argRegs, powF] [satState] using satState)

end VG.Proof.Ed25519.AArch64.Pow250
