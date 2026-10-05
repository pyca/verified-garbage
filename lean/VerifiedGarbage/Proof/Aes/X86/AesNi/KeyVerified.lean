import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (EPre keyP keyLen ekSchP ekSchR ekRetR)

/-- The stored doublewords are the shared specification's byte schedule. -/
theorem KeyDone.post {s₀ entry s : State} {nk : Nat} (hd : KeyDone s₀ entry nk s)
    (hn : 0 < nk) (hl : keyLen s₀ = 4 * nk) :
    Proof.Aes.expandKeyX86.post s₀ s := by
  change Spec.Aes.bytesAt s.mem ((ekSchP s₀).setWidth 64)
      (16 * (Spec.Aes.rounds (keyLen s₀ / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem ((keyP s₀).setWidth 64) (keyLen s₀))
  rw [hl, show 4 * nk / 4 = nk by omega, expandKey_eq _ _ hn]
  have hlen : 16 * (Spec.Aes.rounds nk + 1) = 4 * (4 * (nk + 7)) := by
    simp only [Spec.Aes.rounds]; omega
  rw [hlen, bytesAt_eq _ _ _ _ hd.words]
  rfl

/-- Caller-saved-only key expansion preserves the cdecl registers and return slot. -/
theorem KeyDone.abi {s₀ entry s : State} {nk : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (hd : KeyDone s₀ entry nk s) : abiPreserved s₀ s := by
  refine ⟨?_, ?_⟩
  · intro r hr
    rw [hd.gpr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hs.callee _ (by decide) (by decide) (by decide)
  · exact hd.frame.readW (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r; exact hp.rS) (by decide)

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd

theorem KeyReady.arithFlags {s₀ s : State} (hs : KeyReady s₀ s)
    (v : BitVec 32) (c o : Bool) : KeyReady s₀ (VG.X86.arithFlags s v c o) :=
  ⟨⟨hs.esp, hs.mem, hs.rd, hs.wr⟩, hs.eax, hs.ecx, hs.edx, hs.callee⟩

theorem keyCmp32_ok {s₀ s : State} (hs : KeyReady s₀ s) :
    WP isa (.block [.alu .cmp .ecx (.imm 32)]) s fun s' =>
      KeyReady s₀ s' ∧ s'.zf = some (decide (VG.X86.arg s₀ 1 = 32#32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨hs.arithFlags _ _ _, ?_⟩
  rw [zf_arithFlags, hs.ecx]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  rw [show (0 : BitVec 32) + 32 = 32#32 by decide]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyDispatch`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (EPre keyLen)

/-- The independently checked bodies used by the public-length dispatcher. -/
structure KeyBodies : Prop where
  expand128 : ∀ s₀ entry, EPre s₀ → KeyReady s₀ entry → keyLen s₀ = 16 →
    WP isa (.block Impl.Aes.X86.AesNi.expand128) entry (KeyDone s₀ entry 4)
  expand192 : ∀ s₀ entry, EPre s₀ → KeyReady s₀ entry → keyLen s₀ = 24 →
    WP isa (.block Impl.Aes.X86.AesNi.expand192) entry (KeyDone s₀ entry 6)
  expand256 : ∀ s₀ entry, EPre s₀ → KeyReady s₀ entry → keyLen s₀ = 32 →
    WP isa (.block Impl.Aes.X86.AesNi.expand256) entry (KeyDone s₀ entry 8)

/-- Complete expansion, with public dispatch on the key length. -/
theorem key_dispatch_correct (bodies : VG.Proof.Aes.X86.AesNi.KeyBodies) {s₀ : State} (hp : EPre s₀) :
    WP isa Impl.Aes.X86.AesNi.expandKey s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Aes.expandKeyX86.post s₀ s' := by
  refine WP.seq (WP.mono (keyHead_ok s₀ hp) fun entry hs => ?_)
  refine WP.ite (decide (VG.X86.arg s₀ 1 = 24#32)) (by simp [VG.X86.eval, hs.zf]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    have hl : keyLen s₀ = 24 := congrArg BitVec.toNat h
    refine WP.mono (bodies.expand192 s₀ entry hp hs.toKeyReady hl) fun s hd => ?_
    exact ⟨hd.abi hp hs.toKeyReady, hd.post (by decide) hl⟩
  · simp only [decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.keyCmp32_ok hs.toKeyReady) fun mid ⟨hm, hz⟩ => ?_)
    refine WP.ite (decide (VG.X86.arg s₀ 1 = 32#32)) (by simp [VG.X86.eval, hz]) (fun h32 => ?_) (fun h32 => ?_)
    · simp only [decide_eq_true_eq] at h32
      have hl : keyLen s₀ = 32 := congrArg BitVec.toNat h32
      refine WP.mono (bodies.expand256 s₀ mid hp hm hl) fun s hd => ?_
      exact ⟨hd.abi hp hm, hd.post (by decide) hl⟩
    · simp only [decide_eq_false_iff_not] at h32
      have h24 : keyLen s₀ ≠ 24 := fun e => h (BitVec.eq_of_toNat_eq e)
      have hN32 : keyLen s₀ ≠ 32 := fun e => h32 (BitVec.eq_of_toNat_eq e)
      have hl : keyLen s₀ = 16 := by have := hp.len; omega
      refine WP.mono (bodies.expand128 s₀ mid hp hm hl) fun s hd => ?_
      exact ⟨hd.abi hp hm, hd.post (by decide) hl⟩

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (EPre keyLen ekSat)


theorem expandKey_correct (bodies : VG.Proof.Aes.X86.AesNi.KeyBodies) (s : State) (hs : Proof.Aes.expandKeyX86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyX86.post s s' :=
  (VG.Proof.Aes.X86.AesNi.key_dispatch_correct bodies (EPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem expandKey_verified (bodies : KeyBodies) :
    Verified X86.target Impl.Aes.X86.AesNi.expandKey (Spec.Aes.expandKeyScratchContract X86.abi) :=
  Verified.of_correct (expandKey_correct bodies) expandKey_ct (by
    have a0 : arg ekSat 0 = 0x1000 := by decide
    have a1 : arg ekSat 1 = 16 := by decide
    have a2 : arg ekSat 2 = 0x2000 := by decide
    have a3 : arg ekSat 3 = 0x3000 := by decide
    have e : argAddr ekSat 0 = 0x8004 := by decide
    have esp : ekSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Aes.expandKeyScratchContract, Spec.Aes.expandKeyScratchSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.Aes.expandKeyX86] [a0, a1, a2, a3, e, esp] using ekSat)

end VG.Proof.Aes.X86.AesNi

end
