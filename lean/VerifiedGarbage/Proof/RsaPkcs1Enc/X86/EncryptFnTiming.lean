module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptFnInput
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptBodyTiming
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptNoSp

/-! # Stack allocation and saved-register restoration reveal only public addresses -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt
open VG.Proof.Rsa.X86.PrivChecked (sp_agree)
open VG.Proof.Dsa.X86 (allocated)

theorem allocation_state {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) :
    a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem allocation_relCT (v : PublicImpl) {g : Geometry} {bs1 bs2 : Fin 5 → List Byte}
    (exponent : bs1 1 = bs2 1) (pre : bs1 4 = bs2 4) :
    RelCT isa (fun a b => ∃ s t, FnInput g bs1 s ∧ FnInput g bs2 t ∧
      a = pushed savedRegisters s ∧ b = pushed savedRegisters t)
      (.frame (.alloc VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes)
        (body v.name v.code) (.free VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes))
      (fun a b => a.gpr .esp = b.gpr .esp) := by
  intro a b ta tb a' b' hp ea eb'
  obtain ⟨s, t, hs, ht, rfl, rfl⟩ := hp
  have sp : (pushed savedRegisters s).gpr .esp = (pushed savedRegisters t).gpr .esp := by
    rw [hs.savedSp, ht.savedSp]
  have post : a'.gpr .esp = b'.gpr .esp := by
    rw [Exec.gpr (allocation_noSp v) ea, Exec.gpr (allocation_noSp v) eb', sp]
  cases ea with
  | frame pa ba _ =>
    cases eb' with
    | frame pb bb _ =>
      have ha := allocation_state pa
      have hb := allocation_state pb
      subst ha hb
      have eq := (body_relCT v exponent pre) _ _ _ _ _ _ ⟨hs.context, ht.context⟩ ba bb
      refine ⟨?_, post⟩
      rw [eq.1]
      rfl

theorem encryptFn_relCT (v : PublicImpl) {g : Geometry} {bs1 bs2 : Fin 5 → List Byte}
    (exponent : bs1 1 = bs2 1) (pre : bs1 4 = bs2 4) :
    RelCT isa (fun s t => FnInput g bs1 s ∧ FnInput g bs2 t)
      (code v.name v.code) (fun _ _ => True) := by
  unfold code
  refine RelCT.frame (R := fun _ _ => True) ?_ ?_
  · intro s t h
    have eq := h.1.savedSp.trans h.2.savedSp.symm
    rw [pushed_esp, pushed_esp] at eq
    have same := congrArg (fun x => x + BitVec.ofNat 32 (4 * savedRegisters.length)) eq
    simpa only [BitVec.sub_add_cancel] using same
  · refine VG.RelCT.seq ((allocation_relCT v (g := g) exponent pre).mono ?_ (fun _ _ h => h))
      (VG.Proof.RsaPkcs1Sig.X86.Sgn.restore_relCT.mono (fun _ _ h => sp_agree h) (fun _ _ _ => trivial))
    rintro a b ⟨s, t, h, rfl, rfl⟩
    exact ⟨s, t, h.1, h.2, rfl, rfl⟩
end VG.Proof.RsaPkcs1Enc.X86.Enc
