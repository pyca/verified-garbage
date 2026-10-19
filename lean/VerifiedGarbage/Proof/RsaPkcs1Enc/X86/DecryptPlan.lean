module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptArguments
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptLocal

/-! # Composing hash-call arguments while preserving every earlier slot -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

inductive CallArg where
  | input (i : Nat)
  | inputAdd (i v : Nat)
  | value (v : Nat)
  | scratch (d : Nat)

def CallArg.valid : CallArg → Prop
  | .input i | .inputAdd i _ => i < 23 | _ => True

def CallArg.code (a : CallArg) (j : Nat) : List Instr :=
  match a with
  | .input i => copyArg i j | .value v => immArg v j | .scratch d => scratchArg d j
  | .inputAdd i v => [.mov .eax (.mem (incoming i)), .alu .add .eax (.imm (BitVec.ofNat 32 v)), .store (stackAt (4 * j)) .eax]

def CallArg.valueAt (g : Geometry) : CallArg → BitVec 32
  | .input i => g.argument i | .value v => BitVec.ofNat 32 v | .scratch d => g.workspace + BitVec.ofNat 32 d
  | .inputAdd i v => g.argument i + BitVec.ofNat 32 v

theorem plan_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (plan : Nat → CallArg) (n : Nat) (bound : n ≤ 20)
    (valid : ∀ j < n, (plan j).valid) :
    WP isa (.block ((List.range n).flatMap fun j => (plan j).code j)) s fun t => Context g bs t ∧
      Arguments g (fun j => (plan j).valueAt g) n t ∧
      Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨h, by intro j hj; omega, Frame.refl _ _, Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) (fun j hj => valid j (by omega))) ?_
    rintro u ⟨hu, args, F, K⟩
    have next : WP isa (.block ((plan n).code n)) u fun t => Context g bs t ∧
        Arguments g (fun j => (plan j).valueAt g) (n + 1) t ∧
        Frame [⟨byteAddr g.stack, 80⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
      apply prepareArgument_ok args (by omega)
      have good := valid n (by omega)
      cases e : plan n with
      | input i => exact copyArg_ok u hu (by simpa only [e, CallArg.valid] using good) (by omega)
      | inputAdd i v => exact inputAddArg_ok hu (by simpa only [e, CallArg.valid] using good) (by omega) v
      | value v => exact immArg_ok hu v (by omega)
      | scratch d => exact scratchArg_ok hu d (by omega)
    refine WP.mono next ?_
    rintro t ⟨ht, argsT, Ft, Kt⟩
    exact ⟨ht, argsT, F.trans Ft, K.trans Kt⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
