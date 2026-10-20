module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerStack
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers

/-! # Read-only ciphertext and exponent buffers for one CRT factor -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

structure CrtPowerSources (base xp ep : BitVec 32) (len w k eLen slot : Nat) (xb eb : List Byte) (s : State) : Prop where
  stack : CrtPowerStack base xp ep len k eLen slot s
  input : PublicBytes xp k xb s
  exponent : PublicBytes ep eLen eb s
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputPositive : 0 < k
  inputFits : k ≤ 8 * w
  exponentPositive : 0 < eLen
  exponentFits : eLen < 2 ^ 32

theorem CrtPowerSources.after_workspace {s t : State} {base xp ep : BitVec 32}
    {len w k eLen slot : Nat} {xb eb : List Byte} {rs : List Reg}
    (h : CrtPowerSources base xp ep len w k eLen slot xb eb s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtPowerSources base xp ep len w k eLen slot xb eb t :=
  ⟨h.stack.after_workspace frame rest,
    h.input.after_frame frame rest (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.inputSeparate),
    h.exponent.after_frame frame rest (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.exponentSeparate),
    h.inputSeparate, h.exponentSeparate, h.inputPositive, h.inputFits, h.exponentPositive, h.exponentFits⟩

end VG.Proof.Bignum.Arm
