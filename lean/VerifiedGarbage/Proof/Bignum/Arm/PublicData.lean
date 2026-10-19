module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
import VerifiedGarbage.Proof.Framework.Offset

/-! # Immutable input buffers shared by ordinary and precomputed public RSA -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PublicData (base dst ep xp : BitVec 32) (len k eLen : Nat)
    (eb xb : List Byte) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.publicScratchWords k ≤ len
  exponentPositive : 0 < eLen
  exponentFits : eLen ≤ k
  exponent : PublicBytes ep eLen eb s
  input : PublicBytes xp k xb s
  outputFit : dst.toNat + k ≤ 2 ^ 32
  write : InRegions s.wr (State.addr dst) k
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  outputSeparate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩
  stackExponent : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr s.sp, 56⟩
  stackInput : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr s.sp, 56⟩
  stackOutput : Region.Disjoint ⟨State.addr dst, k⟩ ⟨State.addr s.sp, 56⟩

theorem PublicData.after_frame {base dst ep xp : BitVec 32} {len k eLen : Nat}
    {eb xb : List Byte} {s t : State} {regions : List Region} {rs : List Reg}
    (h : PublicData base dst ep xp len k eLen eb xb s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (eSep : ∀ r ∈ regions, (⟨State.addr ep, eLen⟩ : Region).Disjoint r)
    (xSep : ∀ r ∈ regions, (⟨State.addr xp, k⟩ : Region).Disjoint r) :
    PublicData base dst ep xp len k eLen eb xb t :=
  ⟨h.workspace.congr rest.wr, h.minLength, h.maxLength, h.space, h.exponentPositive, h.exponentFits,
    h.exponent.after_frame frame rest eSep,
    h.input.after_frame frame rest xSep, h.outputFit, by rw [rest.wr]; exact h.write,
    h.exponentSeparate, h.inputSeparate, h.outputSeparate,
    by rw [rest.sp]; exact h.stackExponent,
    by rw [rest.sp]; exact h.stackInput, by rw [rest.sp]; exact h.stackOutput⟩

theorem PublicData.after_workspace {base dst ep xp : BitVec 32} {len k eLen : Nat}
    {eb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PublicData base dst ep xp len k eLen eb xb s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    PublicData base dst ep xp len k eLen eb xb t :=
  h.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.exponentSeparate)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.inputSeparate)

theorem PublicData.after_acceptance {base dst ep xp : BitVec 32} {len k eLen : Nat}
    {eb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PublicData base dst ep xp len k eLen eb xb s)
    (frame : Frame [⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem) (rest : Rest rs s t) :
    PublicData base dst ep xp len k eLen eb xb t :=
  h.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.stackExponent.sub_right (Offset.sub_base _ (by decide)))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.stackInput.sub_right (Offset.sub_base _ (by decide)))

theorem PublicBuffers.data {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} {s : State} (h : PublicBuffers base dst np ep xp len k eLen nb eb xb s) :
    PublicData base dst ep xp len k eLen eb xb s :=
  ⟨h.workspace, h.minLength, h.maxLength, h.space, h.exponentPositive, h.exponentFits,
    h.exponent, h.input, h.outputFit, h.write, h.exponentSeparate,
    h.inputSeparate, h.outputSeparate, h.stackExponent, h.stackInput, h.stackOutput⟩

end VG.Proof.Bignum.Arm
