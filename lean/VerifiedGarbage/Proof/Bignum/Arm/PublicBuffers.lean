module

public import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Buffer geometry and immutable input bytes of checked public RSA -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PublicBytes (p : BitVec 32) (k : Nat) (bs : List Byte) (s : State) : Prop where
  fits : p.toNat + k ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr p) k
  bytes : Spec.Rsa.bytesAt s.mem (State.addr p) k = bs

theorem PublicBytes.length {p : BitVec 32} {k : Nat} {bs : List Byte} {s : State}
    (h : PublicBytes p k bs s) : bs.length = k := by
  rw [← h.bytes]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem PublicBytes.byte {p : BitVec 32} {k : Nat} {bs : List Byte} {s : State}
    (h : PublicBytes p k bs s) (i : Nat) (hi : i < bs.length) :
    s.mem (State.addr p + BitVec.ofNat 64 i) = bs[i] := by
  have hk : i < k := by rw [← h.length]; exact hi
  have hl : i < (Spec.Rsa.bytesAt s.mem (State.addr p) k).length := by
    simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using hk
  have eq := congrArg (fun bs : List Byte => bs[i]?) h.bytes
  rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hi] at eq
  simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, Option.some.injEq] using eq

theorem PublicBytes.after_frame {p : BitVec 32} {k : Nat} {bs : List Byte} {s t : State}
    {regions : List Region} {rs : List Reg} (h : PublicBytes p k bs s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (sep : ∀ r ∈ regions, (⟨State.addr p, k⟩ : Region).Disjoint r) : PublicBytes p k bs t :=
  ⟨h.fits, by rw [rest.rd, rest.wr]; exact h.read,
    (rsa_bytes_frame frame (by have := h.fits; omega) sep).trans h.bytes⟩

structure PublicBuffers (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.publicScratchWords k ≤ len
  exponentPositive : 0 < eLen
  exponentFits : eLen ≤ k
  modulus : PublicBytes np k nb s
  exponent : PublicBytes ep eLen eb s
  input : PublicBytes xp k xb s
  outputFit : dst.toNat + k ≤ 2 ^ 32
  write : InRegions s.wr (State.addr dst) k
  modulusSeparate : Region.Disjoint ⟨State.addr np, k⟩ ⟨State.addr base, 8 * len⟩
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  outputSeparate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩
  stackModulus : Region.Disjoint ⟨State.addr np, k⟩ ⟨State.addr s.sp, 56⟩
  stackExponent : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr s.sp, 56⟩
  stackInput : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr s.sp, 56⟩
  stackOutput : Region.Disjoint ⟨State.addr dst, k⟩ ⟨State.addr s.sp, 56⟩

theorem PublicBuffers.after_frame {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} {s t : State} {regions : List Region} {rs : List Reg}
    (h : PublicBuffers base dst np ep xp len k eLen nb eb xb s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (nSep : ∀ r ∈ regions, (⟨State.addr np, k⟩ : Region).Disjoint r)
    (eSep : ∀ r ∈ regions, (⟨State.addr ep, eLen⟩ : Region).Disjoint r)
    (xSep : ∀ r ∈ regions, (⟨State.addr xp, k⟩ : Region).Disjoint r) :
    PublicBuffers base dst np ep xp len k eLen nb eb xb t :=
  ⟨h.workspace.congr rest.wr, h.minLength, h.maxLength, h.space, h.exponentPositive, h.exponentFits,
    h.modulus.after_frame frame rest nSep, h.exponent.after_frame frame rest eSep,
    h.input.after_frame frame rest xSep, h.outputFit, by rw [rest.wr]; exact h.write,
    h.modulusSeparate, h.exponentSeparate, h.inputSeparate, h.outputSeparate,
    by rw [rest.sp]; exact h.stackModulus, by rw [rest.sp]; exact h.stackExponent,
    by rw [rest.sp]; exact h.stackInput, by rw [rest.sp]; exact h.stackOutput⟩

theorem PublicBuffers.after_workspace {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PublicBuffers base dst np ep xp len k eLen nb eb xb s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    PublicBuffers base dst np ep xp len k eLen nb eb xb t :=
  h.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.modulusSeparate)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.exponentSeparate)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.inputSeparate)

theorem PublicBuffers.after_acceptance {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PublicBuffers base dst np ep xp len k eLen nb eb xb s)
    (frame : Frame [⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem) (rest : Rest rs s t) :
    PublicBuffers base dst np ep xp len k eLen nb eb xb t :=
  h.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.stackModulus.sub_right (Offset.sub_base _ (by decide)))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.stackExponent.sub_right (Offset.sub_base _ (by decide)))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact h.stackInput.sub_right (Offset.sub_base _ (by decide)))

end VG.Proof.Bignum.Arm
