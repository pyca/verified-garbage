module

public import VerifiedGarbage.Proof.RsaPss.X86.Hash
public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# RSASSA-PSS on x86: code that keeps `esp`

`NoSp` of the pieces both functions share: those whose immediates depend on
the hash function (`spOk`, from `Certs.sp`), the hash of a message of secret
length (`ctHash_noSp`) and MGF1's mask (`mgfXor_noSp`), which write `esp`
only through the frames of their calls.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

theorem noSp_ite {c : Cond} {t e : Prog isa} (ht : NoSp t) (he : NoSp e) : NoSp (.ite c t e) := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [ht i h, he i h]

theorem noSp_append {l₁ l₂ : List Instr} (h₁ : NoSp (.block l₁ : Prog isa)) (h₂ : NoSp (.block l₂ : Prog isa)) :
    NoSp (.block (l₁ ++ l₂) : Prog isa) := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [h₁ i h, h₂ i h]

theorem noSp_seq_inv {a b : Prog isa} (h : NoSp (.seq a b)) : NoSp a ∧ NoSp b :=
  ⟨fun i hi => h i (List.mem_append_left _ hi), fun i hi => h i (List.mem_append_right _ hi)⟩

/-- The blocks whose immediates depend on the hash function, from `Certs.sp`. -/
structure SpOk (H : Impl.Pbkdf2.Md.X86.Hash) : Prop where
  lenSet : NoSp (.block (lenSet H) : Prog isa)
  clrB : NoSp (.block (clrArgs oLen H.B) : Prog isa)
  clrY : NoSp (.block (clrArgs oY H.B) : Prog isa)
  padArgs : NoSp (.block (padArgs H) : Prog isa)
  padBody : NoSp (.block (padBody H) : Prog isa)
  blkSet : NoSp (.block (blkSet H) : Prog isa)
  cmpSet : NoSp (.block (cmpSet H) : Prog isa)
  selSet : NoSp (.block (selSet H) : Prog isa)
  outPart : NoSp (outPart H)
  mgfSeed : NoSp (.block (mgfSeed H) : Prog isa)
  ctrSet : NoSp (.block (ctrSet H) : Prog isa)
  xorSet : NoSp (.block (xorSet H) : Prog isa)
  mgfNext : NoSp (.block (mgfNext H) : Prog isa)
  params : NoSp (.block (params H) : Prog isa)
  cpDig16 : NoSp (.block (cpDig H 16) : Prog isa)
  cpDig4 : NoSp (.block (cpDig H 4) : Prog isa)
  lenArgs18 : NoSp (.block (lenArgs H 18) : Prog isa)
  lenArgs7 : NoSp (.block (lenArgs H 7) : Prog isa)
  cpSalt : NoSp (.block (cpSalt H) : Prog isa)
  putH : NoSp (.block (putH H) : Prog isa)
  fxSalt : NoSp (.block (fxSalt H) : Prog isa)
  cpDb : NoSp (.block (cpDb H) : Prog isa)
  passSet : NoSp (.block (passSet H) : Prog isa)
  anyLen : NoSp (.block (anyLen H) : Prog isa)
  cmpArgs : NoSp (.block (cmpArgs H) : Prog isa)

theorem spOk : SpOk h.H := by
  have hsp := h.certs.sp
  simp only [spBlocks, seqs] at hsp
  obtain ⟨s1, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s2, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s3, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s4, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s5, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s6, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s7, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s8, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s9, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s10, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s11, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s12, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s13, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s14, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s15, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s16, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s17, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s18, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s19, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s20, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s21, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s22, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s23, hsp⟩ := noSp_seq_inv hsp
  obtain ⟨s24, s25⟩ := noSp_seq_inv hsp
  exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22,
    s23, s24, s25⟩

theorem ctHash_noSp : NoSp (ctHash h.H) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, -⟩ := spOk h
  have hi : NoSp h.H.st.initC := h.ok.hH.initSp
  have hc : NoSp h.H.compC := h.ok.comp.nosp
  simp only [ctHash, initPart, lenPart, padPart, compLoop, compBody, countLoop, seqs, Impl.Pbkdf2.Md.X86.Hash.cmp,
    Impl.MdStream.X86.compressAt, Impl.MdStream.X86.compressWith, Impl.Pbkdf2.Stream.X86.Hash.callInit]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_loop | with_reducible apply noSp_pushCall
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

theorem mgfXor_noSp : NoSp (mgfXor h.H) := by
  obtain ⟨-, -, s3, -, -, -, -, -, -, s10, s11, s12, s13, -⟩ := spOk h
  have hct := ctHash_noSp h
  simp only [mgfXor, mgfBody, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_loop
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

end VG.Proof.RsaPss.X86
