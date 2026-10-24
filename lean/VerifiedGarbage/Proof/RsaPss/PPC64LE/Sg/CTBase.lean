module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS signing on PPC64LE: the public data

Untrusted: everything here is checked by Lean. The shared contract's public
data (`PubS`, `pubS_of`): the stack pointer, the pointers and lengths (all
the arguments), the modulus and `e`. An entry state with the anchor's public
data has its modulus' first byte (`PubS.byte`), so its `lo`, and agrees with
it on what `Base` fixes (`signOk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE (Agree Ok B fx)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The shared contract's public data, by name. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 13, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r5) (a.gpr .r6).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat

theorem pubS_of {G : Spec.Mgf1.Hash} {s₁ s₂ : State}
    (h : (Spec.RsaPss.signContract G G abi stackBytes).pub s₁ s₂) : PubS s₁ s₂ := by
  have e : stackBytes = 3775 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  rw [List.map_append, List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [bytesAt_length, h6])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm]

theorem pubS_refl (s : State) : PubS s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

section
variable {a s : State} (p : PubS a s)
include p

theorem PubS.pKk : kk s = kk a := by rw [kk, kk, p.g .r6 (by decide)]

theorem PubS.byte (hk : 1 ≤ kk s) : s.mem (s.gpr .r5) = a.mem (a.gpr .r5) := by
  have := congrArg (·.getD 0 0) p.n
  rwa [VG.Proof.RsaPkcs1Sig.bytesAt_getD hk, VG.Proof.RsaPkcs1Sig.bytesAt_getD (by have := p.pKk; unfold kk at this hk; omega),
    BitVec.add_zero, BitVec.add_zero] at this

theorem PubS.pLo (hk : 1 ≤ kk s) : loS s = loS a := by simp only [loS, p.byte hk]

theorem PubS.pLoN (hk : 1 ≤ kk s) : loN s = loN a := by rw [loN, loN, p.byte hk]

theorem PubS.agree (hk : 1 ≤ kk s) : Agree Ss vS a s := ⟨p.sp, p.args 11 (by decide), fun r hr => by
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vS]
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.args 10 (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.pLo hk⟩

end

/-- `PubS`, for a nonempty modulus. -/
def PubK (a s : State) : Prop := PubS a s ∧ 1 ≤ kk s

/-- `PubK` gives what the shared code needs. -/
theorem signOk (D : Nat) : Ok Ss vS (PreS D) PubK where
  fits P := fits P
  agree p := p.1.agree p.2

/-- `Base` from an entry state with the anchor's public data. -/
abbrev BS (D : Nat) : State → State → Prop := B Ss vS (PreS D) PubK

end VG.Proof.RsaPss.PPC64LE.Sg
