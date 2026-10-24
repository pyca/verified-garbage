module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMain
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. The shared contract's public
data as `PubO` (`pubO_of`); constant time (`code_constantTime`, from
`code_ct`); states meeting the precondition for the hash functions the label
is hashed with (`enc_sat`); and `enc_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem leak_eq {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).2, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubO_of {H G : Spec.Mgf1.Hash} {s₁ s₂ : State}
    (h : (Spec.RsaOaep.encryptPrecomputedContract H G abi 304).pub s₁ s₂) : PubO s₁ s₂ := by
  sig_pub [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    stackArgs_seven, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6⟩ := h
  obtain ⟨he, hw⟩ := leak_eq (by simp [bytesAt_length, h6]) (by simp [bytesAt_length, h8]) hl
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm]

theorem pubO_refl (s : State) : PubO s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include cH cG hHh hHl hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi 304).pre
      (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi 304).pub (encrypt H G) :=
  RelCT.constantTime ((code_ct hH cH hG cG hGh hGl hGv hHh hHl).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨hHl ▸ preO_of h₁, pubO_refl s₁⟩, hHl ▸ preO_of h₂, pubO_of hp⟩) fun _ _ h => h)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` against its shared
contract, given a state meeting it. -/
theorem enc_verified (hsat : ∃ s, (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi 304).pre s) :
    Verified PPC64LE.target (encrypt H G) (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi 304) :=
  ⟨code_correct hH hG hHh hHl hGh hGl hGv, code_constantTime hH cH hG cG hHh hHl hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting encryption's contract for `H`: a 512-bit modulus, a
one-byte `e`, an empty label and message, `H`'s seed, a working space of
2080 words, 16 words of `pre` at `0x5000`, and the stack arguments at
`sp + 96`. -/
def encSatState (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10061 then 0x41
    else bif Nat.beq a.toNat 0x10071 then 0x42 else bif Nat.beq a.toNat 0x1007A then 0x02
    else bif Nat.beq a.toNat 0x10080 then 0x20 else bif Nat.beq a.toNat 0x10081 then 0x08
    else bif Nat.beq a.toNat 0x10089 then 0x50 else bif Nat.beq a.toNat 0x10090 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, H.len⟩, ⟨0x5000, 128⟩, ⟨0x10060, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

/-- The hash functions the label is hashed with. -/
def labelHashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512, Spec.Mgf1.sha512_224,
    Spec.Mgf1.sha512_256]

theorem enc_sat {H : Spec.Mgf1.Hash} (G : Spec.Mgf1.Hash) (hH : H ∈ labelHashes) :
    ∃ s, (Spec.RsaOaep.encryptPrecomputedContract H G abi 304).pre s := by
  simp only [labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
      argRegs, stackArgs_seven, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords]
      [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512_256

end VG.Proof.RsaOaep.PPC64LE
