module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCTBase
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
import VerifiedGarbage.Proof.RsaPss.AArch64.ChkTop
import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCT

/-!
# EMSA-PSS's check of an encoding on AArch64: `Verified`

The shared contract (`Proof.RsaPss.checkEncodingContract`, with the stack of
the frame and the hash functions' calls, `chkStack`) from correctness
(`code_ok`), constant time (`code_ct`) and a state meeting the precondition
(`chk_sat`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK mdHashes)
open VG.Proof.RsaPss.AArch64 (PssChecks)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

section
variable {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
  (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D)

include hH hGh hGl hG in
theorem code_correct (s : State) (h : (Proof.RsaPss.checkEncodingContract G G abi chkStack).pre s) :
    ∃ t s', Exec isa (checkEncoding H) s t s' ∧ abiPreserved s s' ∧
      (Proof.RsaPss.checkEncodingContract G G abi chkStack).post s s' := by
  have hp := preC_of G h
  rw [hGl] at hp
  obtain ⟨t, s', he, habi, hr⟩ := code_ok hH hGh hGl hG hp
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, List.append_eq]
  exact hr

include hH hGh hGl hG hc in
theorem code_constantTime :
    ConstantTime isa (Proof.RsaPss.checkEncodingContract G G abi chkStack).pre
      (Proof.RsaPss.checkEncodingContract G G abi chkStack).pub (checkEncoding H) :=
  RelCT.constantTime ((code_ct hH hGh hGl hG hc).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨hGl ▸ preC_of G h₁, PubC.refl s₁⟩, hGl ▸ preC_of G h₂, pubC_of G hp⟩) fun _ _ h => h)

include hH hGh hGl hG hc in
theorem code_verified (hsat : ∃ s, (Proof.RsaPss.checkEncodingContract G G abi chkStack).pre s) :
    Verified AArch64.target (checkEncoding H) (Proof.RsaPss.checkEncodingContract G G abi chkStack) :=
  ⟨code_correct hH hGh hGl hG, code_constantTime hH hGh hGl hG hc, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- The digest, a 64-byte encoding of 511 bits, a working space of 1024
words, and the stack pointer at `2^40`, far above them. -/
def satState (G : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x4600 | .x1 => 0x1000 | .x2 => 64 | .x3 => 511 | .x6 => 0x20000 | .x7 => 1024
    | _ => 0
  sp := 0x10000000000
  mem _ := 0
  rd := [⟨0x4600, G.len⟩, ⟨0x1000, 64⟩]
  wr := [⟨0x20000, 1024 * 8⟩]

/-- `checkEncodingContract` is satisfiable for each of `MdHash`'s hash
functions. -/
theorem chk_sat {G : Spec.Mgf1.Hash} (hG : G ∈ mdHashes) :
    ∃ s, (Proof.RsaPss.checkEncodingContract G G abi chkStack).pre s := by
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.md5
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha1
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha224
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha256
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha384
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_224
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_256

end VG.Proof.RsaPss.AArch64.Chk
