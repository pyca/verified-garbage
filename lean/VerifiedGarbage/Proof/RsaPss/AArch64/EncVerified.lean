module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCTBase
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
import VerifiedGarbage.Proof.RsaPss.AArch64.EncTop
import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT

/-!
# EMSA-PSS's encoding on AArch64: `Verified`

The shared contract (`Proof.RsaPss.encodeContract`, with the stack of the
frame and the hash functions' calls, `encStack`) from correctness
(`code_ok`), constant time (`code_ct`) and a state meeting the precondition
(`enc_sat`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK mdHashes)
open VG.Proof.RsaPss.AArch64 (PssChecks)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

/-- MGF1's hash function, as a hash function of `MdHash` takes it, is valid. -/
theorem mgf_valid {H : Hash} {hH : HashOK H} (lk : Proof.Pbkdf2.Md.AArch64.MgfLink H hH) :
    Proof.Mgf1.Valid lk.G := by
  have hD := hH.sizes.D0
  refine ⟨by rw [lk.len]; exact hD, fun x => ?_⟩
  rw [lk.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, lk.len]
  have := hH.sizes.DN
  omega

section
variable {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
  (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D)

include hH hGh hGl hG in
theorem code_correct (s : State) (h : (Proof.RsaPss.encodeContract G G abi encStack).pre s) :
    ∃ t s', Exec isa (encode H) s t s' ∧ abiPreserved s s' ∧
      (Proof.RsaPss.encodeContract G G abi encStack).post s s' := by
  have hp := preE_of G h
  rw [hGl] at hp
  obtain ⟨t, s', he, habi, hr⟩ := code_ok hH hGh hGl hG hp
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, List.append_eq]
  exact hr

include hH hGh hGl hG hc in
theorem code_constantTime :
    ConstantTime isa (Proof.RsaPss.encodeContract G G abi encStack).pre
      (Proof.RsaPss.encodeContract G G abi encStack).pub (encode H) :=
  RelCT.constantTime ((code_ct hH hGh hGl hG hc).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨hGl ▸ preE_of G h₁, PubE.refl s₁⟩, hGl ▸ preE_of G h₂, pubE_of G hp⟩) fun _ _ h => h)

include hH hGh hGl hG hc in
theorem code_verified (hsat : ∃ s, (Proof.RsaPss.encodeContract G G abi encStack).pre s) :
    Verified AArch64.target (encode H) (Proof.RsaPss.encodeContract G G abi encStack) :=
  ⟨code_correct hH hGh hGl hG, code_constantTime hH hGh hGl hG hc, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A 64-byte encoding of 511 bits, the digest, an empty salt, a working
space of 1024 words, and the stack pointer at `2^40`, far above them. -/
def satState (G : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x4600 | .x3 => 0x4700 | .x5 => 511 | .x6 => 0x20000 | .x7 => 1024
    | _ => 0
  sp := 0x10000000000
  mem _ := 0
  rd := [⟨0x4600, G.len⟩, ⟨0x4700, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 1024 * 8⟩]

/-- `encodeContract` is satisfiable for each of `MdHash`'s hash functions. -/
theorem enc_sat {G : Spec.Mgf1.Hash} (hG : G ∈ mdHashes) :
    ∃ s, (Proof.RsaPss.encodeContract G G abi encStack).pre s := by
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.md5
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha1
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha224
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha256
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha384
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_224
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encStack, stk, frameBytes,
      List.append_eq] [satState, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_256

end VG.Proof.RsaPss.AArch64.Enc
