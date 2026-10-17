module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
public import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS on x86-64 with the hash functions as arguments: what the code may do

No instruction writes `rsp` or loads MXCSR (`safeI`), and the code uses
8 bytes of stack between its calls (the return address of the hash
functions' calls), for any list of hash functions whose code is such
(`TierOk`): the dispatches are their cases', and their tests' (`cmp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- What the proofs know of each of the hash functions `hs`. -/
def TierOk (hs : List Hash) : Prop := ∀ h ∈ hs, Nonempty (HashOK h) ∧ Callees h

theorem chain_all {p : Instr → Bool} (hp : ∀ k, (Impl.Dispatch.X86_64.test k).all p = true) :
    ∀ cs : List (Nat × Prog isa), (∀ c ∈ cs, c.2.allInstrs p = true) →
      (Impl.Dispatch.X86_64.chain cs).allInstrs p = true
  | [], _ => rfl
  | [(_, c)], h => h (_, c) List.mem_cons_self
  | (k, c) :: c' :: cs, h => by
    have h1 := h (k, c) List.mem_cons_self
    have h2 := chain_all hp (c' :: cs) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [Impl.Dispatch.X86_64.chain, Impl.Dispatch.chain] at h2 ⊢
    simp only [Code.allInstrs, h1, h2, Bool.and_true]
    rw [rec_all]; exact hp k

theorem chain_xd {d : Nat} :
    ∀ cs : List (Nat × Prog isa), (∀ c ∈ cs, c.2.x86_64Depth ≤ d) →
      (Impl.Dispatch.X86_64.chain cs).x86_64Depth ≤ d
  | [], _ => Nat.zero_le _
  | [(_, c)], h => h (_, c) List.mem_cons_self
  | (k, c) :: c' :: cs, h => by
    have h1 : c.x86_64Depth ≤ d := h (k, c) List.mem_cons_self
    have h2 := chain_xd (c' :: cs) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [Impl.Dispatch.X86_64.chain, Impl.Dispatch.chain] at h2 ⊢
    simp only [Code.x86_64Depth]
    omega

theorem dispatch_all {p : Instr → Bool} (hp : ∀ k, (Impl.Dispatch.X86_64.test k).all p = true) {d : Nat}
    (hd : p (.mov .rax (.mem (sp d))) = true) {f : Hash → Prog isa} {hs : List Hash}
    (hf : ∀ h ∈ hs, (f h).allInstrs p = true) : (dispatch d f hs).allInstrs p = true := by
  simp only [dispatch, Code.allInstrs, hd, Bool.true_and]
  refine chain_all hp _ fun c hc => ?_
  simp only [cases, List.mem_mapIdx] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact hf _ (List.getElem_mem hi)

theorem dispatch_xd {d e : Nat} {f : Hash → Prog isa} {hs : List Hash} (hf : ∀ h ∈ hs, (f h).x86_64Depth ≤ e) :
    (dispatch d f hs).x86_64Depth ≤ e := by
  simp only [dispatch, Code.x86_64Depth]
  refine Nat.max_le.mpr ⟨Nat.zero_le _, chain_xd _ fun c hc => ?_⟩
  simp only [cases, List.mem_mapIdx] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact hf _ (List.getElem_mem hi)

theorem test_safe (k : Nat) : (Impl.Dispatch.X86_64.test k).all safeI = true := rfl

variable {H : Hash} (hH : HashOK H) (K : Callees H)

include hH K in
theorem signPre_safe : (signPre H).allInstrs safeI = true := by
  simp only [signPre, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, Code.allInstrs, ctHash_safe hH K,
    rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem signPre_xd : (signPre H).x86_64Depth ≤ 8 := by
  simp only [signPre, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, byteLoop, Code.x86_64Depth,
    ctHash_xd K]
  decide

include hH K in
theorem gPart_safe : (gPart H).allInstrs safeI = true := by
  have hl : H.P.len.all safeI = true := hH.taints.lenSafe
  have ho : H.P.out.all safeI = true := hH.taints.outSafe
  simp only [gPart, mgfHashAny, directRest, genericRest, seqs, ctInit, slotPad80, lenLoop, compLoop, select,
    directLen_safe (H := H), xorOut_safe (H := H), Code.allInstrs, comp_safe K, init_safe K, rec_all, lenField,
    digestOut, digestAt, List.all_append, hl, ho, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem gPart_xd : (gPart H).x86_64Depth ≤ 8 := by
  simp only [gPart, mgfHashAny, directRest, genericRest, seqs, ctInit, slotPad80, lenLoop, compLoop, select,
    directLen_xd (H := H), xorOut_xd (H := H), Code.x86_64Depth, K.cXD, K.iXD, byteLoop]
  decide

theorem mgfXorAny_safe {hs : List Hash} (ht : TierOk hs) : (mgfXorAny hs).allInstrs safeI = true := by
  have hd := dispatch_all (p := safeI) test_safe (d := sMsel) rfl (f := gPart) (hs := hs)
    fun h hh => let ⟨⟨hH⟩, K⟩ := ht h hh; gPart_safe hH K
  simp only [mgfXorAny, seedPart, seqs, clearSeedBlocks, copySeed, Code.allInstrs, hd, rec_all, List.all_append,
    byteLoop, step, Bool.and_true]
  rfl

theorem mgfXorAny_xd {hs : List Hash} (ht : TierOk hs) : (mgfXorAny hs).x86_64Depth ≤ 8 := by
  have hd := dispatch_xd (d := sMsel) (f := gPart) (hs := hs) fun h hh => gPart_xd (ht h hh).2
  simp only [mgfXorAny, seedPart, seqs, clearSeedBlocks, copySeed, Code.x86_64Depth, byteLoop]
  omega

theorem signEncAny_safe {hs : List Hash} (ht : TierOk hs) : (AnyHash.signEnc hs).allInstrs safeI = true := by
  have hd := dispatch_all (p := safeI) test_safe (d := sHsel) rfl (f := signPre) (hs := hs)
    fun h hh => let ⟨⟨hH⟩, K⟩ := ht h hh; signPre_safe hH K
  simp only [AnyHash.signEnc, seqs, Code.allInstrs, hd, mgfXorAny_safe ht, rec_all, Bool.true_and]
  rfl

theorem signEncAny_xd {hs : List Hash} (ht : TierOk hs) : (AnyHash.signEnc hs).x86_64Depth ≤ 8 := by
  have hd := dispatch_xd (d := sHsel) (f := signPre) (hs := hs) fun h hh => signPre_xd (ht h hh).2
  have hm := mgfXorAny_xd ht
  simp only [AnyHash.signEnc, seqs, Code.x86_64Depth]
  omega

end VG.Proof.RsaPss.X86_64.Any
