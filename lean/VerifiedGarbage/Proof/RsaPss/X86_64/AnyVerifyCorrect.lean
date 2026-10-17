module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyBody
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS verification with the hash functions as arguments on x86-64: the calling convention

`verifyAny_safe` and `verifyAny_xd`: what the code may do; `verify_okA`:
from the entry state, for the hash functions the selectors name, it meets
`verifyAnyK` and keeps its return address.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

theorem public_safe (v : PublicImpl) : v.code.allInstrs safeI = true := by
  rw [safeI_eq, allInstrs_and, v.mxSafe, Bool.and_true, Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [(SpSafe.of_all v.spSafe) i hi]
  rfl

theorem verifyAny_safe {hs : List Hash} (ht : TierOk hs) (v : PublicImpl) :
    (AnyHash.verify hs v.name v.code).allInstrs safeI = true := by
  simp only [AnyHash.pubArgs, AnyHash.verify, AnyHash.verifyBody, seqs, AnyHash.verifyMain, Code.allInstrs,
    mgfXorAny_safe ht, verifyTailD_safe ht, public_safe v, rec_all, List.all_append, verifyFail, emLenAny,
    AnyHash.anyArgs, posScan, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

theorem verifyAny_xd {hs : List Hash} (ht : TierOk hs) (v : PublicImpl) :
    (AnyHash.verify hs v.name v.code).x86_64Depth ≤ verifyStack := by
  have h1 := mgfXorAny_xd ht
  have h2 := verifyTailD_xd ht
  simp only [AnyHash.pubArgs, AnyHash.verify, AnyHash.verifyBody, seqs, AnyHash.verifyMain, Code.x86_64Depth,
    x86_64Depth_zero v.nosp v.depth, verifyFail, emLenAny, AnyHash.anyArgs, posScan, byteLoop,
    X86_64.Instr.frameBytes]
  unfold verifyStack frameBytes at *
  rw [Nat.add_comm _ 392]
  refine Nat.add_le_add_left ?_ 392
  simp only [Nat.max_le]
  omega

theorem verify_okA {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs) {H : Hash} (hkH : hs[kh] = H) (hH : HashOK H) (K : Callees H)
    (lk : MgfLink H hH) (hG : HashOK hs[g]) (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG) (v : PublicImpl)
    (s : State) (h : verifyAnyK.pre s) (hsk : vhsel s = kh) (hsg : vmsel s = g)
    (hHs : Spec.HashId.mgf1 kh = some lk.G) (hGs : Spec.HashId.mgf1 g = some lkG.G) :
    ∃ t s', Exec isa (AnyHash.verify hs v.name v.code) s t s' ∧ abiPreserved s s' ∧ verifyAnyK.post s s' := by
  have hp := VPreA.of lk.G h (by rw [hsk]; exact hHs)
  have hsf := verifyAny_safe ht v
  have hW := X86_64.WP.stackFrame (safe_sp hsf) (by have := verifyAny_xd ht v; unfold verifyStack at this; omega)
    (code_okA hkh hg hl ht hkH hH K lk hG KG lkG v h hsk hsg hHs hGs)
  obtain ⟨t, s', he, hq⟩ := WP.mono_mx (safe_mx hsf) hW fun s' q hmx => (⟨q, hmx⟩ : _ ∧ _)
  obtain ⟨⟨⟨hcs, hpost⟩, hf⟩, hmx⟩ := hq
  refine ⟨t, s', he, ⟨hcs, ?_, by rw [hmx]⟩, hpost⟩
  -- The return address.
  have hd := verifyAny_xd ht v
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (AnyHash.verify hs v.name v.code).x86_64Depth) (k := 8)
      (by unfold verifyStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64.Any
