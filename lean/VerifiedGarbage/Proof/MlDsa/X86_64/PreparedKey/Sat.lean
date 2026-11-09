module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignPre
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on x86-64: states holding prepared keys

Untrusted: everything here is checked by Lean. The preconditions of
`preparedSignMessageContract` and `preparedVerifyMessageContract` can be
satisfied: by a state whose memory holds, at `0x1000`, the key that the
verified `prepareSecret` or `preparePublic` (with any primitives meeting their
contracts) writes there, and the other arguments around it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlDsa.X86_64.Verify (Prims)
open VG.Proof.MlDsa.X86_64.Verify (params PrimsOk)
open VG.Proof.MlDsa.X86_64.Verify.Prepare (PPre preparePublic_correct prepareSecret_correct)

/-- The state from which `prepare` writes a prepared key to `0x1000`. -/
def runSat (len size : Nat) : State where
  gpr r := match r with
    | .rdi => 0x200000 | .rsi => 0x1000 | .rdx => 0x300000 | .rsp => 0x400000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x200000, len⟩]
  wr := [⟨0x1000, size⟩, ⟨0x300000, 1024⟩]

theorem runSat_pre {len size : Nat} (hl : len < 0x10000) (hs : size < 0x10000) : PPre len size (runSat len size) := by
  refine ⟨show 32 ≤ (0x400000 : BitVec 64).toNat by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro a h₁ h₂; simp only [Region.Contains, runSat] at h₁ h₂; bv_omega)
    | (simp only [runSat, BitVec.reduceToNat]; omega)

/-- Memory equal to `m` but in `[lo, hi)`. -/
def patch (m : Mem) (lo hi : Nat) (f : Addr → Byte) : Mem := fun a =>
  if lo ≤ a.toNat ∧ a.toNat < hi then f a else m a

theorem patch_bytes {m : Mem} {lo hi : Nat} {f : Addr → Byte} {a : Addr} {len : Nat}
    (h : a.toNat + len ≤ lo) (hlo : lo ≤ 2 ^ 64) : bytesAt (patch m lo hi f) a len = bytesAt m a len := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi'
  have he : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [patch, he]
  exact ite_eq_right_iff.mpr fun h' => absurd h'.1 (by omega)

theorem patch_readW {m : Mem} {lo hi : Nat} {f : Addr → Byte} {a : Addr} (h₁ : lo ≤ a.toNat) (h₂ : a.toNat + 8 ≤ hi)
    (h₃ : a.toNat + 8 < 2 ^ 64) : (patch m lo hi f).readW a 64 = Mem.readW f a 64 :=
  Mem.readW_congr fun i hi' => by
    have hi8 : i < 8 := hi'
    have he : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [patch, he]
    have hc : lo ≤ a.toNat + i ∧ a.toNat + i < hi := by omega
    simp only [hc, and_self, ↓reduceIte]

theorem patch_readW' {m : Mem} {lo hi : Nat} {f : Addr → Byte} {a : Addr} (h : a.toNat + 8 ≤ lo ∨ hi ≤ a.toNat)
    (h₃ : a.toNat + 8 < 2 ^ 64) : (patch m lo hi f).readW a 64 = m.readW a 64 :=
  Mem.readW_congr fun i hi' => by
    have hi8 : i < 8 := hi'
    have he : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [patch, he]
    exact ite_eq_right_iff.mpr fun h' => absurd h' (by omega)

/-! ## Signing -/

/-- The stack arguments `sig = 0xB000` and `scratch = 0x10000`. -/
def sStk (a : Addr) : Byte := if a = 0x80009 then 0xB0 else if a = 0x80012 then 0x01 else 0

def signPSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0xA000 | .rcx => 0xA100 | .r9 => 0xA200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := patch m 0x80008 0x80018 sStk
  rd := [⟨0x1000, preparedSecretKeyBytes p⟩, ⟨0xA000, 0⟩, ⟨0xA100, 0⟩, ⟨0xA200, 32⟩, ⟨0x80008, 16⟩]
  wr := [⟨0xB000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩]

theorem signPrepared_sat {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    ∃ s, (preparedSignMessageContract p X86_64.abi 112).pre s := by
  have hsz : p.skLen < 0x10000 ∧ preparedSecretKeyBytes p < 0x7000 := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  obtain ⟨_, s', _, _, _, hk⟩ := prepareSecret_correct C hp _ (runSat_pre hsz.1 (by omega))
  have hk' : PreparedSecretKey p (signPSat p s'.mem).mem 0x1000 :=
    prepared_congr (patch_bytes (by simp only [BitVec.reduceToNat]; omega) (by decide)) hk
  refine ⟨signPSat p s'.mem, ?_⟩
  have a0 : stackArg (signPSat p s'.mem) 0 = 0xB000 := by
    rw [stackArg, show stackArgAddr (signPSat p s'.mem) 0 = 0x80008 from rfl]
    exact (patch_readW (by decide) (by decide) (by decide)).trans (by decide)
  have a1 : stackArg (signPSat p s'.mem) 1 = 0x10000 := by
    rw [stackArg, show stackArgAddr (signPSat p s'.mem) 1 = 0x80010 from rfl]
    exact (patch_readW (by decide) (by decide) (by decide)).trans (by decide)
  have b0 : stackArgAddr (signPSat p s'.mem) 0 = 0x80008 := rfl
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [preparedSignMessageContract, preparedSignMessageSig, X86_64.abi, X86_64.argRegs,
      List.range, List.range.loop] <;> sig_and_intros <;> (try simp only [a0, a1, b0])
  all_goals first
    | exact hk'
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

/-! ## Verification -/

/-- `tr = H(pk, 64)` of the key at `0x1000` of `m`, at `0x8000`. -/
def trBytes (p : Params) (m : Mem) (a : Addr) : Byte := (pkTr (bytesAt m 0x1000 p.pkLen)).getD (a.toNat - 0x8000) 0

def verifyPSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x6000 | .rcx => 0x6100 | .r9 => 0x6200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := patch (patch m 0x80008 0x80018 stkMem) 0x8000 0x8040 (trBytes p m)
  rd := [⟨0x1000, preparedPublicKeyBytes p⟩, ⟨0x6000, 0⟩, ⟨0x6100, 0⟩, ⟨0x6200, p.sigLen⟩, ⟨0x8000, 64⟩,
    ⟨0x80008, 16⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyPSat_tr {p : Params} {m : Mem} (hp : preparedPublicKeyBytes p < 0x7000) :
    bytesAt (verifyPSat p m).mem 0x8000 64 = pkTr (bytesAt (verifyPSat p m).mem 0x1000 p.pkLen) := by
  have hpk : p.pkLen ≤ preparedPublicKeyBytes p := by unfold preparedPublicKeyBytes; omega
  have hk : bytesAt (verifyPSat p m).mem 0x1000 p.pkLen = bytesAt m 0x1000 p.pkLen := by
    rw [show (verifyPSat p m).mem = patch (patch m 0x80008 0x80018 stkMem) 0x8000 0x8040 (trBytes p m) from rfl,
      patch_bytes (by simp only [BitVec.reduceToNat]; omega) (by decide),
      patch_bytes (by simp only [BitVec.reduceToNat]; omega) (by decide)]
  rw [hk]
  have hl : (pkTr (bytesAt m 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0x8000 : Addr) + BitVec.ofNat 64 i).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [verifyPSat, patch, trBytes, he, show 0x8000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x8040 by omega, and_self,
    ↓reduceIte, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem verifyPrepared_sat {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    ∃ s, (preparedVerifyMessageContract p X86_64.abi 112).pre s := by
  have hsz : p.pkLen < 0x10000 ∧ preparedPublicKeyBytes p < 0x7000 := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  obtain ⟨_, s', _, _, _, hk⟩ := preparePublic_correct C hp _ (runSat_pre hsz.1 (by omega))
  have hk' : PreparedPublicKey p (verifyPSat p s'.mem).mem 0x1000 :=
    preparedPk_congr (by
      rw [show (verifyPSat p s'.mem).mem =
          patch (patch s'.mem 0x80008 0x80018 stkMem) 0x8000 0x8040 (trBytes p s'.mem) from rfl, patch_bytes (by simp only [BitVec.reduceToNat]; omega) (by decide),
        patch_bytes (by simp only [BitVec.reduceToNat]; omega) (by decide)]) hk
  have htr := verifyPSat_tr (m := s'.mem) hsz.2
  refine ⟨verifyPSat p s'.mem, ?_⟩
  have a0 : stackArg (verifyPSat p s'.mem) 0 = 0x10000 := by
    rw [stackArg, show stackArgAddr (verifyPSat p s'.mem) 0 = 0x80008 from rfl]
    refine ((patch_readW' (by decide) (by decide)).trans (patch_readW (by decide) (by decide) (by decide))).trans (by decide)
  have a1 : stackArg (verifyPSat p s'.mem) 1 = 0x8000 := by
    rw [stackArg, show stackArgAddr (verifyPSat p s'.mem) 1 = 0x80010 from rfl]
    refine ((patch_readW' (by decide) (by decide)).trans (patch_readW (by decide) (by decide) (by decide))).trans (by decide)
  have b0 : stackArgAddr (verifyPSat p s'.mem) 0 = 0x80008 := rfl
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, X86_64.abi, X86_64.argRegs,
      List.range, List.range.loop] <;> sig_and_intros <;> (try simp only [a0, a1, b0])
  all_goals first
    | exact hk'
    | exact htr
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86_64.Message
