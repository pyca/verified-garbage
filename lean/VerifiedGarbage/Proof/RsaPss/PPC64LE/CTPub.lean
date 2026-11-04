module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Correct
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View

/-!
# RSASSA-PSS verification on PPC64LE: the public data

Untrusted: everything here is checked by Lean. The shared contract's public
data (`PubP`, `pubP_of`): the stack pointer, the pointers and lengths, the
salt-length mode, the modulus, `e` and `pre`. An entry state with the
anchor's public data has its modulus' first byte (`PubP.byte`), so its
`lo`, `c` and `dbLen`, and agrees with it on what `Base` fixes (`pssOk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Proof.RsaOaep.PPC64LE (Base Fits fx Agree Ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubP (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  a1 : (stackArg s 1).setWidth 32 = (stackArg a 1).setWidth 32
  args : ∀ i, i < 8 → i ≠ 1 → stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s) = Spec.Rsa.bytesAt a.mem (a.gpr .r3) (kk a)
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r5) (a.gpr .r6).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat

theorem pubP_refl (s : State) : PubP s s := ⟨rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq3 {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    a = c ∧ b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).1, (List.append_inj hi ha).2,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

/-- The contract's public data: `PubP`, the tables' functions at the same
addresses, and the same tables held. -/
theorem pubT_of {hs gs : List FnTable} {s₁ s₂ : State} (h : (verSpec hs gs).pub s₁ s₂) :
    PubP s₁ s₂ ∧
      (∀ f ∈ (hs.map (fun T : FnTable => T.fns)).flatten ++ (gs.map (fun T : FnTable => T.fns)).flatten,
        s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ hs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 6) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 6) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ gs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 7) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 7) (FnTable.words isa s₂ T)) := by
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec at h
  rw [e] at h
  sig_pub [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htab, htab', hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨hn, he, hw⟩ := leak_eq3 (by simp [bytesAt_length, h4]) (by simp [bytesAt_length, h6]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, a1.symm, fun i hi h1 => ?_, hn.symm, he.symm, hw.symm⟩, hsy,
    fun T hT => htab _ _ rfl rfl T hT, fun T hT => htab' _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

section
variable {a s : State} (p : PubP a s)
include p

theorem PubP.byte (hk : 1 ≤ kk s) : s.mem (s.gpr .r3) = a.mem (a.gpr .r3) := by
  have e4 : kk s = kk a := by rw [kk, kk, p.g .r4 (by decide)]
  have := congrArg (·.getD 0 0) p.n
  rwa [bytesAt_getD _ _ hk, bytesAt_getD _ _ (by omega), BitVec.add_zero, BitVec.add_zero] at this

theorem PubP.pAny : anyL s = anyL a := by unfold anyL; rw [p.a1]

theorem PubP.pN0 (hk : 1 ≤ kk s) : n0 s = n0 a := by rw [n0, n0, p.byte hk]

theorem PubP.pLo (hk : 1 ≤ kk s) : lo s = lo a := by simp only [lo, smear, p.pN0 hk]

theorem PubP.pCm (hk : 1 ≤ kk s) : cm s = cm a := by rw [cm, cm, p.pLo hk]; simp only [smear, p.pN0 hk]

theorem PubP.pLoN (hk : 1 ≤ kk s) : loN s = loN a := by rw [loN, loN, p.byte hk]

theorem PubP.pCB (hk : 1 ≤ kk s) : cB s = cB a := by rw [cB, cB, p.byte hk]

theorem PubP.pKk : kk s = kk a := by rw [kk, kk, p.g .r4 (by decide)]

theorem PubP.pSp : Sp s = Sp a := p.args 2 (by decide) (by decide)

theorem PubP.agree {D : Nat} (hk : 1 ≤ kk s) : Agree Sp (vP D) a s := ⟨p.sp, p.pSp, fun r hr => by
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vP]
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.pLo hk
  · exact p.pCm hk
  · exact p.args 0 (by decide) (by decide)
  · exact p.pAny
  · rw [dbLen, dbLen, p.pLo hk, p.g .r4 (by decide)]
  · exact p.args 4 (by decide) (by decide)
  · exact p.args 5 (by decide) (by decide)⟩

end

/-- `PubP`, for a nonempty modulus. -/
def PubK (a s : State) : Prop := PubP a s ∧ 1 ≤ kk s

/-- `PubK` gives what the shared code needs. -/
theorem pssOk (D : Nat) {Pre : State → Prop} (hP : ∀ {s}, Pre s → PreP D s) : Ok Sp (vP D) Pre PubK where
  fits P := (hP P).fits
  agree p := p.1.agree p.2

end VG.Proof.RsaPss.PPC64LE
