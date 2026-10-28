module
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame

import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.Safe

/-!
# RSASSA-PSS verification on x86-64: correctness

`vlogic`: what the code computes is zero exactly when the encoding is
valid, byte by byte (`VerifyCases.lean`). `verify_body`: from the entry
state, the body of the frame returns 1 exactly when `RsaPss.verify` holds,
with the callee-saved registers restored.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

theorem list_eq_iff_getD {a b : List Byte} {n : Nat} (ha : a.length = n) (hb : b.length = n) :
    a = b ↔ ∀ i < n, a.getD i 0 = b.getD i 0 := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply List.ext_getElem (by omega_arith)
    intro i h₁ h₂
    have := h i (by omega_arith)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at this

theorem ofNat_eq_iff {a : Nat} (ha : a < 2 ^ 64) (b : BitVec 64) : BitVec.ofNat 64 a = b ↔ a = b.toNat := by
  constructor
  · rintro rfl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  · rintro rfl; simp

/-- What the code computes, against the checks of `verifyEncoding`. -/
theorem vlogic (G : Spec.Mgf1.Hash) (hG : Proof.Mgf1.Valid G) (x mHash : List Byte) {k lo z : Nat} (fixed : Bool)
    (slen : BitVec 64) {sLen : Option Nat} (hsl : sLen = if fixed then some slen.toNat else none)
    (hx : x.length = k) (hlo : lo ≤ 1) (hfit : G.len + 2 ≤ k - lo) (hk : k ≤ 1024) :
    let em := x.drop lo
    let L := k - lo - G.len - 1
    let dbL := vDb G em L z
    let fd := decide (lz dbL < L)
    let pos := if lz dbL < L then lz dbL else 0
    let val := if lz dbL < L then dbL.getD (lz dbL) 0 else 0
    (acc1V (acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo) fd val fixed
        (BitVec.ofNat 64 (L - pos - 1)) slen = 0 ∧
      ∀ i < G.len, (G.hash (Spec.RsaPss.zeros 8 ++ mHash ++ dbL.drop (pos + 1))).getD i 0 = (vH G em L).getD i 0) ↔
    ((lo = 1 → x.getD 0 0 = 0) ∧ EncOk G mHash em (k - lo) z sLen) := by
  dsimp only
  have hvH : (vH G (x.drop lo) (k - lo - G.len - 1)).length = G.len := by simp [vH]; omega_arith
  rw [acc1V_eq_zero, acc0V_eq_zero _ _ _ _ hlo]
  have e1 : x.getD (k - 1) 0 = (x.drop lo).getD (k - lo - 1) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]; congr 2; omega_arith
  have e2 : x.getD lo 0 = (x.drop lo).getD 0 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  rw [e1, e2]
  unfold EncOk
  rw [← list_eq_iff_getD (hG.2 _) hvH]
  generalize vDb G (x.drop lo) (k - lo - G.len - 1) z = dbL
  by_cases hf : lz dbL < k - lo - G.len - 1
  · rw [ifp hf, ifp hf, decide_eq_true hf, ofNat_eq_iff (by omega_arith)]
    subst hsl
    constructor
    · rintro ⟨⟨⟨hA, hP, hB⟩, hC, -, hS⟩, hH⟩
      refine ⟨hP, hA, hB, hf, hC, ?_, hH⟩
      cases fixed
      · exact .inl rfl
      · exact .inr (by rw [ifp rfl]; congr 1; have := hS rfl; omega_arith)
    · rintro ⟨hP, hA, hB, -, hC, hS, hH⟩
      refine ⟨⟨⟨hA, hP, hB⟩, hC, rfl, fun hfx => ?_⟩, hH⟩
      subst hfx
      rw [ifp rfl] at hS
      rcases hS with h | h
      · cases h
      · have := Option.some.inj h; omega_arith
  · rw [decide_eq_false hf]
    constructor
    · rintro ⟨⟨_, _, h, _⟩, _⟩; cases h
    · rintro ⟨_, _, _, h, _⟩; exact absurd h hf

variable {G : Spec.Mgf1.Hash}

variable (G) in
/-- What `verifyK.post` asks of `rax`. -/
def verifyOut (s : State) : Bool :=
  Spec.RsaPss.verify G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat)
    (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32))

variable (G) in
/-- Before the epilogue: the result in `rax`, the saved registers in their
slots. -/
structure VDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 3)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : (t.gpr .rax).setWidth 32 = if verifyOut G s then 1 else 0

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem vmid_safe : (seqs [.block acc0, mgfXor H, .block clearTop, scanCheck H]).allInstrs safeI = true := by
  simp only [seqs, scanCheck, prefixCheck, prefixWords, prefixBytes, posScan, posCheck, Code.allInstrs,
    mgfXor_safe hH K, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem vmid_xd : (seqs [.block acc0, mgfXor H, .block clearTop, scanCheck H]).x86_64Depth = 8 := by
  simp only [seqs, scanCheck, prefixCheck, prefixWords, prefixBytes, posScan, posCheck, byteLoop, Code.x86_64Depth,
    mgfXor_xd K]
  rfl

theorem ite_setWidth {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) :
    ((if p then 1 else 0 : BitVec 64).setWidth 32) = if b then 1 else 0 := by
  by_cases hb : b = true
  · rw [ifp (h.mpr hb), ifp hb]; rfl
  · rw [ifn (fun hp => hb (h.mp hp)), ifn hb]; rfl

theorem map_range_drop {x : List Byte} {lo n : Nat} (hn : lo + n ≤ x.length) {f : Nat → Byte}
    (hf : ∀ i < n, f i = x.getD (lo + i) 0) : (List.range n).map f = (x.drop lo).take n := by
  rw [list_eq_iff_getD (n := n) (by simp) (by simp; omega_arith)]
  intro i hi
  rw [getD_map_range, ifp hi, hf i hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]

end VG.Proof.RsaPss.X86_64
