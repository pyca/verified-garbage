module

public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
public import VerifiedGarbage.Impl.RsaPss.RISCV64
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Mgf1.Bytes
import all Init.Data.Nat.Bitwise.Basic

/-!
# RSASSA-PSS verification on RISC-V: the precondition

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Pre.lean`, `Params.lean`, `ShiftV.lean`): `PreP D s`,
the shared contract's precondition (`Spec.RsaPss.verifyPrecomputedTableContract`,
with the stack of the frame and of the streaming hash functions,
`stackBytes`), by name (`preP_of`); the working space and the values `Base`
fixes in `s1`–`s4` (`Sp`, `vP`: `k`, the digest, and the encoding's
parameters `lo` and `dbLen` from the modulus' first byte), the values kept
in `s5`–`s7` (`cm`, `salt_len`, `anyL`), and what `Base` needs of the entry
(`PreP.fits`). For a modulus whose first byte is not zero, `lo` and `c` are
those of EMSA-PSS (`lo_eq`, `cm_eq`). A pass of the shift (`passV`) replaces
each of `n` bytes from `b` by the one `d` bytes after it, or none, by one
bit; ten passes by the bits of `a < 2^10` shift the `n` bytes left by `a`
(`shV_eq`), if the `2^9` bytes after them are zero.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes saved oEm oSt oDig oCtr oRsa mgfXor save restore)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR stackBytes)
open VG.Proof.RsaPkcs1Sig.RISCV64 (zx)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_mov wp_addSp wp_nil wp_lbu wp_srl wp_sll wp_or wp_and wp_sub
  wp_subi wp_li)
open VG.Proof.RsaOaep.RISCV64 (fb fr save_ok Saves fb_al stackArgAddr_eq)

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

/-- The buffers: `n`, `e`, the digest, the signature, the working space, the
precomputed values, the tables of the hash function and of MGF1's, and the
arguments on the stack. -/
abbrev nR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev dR (D : Nat) (s : State) : Region := ⟨s.gpr .a4, D⟩
abbrev gR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 6) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 7) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- What the code needs of `verifyPrecomputedTableContract.pre`, by name,
for a hash function of `D`-byte digests (the table `hash`'s). -/
structure PreP (D : Nat) (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 64 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR D s, gR s, pR s, tHR s, tGR s, aR s]
  hwr : s.wr = [scR s]
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ds : (dR D s).Disjoint (scR s)
  gs : (gR s).Disjoint (scR s)
  sp : (scR s).Disjoint (pR s)
  sth : (scR s).Disjoint (tHR s)
  stg : (scR s).Disjoint (tGR s)
  sa : (scR s).Disjoint (aR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR D s)
  kg : (kR s).Disjoint (gR s)
  ksc : (kR s).Disjoint (scR s)
  kp : (kR s).Disjoint (pR s)
  kth : (kR s).Disjoint (tHR s)
  ktg : (kR s).Disjoint (tGR s)
  ka : (kR s).Disjoint (aR s)
  wn : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  we : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  wd : (s.gpr .a4).toNat + D ≤ 2 ^ 64
  wg : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wsc : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  wth : (stackArg s 6).toNat + 88 ≤ 2 ^ 64
  wtg : (stackArg s 7).toNat + 40 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a1).toNat
  k2 : (s.gpr .a1).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .a3).toNat
  e2 : (s.gpr .a3).toNat ≤ (s.gpr .a1).toNat
  gk : (s.gpr .a7).toNat = (s.gpr .a1).toNat
  hs : Spec.RsaPss.publicScratchWords (s.gpr .a1).toNat ≤ (stackArg s 3).toNat
  hp : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .a1).toNat
  al2 : (stackArg s 2).toNat % 8 = 0
  al4 : (stackArg s 4).toNat % 8 = 0
  al6 : (stackArg s 6).toNat % 8 = 0
  al7 : (stackArg s 7).toNat % 8 = 0

/-- The contract, with the hash function one of the tables `tsH` of `MdHash`
and MGF1's one of the tables `tsG` of `Hash`, and the stack of the frame and
of the streaming hash functions. -/
abbrev verSpec (tsH tsG : List FnTable) : Contract isa :=
  Spec.RsaPss.verifyPrecomputedTableContract
    (abi.withTables Spec.RsaPss.verifyPrecomputedTableSig [("hash", tsH), ("mgf1", tsG)]) stackBytes

/-- Unfolds the precondition at `h`. -/
macro "ver_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes = 335 + 1 := rfl
  unfold verSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_eight, List.append_eq, List.range, List.range.loop,
    Spec.Rsa.lenValid] at $h:ident
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_eight, List.append_eq, List.range, List.range.loop,
    Spec.Rsa.lenValid] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- `PreP`, for the hash function `H` that the table at the stack argument 6
names: the digest has its length. -/
theorem preP_of {H : Spec.Mgf1.Hash} {tsH tsG : List FnTable} {s : State} (h : (verSpec tsH tsG).pre s)
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some H) : PreP H.len s := by
  ver_pre at h
  obtain ⟨spal, sp1, sp2, -, -, -, hrd, hwr, ns, es, ds, gs, sp, sth, stg, sa, kn, ke, kd, kg, ksc, kp, kth, ktg,
    ka, wn, we, wd, wg, wsc, wp, wth, wtg, k1, k2, e1, e2, gk, hs, hp, hl, al2, al4, al6, al7⟩ := h
  have hl := hl H hH
  rw [hl] at hrd ds kd wd
  exact ⟨spal, sp1, sp2, hrd, hwr, ns, es, ds, gs, sp, sth, stg, sa, kn, ke, kd, kg, ksc, kp, kth, ktg, ka, wn, we,
    wd, wg, wsc, wp, wth, wtg, k1, k2, e1, e2, gk, hs, hp, al2, al4, al6, al7⟩

/-- The tables, as the contract gives them: the hash function's one of `tsH`
at the stack argument 6 and MGF1's one of `tsG` at 7, with the functions of
distinct names at distinct addresses. -/
theorem spec_tab {tsH tsG : List FnTable} {s : State} (h : (verSpec tsH tsG).pre s) :
    (∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s T)) ∧
      (∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s T)) ∧
      ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  ver_pre at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- The working space. -/
abbrev Sp (s : State) : Addr := stackArg s 2

/-- The modulus' first byte, zero-extended. -/
def n0 (s : State) : BitVec 64 := (s.mem (s.gpr .a0)).setWidth 64

/-- The bits of `n₀ >> 1` smeared down. -/
def smear (s : State) : BitVec 64 :=
  let a := n0 s >>> 1
  let b := a ||| a >>> 1
  let c := b ||| b >>> 2
  c ||| c >>> 4

/-- 1 if `emLen = k - 1`, else 0. -/
def lo (s : State) : BitVec 64 := (smear s - BitVec.ofNat 64 1) >>> 63

/-- The mask of `maskedDB`'s first byte. -/
def cm (s : State) : BitVec 64 := smear s ||| ((BitVec.ofNat 64 0 - lo s) &&& BitVec.ofNat 64 0xFF)

/-- `dbLen = k - lo - hLen - 1`. -/
def dbLen (D : Nat) (s : State) : BitVec 64 := s.gpr .a1 - lo s - BitVec.ofNat 64 (D + 1)

/-- The salt-length mode, zero-extended. -/
def anyL (s : State) : BitVec 64 := stackArg s 1 <<< 32 >>> 32

/-- The values `Base` fixes in `s1`–`s4`: `k`, `digest`, `lo` and `dbLen`. -/
def vP (D : Nat) (s : State) : Reg → BitVec 64
  | .s1 => s.gpr .a1
  | .s2 => s.gpr .a4
  | .s3 => lo s
  | .s4 => dbLen D s
  | _ => 0

/-- `c`, `salt_len` and the salt-length mode in `s5`–`s7`. -/
structure Xs (s t : State) : Prop where
  s5 : t.gpr .s5 = cm s
  s6 : t.gpr .s6 = stackArg s 0
  s7 : t.gpr .s7 = anyL s

theorem Xs.of {s t u : State} (h : Xs s t) (g : ∀ r ∈ [Reg.s5, .s6, .s7], u.gpr r = t.gpr r) : Xs s u :=
  ⟨(g _ (by decide)).trans h.s5, (g _ (by decide)).trans h.s6, (g _ (by decide)).trans h.s7⟩

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem scLen : oRsa ≤ (stackArg s 3).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC Sp s) (scR s) := Region.sub_prefix (scLen P)

theorem scR_contains {o n : Nat} (h : o + n ≤ oRsa) : (scR s).Contains (off (Sp s) o) n :=
  Offset.contains_base _ (by have := scLen P; omega) (by unfold oRsa at h; omega)

theorem PreP.fits : Fits Sp s where
  sp1 := P.sp1
  sp16 := P.spal
  sc := ⟨scR s, by rw [P.hwr]; simp, rfl, scLen P⟩
  ksc := P.ksc.sub_right (sc_sub P)
  wS := by show (stackArg s 2).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {D : Nat} {s t : State} (h : Base Sp (vP D) s t)
include h

theorem _root_.VG.Proof.RsaOaep.RISCV64.Base.pk : t.gpr .s1 = s.gpr .a1 := h.vs .s1 (by decide)
theorem _root_.VG.Proof.RsaOaep.RISCV64.Base.pdig : t.gpr .s2 = s.gpr .a4 := h.vs .s2 (by decide)
theorem _root_.VG.Proof.RsaOaep.RISCV64.Base.plo : t.gpr .s3 = lo s := h.vs .s3 (by decide)
theorem _root_.VG.Proof.RsaOaep.RISCV64.Base.pdb : t.gpr .s4 = dbLen D s := h.vs .s4 (by decide)

end

/-! ## The encoding's parameters -/

/-- `smear`, `lo` and `c` of a byte. -/
def smB (b : Byte) : BitVec 64 :=
  let a := b.setWidth 64 >>> 1
  let b := a ||| a >>> 1
  let c := b ||| b >>> 2
  c ||| c >>> 4

def loB (b : Byte) : BitVec 64 := (smB b - BitVec.ofNat 64 1) >>> 63

def cmB (b : Byte) : BitVec 64 := smB b ||| ((BitVec.ofNat 64 0 - loB b) &&& BitVec.ofNat 64 0xFF)

theorem byte_ok : ∀ n < 256, n ≠ 0 →
    loB (BitVec.ofNat 8 n) = BitVec.ofNat 64 (if n = 1 then 1 else 0) ∧
      cmB (BitVec.ofNat 8 n) = BitVec.ofNat 64 (if n = 1 then 255 else 2 ^ Nat.log2 n - 1) := by
  decide +kernel

theorem lo_byte (s : State) : lo s = loB (s.mem (s.gpr .a0)) := rfl
theorem cm_byte (s : State) : cm s = cmB (s.mem (s.gpr .a0)) := rfl

section
variable {s : State} (h0 : s.mem (s.gpr .a0) ≠ 0)
include h0

theorem byte_ne : (s.mem (s.gpr .a0)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)

theorem lo_eq : lo s = BitVec.ofNat 64 (if (s.mem (s.gpr .a0)).toNat = 1 then 1 else 0) := by
  have := (byte_ok _ (s.mem (s.gpr .a0)).isLt (byte_ne h0)).1
  rw [lo_byte, ← this, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cm_eq : cm s = (if (s.mem (s.gpr .a0)).toNat = 1 then (0xFF : Byte) else
    BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .a0)).toNat - 1)).setWidth 64 := by
  have := (byte_ok _ (s.mem (s.gpr .a0)).isLt (byte_ne h0)).2
  rw [cm_byte, BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
  rw [this]
  split
  · rfl
  · have h8 := Proof.RsaPss.log2_lt8 (s.mem (s.gpr .a0))
    have hp : 2 ^ Nat.log2 (s.mem (s.gpr .a0)).toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have hp1 := Nat.one_le_two_pow (n := Nat.log2 (s.mem (s.gpr .a0)).toNat)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end


/-! ## The shift, as views -/

/-- A pass: the `n` bytes from `b` replaced by those `d` after them if
`bit`. -/
def passV (V : Nat → Byte) (b n : Nat) (bit : Bool) (d : Nat) (o : Nat) : Byte :=
  if b ≤ o ∧ o < b + n then (if bit then V (o + d) else V o) else V o

/-- The first `j` passes by the bits of `a`. -/
def shV (V : Nat → Byte) (b n a : Nat) : Nat → Nat → Byte
  | 0 => V
  | j + 1 => passV (shV V b n a j) b n (a / 2 ^ j % 2 = 1) (2 ^ j)

theorem shV_out (V : Nat → Byte) (b n a : Nat) : ∀ j o, ¬ (b ≤ o ∧ o < b + n) → shV V b n a j o = V o
  | 0, _, _ => rfl
  | j + 1, o, h => by rw [shV, passV, ifn h, shV_out V b n a j o h]

theorem shV_in (V : Nat → Byte) (b n a : Nat) (hz : ∀ x, n ≤ x → x < n + 2 ^ 9 → V (b + x) = 0) :
    ∀ j ≤ 10, ∀ i < n, shV V b n a j (b + i) = if i + a % 2 ^ j < n then V (b + (i + a % 2 ^ j)) else 0
  | 0, _, i, hi => by simp only [shV, Nat.pow_zero, Nat.mod_one, Nat.add_zero]; rw [ifp hi]
  | j + 1, hj, i, hi => by
    have ih := shV_in V b n a hz j (by omega)
    have hm : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * (a / 2 ^ j % 2) := Nat.mod_pow_succ
    have h2 := Nat.mod_lt (a / 2 ^ j) (show 0 < 2 by decide)
    have hp : 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
    have hp10 : (2 : Nat) ^ 10 = 1024 := rfl
    have hp9 : (2 : Nat) ^ 9 = 512 := rfl
    have hmj := Nat.mod_lt a (Nat.two_pow_pos j)
    rw [shV, passV, ifp ⟨by omega, by omega⟩]
    by_cases hb : a / 2 ^ j % 2 = 1
    · rw [ifp (decide_eq_true hb), show b + i + 2 ^ j = b + (i + 2 ^ j) by omega]
      rw [hb, Nat.mul_one] at hm
      rw [hm]
      by_cases hl : i + 2 ^ j < n
      · rw [ih (i + 2 ^ j) hl, show i + 2 ^ j + a % 2 ^ j = i + (a % 2 ^ j + 2 ^ j) by omega]
      · rw [shV_out V b n a j _ (by omega), hz _ (by omega) (by omega), ifn (by omega)]
    · have hb0 : a / 2 ^ j % 2 = 0 := by omega
      rw [ifn (by simpa using hb), hm, hb0, Nat.mul_zero, Nat.add_zero, ih i hi]

/-- Ten passes shift the `n` bytes left by `a`. -/
theorem shV_eq (V : Nat → Byte) {b n a : Nat} (ha : a < 2 ^ 10)
    (hz : ∀ x, n ≤ x → x < n + 2 ^ 9 → V (b + x) = 0) {i : Nat} (hi : i < n) :
    shV V b n a 10 (b + i) = if i + a < n then V (b + (i + a)) else 0 := by
  rw [shV_in V b n a hz 10 (Nat.le_refl _) i hi, Nat.mod_eq_of_lt ha]



/-! ## The entry -/

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 8) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- After the saves and the prologue. -/
structure Entered (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  xs : Xs s t
  s8 : t.gpr .s8 = s.gpr .a2
  s9 : t.gpr .s9 = s.gpr .a3
  s10 : t.gpr .s10 = s.gpr .a6
  t1 : t.gpr .t1 = n0 s

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem arg_al {j : Nat} (hj : j < 8) : (stackArgAddr s j).toNat % 8 = 0 := by
  have := P.spal; have := P.sp2
  have e : (stackArgAddr s j).toNat = s.sp.toNat + 8 * j := by
    simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; omega

theorem fb_al8 : (fb s).toNat % 8 = 0 := by
  have := fb_al (PreP.fits P); omega

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
with memory changed only in the stack and our part of the working space. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 8)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kR s, SC Sp s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.ka.symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

theorem entry_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) (hD64 : D ≤ 64) :
    WP isa (.block (save ++ Impl.RsaPss.RISCV64.prologue H)) (allocd frameBytes s) (Entered D s) := by
  refine save_ok (u := allocd frameBytes s) rfl rfl (fb_al8 P) (Frame.refl _ _) (fun r _ => rfl)
    fun v kv h0 hm hsv => ?_
  have hrd : v.rd = s.rd := kv.rd
  have hsp : v.sp = fb s := kv.sp
  have hm2 : Frame [kR s, SC Sp s] s.mem v.mem := hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  have gs : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a6], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide)]; rfl
  simp only [Impl.RsaPss.RISCV64.prologue, Impl.RsaOaep.RISCV64.argBase]
  refine wp_addSp fun v₁ o₁ e₁ => ?_
  have g6 : v₁.gpr .t6 = s.sp := by rw [e₁, hsp, BitVec.sub_add_cancel]
  refine wp_arg P (j := 1) (by decide) g6 (o₁.rd.trans hrd) (by rw [o₁.mem]; exact hm2) fun v₂ o₂ e₂ => ?_
  refine wp_sll fun v₃ o₃ e₃ => wp_srl fun v₄ o₄ e₄ => ?_
  refine wp_arg P (j := 2) (by decide) (by rw [o₄.get .t6, o₃.get .t6, o₂.get .t6, g6])
    (by rw [o₄.rd, o₃.rd, o₂.rd, o₁.rd, hrd]) (by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact hm2)
    fun v₅ o₅ e₅ => ?_
  refine wp_mov fun v₆ o₆ e₆ => wp_mov fun v₇ o₇ e₇ => ?_
  refine wp_arg P (j := 0) (by decide)
    (by rw [o₇.get .t6, o₆.get .t6, o₅.get .t6, o₄.get .t6, o₃.get .t6, o₂.get .t6, g6])
    (by rw [o₇.rd, o₆.rd, o₅.rd, o₄.rd, o₃.rd, o₂.rd, o₁.rd, hrd])
    (by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact hm2) fun v₈ o₈ e₈ => ?_
  refine wp_mov fun v₉ o₉ e₉ => wp_mov fun v₁₀ o₁₀ e₁₀ => wp_mov fun v₁₁ o₁₁ e₁₁ => ?_
  have k₁₁ : Only [.t6, .s7, .s0, .s1, .s2, .s6, .s8, .s9, .s10] v v₁₁ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans
      o₁₁)))))))))).mono
  have hn : nR s ∈ s.rd := by rw [P.hrd]; simp
  have hc : (nR s).Contains (s.gpr .a0) 1 := by
    have := Offset.contains_base (s.gpr .a0) (d := 0) (n := 1) (k := (s.gpr .a1).toNat) (by have := P.k1; omega)
      (by have := P.wn; omega)
    simpa only [BitVec.add_zero] using this
  refine wp_lbu (a := s.gpr .a0) (by rw [k₁₁.get .a0, gs .a0 (by decide), BitVec.add_zero])
    (by rw [k₁₁.rd, hrd]; exact ⟨nR s, List.mem_append_left _ hn, hc⟩) fun v₁₂ o₁₂ e₁₂ => ?_
  refine wp_srl fun v₁₃ o₁₃ e₁₃ => wp_srl fun v₁₄ o₁₄ e₁₄ => wp_or fun v₁₅ o₁₅ e₁₅ => wp_srl fun v₁₆ o₁₆ e₁₆ =>
    wp_or fun v₁₇ o₁₇ e₁₇ => wp_srl fun v₁₈ o₁₈ e₁₈ => wp_or fun v₁₉ o₁₉ e₁₉ =>
    wp_subi (imm := 1) fun v₂₀ o₂₀ e₂₀ => wp_srl fun v₂₁ o₂₁ e₂₁ => wp_li (imm := 0) (by decide) fun v₂₂ o₂₂ e₂₂ =>
    wp_sub fun v₂₃ o₂₃ e₂₃ => wp_li (imm := 255) (by decide) fun v₂₄ o₂₄ e₂₄ => wp_and fun v₂₅ o₂₅ e₂₅ =>
    wp_or fun v₂₆ o₂₆ e₂₆ => wp_sub fun v₂₇ o₂₇ e₂₇ => wp_subi (imm := H.D + 1) (h := by omega)
    fun w ow ew => wp_nil ?_
  have kw : Only [.t1, .t2, .t3, .s3, .t4, .s5, .s4] v₁₁ w :=
    (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans (o₂₀.trans (o₂₁.trans
      (o₂₂.trans (o₂₃.trans (o₂₄.trans (o₂₅.trans (o₂₆.trans (o₂₇.trans ow)))))))))))))))).mono
  -- The byte, and what it gives.
  have hb : v₁₂.gpr .t1 = n0 s := by
    rw [e₁₂, k₁₁.mem]
    show (v.mem (s.gpr .a0)).setWidth 64 = (s.mem (s.gpr .a0)).setWidth 64
    rw [hm _ fun r hr hx => by
      rw [List.mem_singleton.mp hr] at hx; exact P.kn _ hx hc]
  -- The registers at `v₁₁`.
  have a11 : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a6], v₁₁.gpr r = s.gpr r := fun r hr => by
    rw [k₁₁.gpr r (by revert r; decide), gs r hr]
  have g0 : v₁₁.gpr .s0 = Sp s := by
    rw [o₁₁.get .s0, o₁₀.get .s0, o₉.get .s0, o₈.get .s0, o₇.get .s0, o₆.get .s0, e₅]
  have g1 : v₁₁.gpr .s1 = s.gpr .a1 := by
    rw [o₁₁.get .s1, o₁₀.get .s1, o₉.get .s1, o₈.get .s1, o₇.get .s1, e₆, ← a11 .a1 (by decide), o₁₁.get .a1,
      o₁₀.get .a1, o₉.get .a1, o₈.get .a1, o₇.get .a1, o₆.get .a1]
  have g2 : v₁₁.gpr .s2 = s.gpr .a4 := by
    rw [o₁₁.get .s2, o₁₀.get .s2, o₉.get .s2, o₈.get .s2, e₇, ← a11 .a4 (by decide), o₁₁.get .a4,
      o₁₀.get .a4, o₉.get .a4, o₈.get .a4, o₇.get .a4]
  have g6 : v₁₁.gpr .s6 = stackArg s 0 := by
    rw [o₁₁.get .s6, o₁₀.get .s6, o₉.get .s6, e₈]
  have g8 : v₁₁.gpr .s8 = s.gpr .a2 := by
    rw [o₁₁.get .s8, o₁₀.get .s8, e₉, ← a11 .a2 (by decide), o₁₁.get .a2, o₁₀.get .a2, o₉.get .a2]
  have g9 : v₁₁.gpr .s9 = s.gpr .a3 := by
    rw [o₁₁.get .s9, e₁₀, ← a11 .a3 (by decide), o₁₁.get .a3, o₁₀.get .a3]
  have g10 : v₁₁.gpr .s10 = s.gpr .a6 := by rw [e₁₁, ← a11 .a6 (by decide), o₁₁.get .a6]
  have g7 : v₁₁.gpr .s7 = anyL s := by
    rw [o₁₁.get .s7, o₁₀.get .s7, o₉.get .s7, o₈.get .s7, o₇.get .s7, o₆.get .s7, o₅.get .s7, e₄, e₃, e₂]; rfl
  -- The parameters.
  have m19 : v₁₉.gpr .t2 = smear s := by
    rw [e₁₉, o₁₈.get .t2, e₁₈, e₁₇, o₁₆.get .t2, e₁₆, e₁₅, o₁₄.get .t2, e₁₄, e₁₃, hb]; rfl
  have m21 : v₂₁.gpr .s3 = lo s := by rw [e₂₁, e₂₀, m19]; rfl
  have k1925 : Only [.t3, .s3, .t4] v₁₉ v₂₅ := (o₂₀.trans (o₂₁.trans (o₂₂.trans (o₂₃.trans (o₂₄.trans
    o₂₅))))).mono
  have m26 : v₂₆.gpr .s5 = cm s := by
    rw [e₂₆, e₂₅, k1925.get .t2, m19, o₂₄.get .t3, e₂₄, e₂₃, e₂₂, o₂₂.get .s3, m21]; rfl
  have k2126 : Only [.t3, .t4, .s5] v₂₁ v₂₆ := (o₂₂.trans (o₂₃.trans (o₂₄.trans (o₂₅.trans o₂₆)))).mono
  have k1121 : Only [.t1, .t2, .t3, .s3] v₁₁ v₂₁ := (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans
    (o₁₇.trans (o₁₈.trans (o₁₉.trans (o₂₀.trans o₂₁))))))))).mono
  have m27 : w.gpr .s4 = dbLen D s := by
    rw [ew, e₂₇, k2126.get .s1, k1121.get .s1, g1, k2126.get .s3, m21, hD]; rfl
  have k2127 : Only [.t3, .t4, .s5, .s4] v₂₁ w := (k2126.trans (o₂₇.trans ow)).mono
  have k1219 : Only [.t2, .t3, .s3, .t4, .s5, .s4] v₁₂ w :=
    (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans (o₂₀.trans (o₂₁.trans
      (o₂₂.trans (o₂₃.trans (o₂₄.trans (o₂₅.trans (o₂₆.trans (o₂₇.trans ow))))))))))))))).mono
  have sv : Saves s w := ⟨by rw [kw.sp, k₁₁.sp, hsp], by rw [kw.wr, k₁₁.wr, kv.wr]; rfl,
    by rw [kw.mem, k₁₁.mem]; exact hsv⟩
  refine ⟨⟨sv, by rw [kw.rd, k₁₁.rd, hrd], by rw [kw.get .s0, g0], fun r hr => ?_, ?_⟩,
    ⟨by rw [o₂₇.get .s5 |> fun _ => (o₂₇.trans ow).get .s5, m26], by rw [kw.get .s6, g6], by rw [kw.get .s7, g7]⟩,
    by rw [kw.get .s8, g8], by rw [kw.get .s9, g9], by rw [kw.get .s10, g10], by rw [k1219.get .t1, hb]⟩
  · simp only [Proof.RsaOaep.RISCV64.fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [vP]
    · rw [kw.get .s1, g1]
    · rw [kw.get .s2, g2]
    · rw [k2127.get .s3, m21]
    · exact m27
  · rw [kw.mem, k₁₁.mem]; exact hm2

end

end VG.Proof.RsaPss.RISCV64
