module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Random
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA sampling on PPC64LE: the sampler's state

`SE`: what the sampler works with, all public: the frame's stack pointer
`F` (the nonce at `F + oNonce`), the tape (`rl` octets at `rand`), q's
significant octets (`W` of them at `qp`, `qs`), `q_len` and the mask `M` of
the first one's bits. `SEnv E R s`: the registers hold them, the nonce is
writable, the tape and q readable, and memory holds the tape `R` and `qs`.
A change of memory in the nonce only keeps `SEnv` (`SEnv.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- The sampler's public data. -/
structure SE where
  F : Addr
  rand : Addr
  rl : Nat
  qp : Addr
  ql : Nat
  W : Nat
  M : Nat
  qs : List Byte

/-- The nonce. -/
abbrev SE.N (E : SE) : Addr := off E.F oNonce

/-- The nonce's region. -/
abbrev SE.NR (E : SE) : Region := ⟨E.N, 32⟩

structure SE.Ok (E : SE) : Prop where
  ql : E.ql ≤ 32
  W1 : 1 ≤ E.W
  Wq : E.W ≤ E.ql
  M : E.M < 256
  qs : E.qs.length = E.W
  rnw : E.rand.toNat + E.rl ≤ 2 ^ 64
  rl : E.rl < 2 ^ 64
  qnw : E.qp.toNat + E.W ≤ 2 ^ 64
  fnw : E.F.toNat + frameBytes ≤ 2 ^ 64
  dR : (⟨E.rand, E.rl⟩ : Region).Disjoint E.NR
  dQ : (⟨E.qp, E.W⟩ : Region).Disjoint E.NR

/-- A state of the sampler, with the tape `R`. -/
structure SEnv (E : SE) (R : List Byte) (s : State) : Prop where
  sp : s.sp = E.F
  r21 : s.gpr .r21 = BitVec.ofNat 64 E.ql
  r23 : s.gpr .r23 = E.rand
  r24 : s.gpr .r24 = BitVec.ofNat 64 E.rl
  r27 : s.gpr .r27 = E.qp
  r28 : s.gpr .r28 = BitVec.ofNat 64 E.W
  r29 : s.gpr .r29 = BitVec.ofNat 64 E.M
  nw : Scr s E.N 32
  rr : ∀ i < E.rl, InRegions (s.rd ++ s.wr) (off E.rand i) 1
  qr : ∀ i < E.W, InRegions (s.rd ++ s.wr) (off E.qp i) 1
  R : Spec.Rsa.bytesAt s.mem E.rand E.rl = R
  Q : Spec.Rsa.bytesAt s.mem E.qp E.W = E.qs

theorem exec_addSp {s : State} {d : Reg} {imm : Nat} (h : imm < 2 ^ 15) :
    exec (.addSp d imm) s = some (s.write d (s.sp + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true]

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The registers `SEnv` fixes. -/
def envRegs : List Reg := [.r21, .r23, .r24, .r27, .r28, .r29]

/-- An address of a region apart from the nonce is not in the frame's
octets `[oNonce + o, oNonce + o + n)` within the nonce. -/
theorem outside_of_disj {E : SE} (hE : E.Ok) {r : Region} (hd : r.Disjoint E.NR) {x : Addr}
    (hx : r.Contains x 1) {o n : Nat} (hon : o + n ≤ 32) :
    ofs E.F x < oNonce + o ∨ oNonce + o + n ≤ ofs E.F x := by
  have hf := hE.fnw
  by_contra hc
  apply hd x hx
  simp only [Region.Contains, SE.N, off]
  rw [VG.Offset.toNat_sub_add x E.F (by simp only [oNonce]; omega)]
  simp only [ofs, oNonce, frameBytes] at hc hf ⊢
  rw [show 2 ^ 64 - 120 + (x - E.F).toNat = (x - E.F).toNat - 120 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The octets of a region apart from the nonce are kept by a change in it. -/
theorem bytes_kept {E : SE} (hE : E.Ok) {A : Addr} {k : Nat} (hd : (⟨A, k⟩ : Region).Disjoint E.NR)
    (hnw : A.toNat + k ≤ 2 ^ 64) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside E.F (oNonce + o) n m m') : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (outside_of_disj hE hd ?_ hon)
  exact VG.Offset.contains_base A (by omega) (by omega)

/-- `SEnv` after code that keeps its registers and changes memory in the nonce only. -/
theorem SEnv.step {E : SE} {R : List Byte} {s t : State} {rs : List Reg} (hE : E.Ok) (h : SEnv E R s)
    (k : Keep rs s t) {o n : Nat} (hon : o + n ≤ 32) (ho : Outside E.F (oNonce + o) n s.mem t.mem)
    (hr : ∀ r ∈ envRegs, r ∉ rs := by decide) : SEnv E R t where
  sp := k.sp.trans h.sp
  r21 := (k.gpr _ (hr _ (by decide))).trans h.r21
  r23 := (k.gpr _ (hr _ (by decide))).trans h.r23
  r24 := (k.gpr _ (hr _ (by decide))).trans h.r24
  r27 := (k.gpr _ (hr _ (by decide))).trans h.r27
  r28 := (k.gpr _ (hr _ (by decide))).trans h.r28
  r29 := (k.gpr _ (hr _ (by decide))).trans h.r29
  nw := h.nw.congr k.wr
  rr := by rw [k.rd, k.wr]; exact h.rr
  qr := by rw [k.rd, k.wr]; exact h.qr
  R := (bytes_kept hE hE.dR hE.rnw hon ho).trans h.R
  Q := (bytes_kept hE hE.dQ hE.qnw hon ho).trans h.Q

/-- The tape's octet `i`. -/
theorem SEnv.byte {E : SE} {R : List Byte} {s : State} (h : SEnv E R s) {i : Nat} (hi : i < E.rl) :
    s.mem (off E.rand i) = R.getD i 0 := by
  rw [← h.R]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

/-- q's significant octet `i`. -/
theorem SEnv.qbyte {E : SE} {R : List Byte} {s : State} (h : SEnv E R s) {i : Nat} (hi : i < E.W) :
    s.mem (off E.qp i) = E.qs.getD i 0 := by
  rw [← h.Q]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem SEnv.R_length {E : SE} {R : List Byte} {s : State} (h : SEnv E R s) : R.length = E.rl := by
  rw [← h.R, VG.Proof.Bignum.bytesAt_length]

end VG.Proof.Dsa.PPC64LE.Rnd
