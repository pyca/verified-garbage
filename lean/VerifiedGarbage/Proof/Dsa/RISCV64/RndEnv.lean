module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Random
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.RISCV64.RndMath
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA sampling on RISC-V: the sampler's state

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Env.lean` and `Q.lean`). `SE`:
what the sampler works with, all public: the frame's stack pointer `F` (the
nonce at `F + oNonce`), the tape (`rl` octets at `rand`), q's significant
octets (`W` of them at `qp`, `qs`), `p_len` and `q_len` (in `s2`) and the
mask `M` of the first one's bits. `SEnv E R s`: the registers hold them,
the nonce is writable, the tape and q readable, and memory holds the tape
`R` and `qs`. A change of memory in the nonce only keeps `SEnv`
(`SEnv.step`). `SE.Q`: `E` is the data of q's octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa (significant qSigOf)

/-- A run keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp :=
  let ⟨tr, t, e, q⟩ := h
  ⟨tr, t, e, q, Exec.sp e⟩

/-- The lengths in `s2`. -/
abbrev lens (pl ql : Nat) : BitVec 64 := BitVec.ofNat 64 (pl + 65536 * ql)

theorem lenQ_eq {pl ql : Nat} (hp : pl < 65536) (hq : ql < 65536) :
    lens pl ql >>> 16 = BitVec.ofNat 64 ql := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show pl + 65536 * ql < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show ql < 2 ^ 64 by omega)]
  omega

theorem lenP_eq {pl ql : Nat} (hp : pl < 65536) (hq : ql < 65536) :
    lens pl ql <<< 48 >>> 48 = BitVec.ofNat 64 pl := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show pl + 65536 * ql < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show pl < 2 ^ 64 by omega)]
  simp only [Nat.reducePow]
  omega

/-- The sampler's public data. -/
structure SE where
  F : Addr
  rand : Addr
  rl : Nat
  qp : Addr
  pl : Nat
  ql : Nat
  W : Nat
  M : Nat
  qs : List Byte

/-- The nonce. -/
abbrev SE.N (E : SE) : Addr := off E.F oNonce

/-- The nonce's region. -/
abbrev SE.NR (E : SE) : Region := ⟨E.N, 32⟩

structure SE.Ok (E : SE) : Prop where
  pl : E.pl < 65536
  ql : E.ql ≤ 32
  W1 : 1 ≤ E.W
  Wq : E.W ≤ E.ql
  M : E.M < 256
  qs : E.qs.length = E.W
  rnw : E.rand.toNat + E.rl ≤ 2 ^ 64
  rl : E.rl < 2 ^ 64
  qnw : E.qp.toNat + E.W ≤ 2 ^ 64
  fnw : E.F.toNat + frameBytes ≤ 2 ^ 64
  fal : E.F.toNat % 8 = 0
  dR : (⟨E.rand, E.rl⟩ : Region).Disjoint E.NR
  dQ : (⟨E.qp, E.W⟩ : Region).Disjoint E.NR

/-- A state of the sampler, with the tape `R`. -/
structure SEnv (E : SE) (R : List Byte) (s : State) : Prop where
  sp : s.sp = E.F
  s2 : s.gpr .s2 = lens E.pl E.ql
  s3 : s.gpr .s3 = E.rand
  s4 : s.gpr .s4 = BitVec.ofNat 64 E.rl
  s7 : s.gpr .s7 = E.qp
  s8 : s.gpr .s8 = BitVec.ofNat 64 E.W
  s9 : s.gpr .s9 = BitVec.ofNat 64 E.M
  nw : Scr s E.N 32
  rr : ∀ i < E.rl, InRegions (s.rd ++ s.wr) (off E.rand i) 1
  qr : ∀ i < E.W, InRegions (s.rd ++ s.wr) (off E.qp i) 1
  R : Spec.Rsa.bytesAt s.mem E.rand E.rl = R
  Q : Spec.Rsa.bytesAt s.mem E.qp E.W = E.qs

/-- The registers `SEnv` fixes. -/
def envRegs : List Reg := [.s2, .s3, .s4, .s7, .s8, .s9]

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
  rw [show 2 ^ 64 - 32 + (x - E.F).toNat = (x - E.F).toNat - 32 + 2 ^ 64 by omega, Nat.add_mod_right,
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

/-- `SEnv` after code that keeps its registers and the stack pointer and
changes memory in the nonce only. -/
theorem SEnv.step {E : SE} {R : List Byte} {s t : State} {rs : List Reg} (hE : E.Ok) (h : SEnv E R s)
    (k : Keep rs s t) (hsp : t.sp = s.sp) {o n : Nat} (hon : o + n ≤ 32)
    (ho : Outside E.F (oNonce + o) n s.mem t.mem)
    (hr : ∀ r ∈ envRegs, r ∉ rs := by decide) : SEnv E R t where
  sp := hsp.trans h.sp
  s2 := (k.gpr (hr _ (by decide))).trans h.s2
  s3 := (k.gpr (hr _ (by decide))).trans h.s3
  s4 := (k.gpr (hr _ (by decide))).trans h.s4
  s7 := (k.gpr (hr _ (by decide))).trans h.s7
  s8 := (k.gpr (hr _ (by decide))).trans h.s8
  s9 := (k.gpr (hr _ (by decide))).trans h.s9
  nw := h.nw.congr k.2.2
  rr := by rw [k.2.1, k.2.2]; exact h.rr
  qr := by rw [k.2.1, k.2.2]; exact h.qr
  R := (bytes_kept hE hE.dR hE.rnw hon ho).trans h.R
  Q := (bytes_kept hE hE.dQ hE.qnw hon ho).trans h.Q

/-- `SEnv` after code that keeps its registers, the stack pointer and memory. -/
theorem SEnv.stepM {E : SE} {R : List Byte} {s t : State} {rs : List Reg} (hE : E.Ok) (h : SEnv E R s)
    (k : Keep rs s t) (hsp : t.sp = s.sp) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ envRegs, r ∉ rs := by decide) : SEnv E R t :=
  h.step hE k hsp (o := 0) (n := 0) (by omega) (by rw [hm]; exact Outside.refl _ _ _ _) hr

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

theorem SEnv.lenQ {E : SE} {R : List Byte} {s : State} (hE : E.Ok) (h : SEnv E R s) :
    s.gpr .s2 >>> 16 = BitVec.ofNat 64 E.ql := by
  rw [h.s2]; exact lenQ_eq hE.pl (by have := hE.ql; omega)

/-! ## The data of q -/

/-- The draw's octet `j` as the nonce gets it: the first masked. -/
def cpy (bs : List Byte) (M : Nat) (j : Nat) : Byte :=
  if j = 0 then bs.getD 0 0 &&& BitVec.ofNat 8 M else bs.getD j 0

/-- The frame's offset of the draw in the nonce. -/
abbrev SE.o (E : SE) : Nat := oNonce + (E.ql - E.W)

/-- `E` is the sampler's data for q's octets `qb`, and `q > 1`. -/
structure SE.Q (E : SE) (qb : List Byte) : Prop where
  len : qb.length = E.ql
  W : E.W = (significant qb).1
  M : E.M = maskOf (significant qb).2.toNat
  qs : E.qs = qSigOf qb
  gt : 1 < Spec.Dsa.decodeBE qb

theorem SE.Q.draw {E : SE} {qb : List Byte} (h : E.Q qb) :
    Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE qb) = E.W := by
  rw [Dsa.random_drawBytes_scan, h.W]

theorem SE.Q.qs_val {E : SE} {qb : List Byte} (h : E.Q qb) :
    Spec.Dsa.decodeBE E.qs = Spec.Dsa.decodeBE qb := by
  rw [h.qs, qSigOf, Dsa.random_significant_drop]

theorem SE.Q.W_pos {E : SE} {qb : List Byte} (h : E.Q qb) : 0 < E.W := by
  have := (Dsa.random_valid_scan qb).mp h.gt
  rw [h.W]; omega

/-- The draw as the nonce gets it. -/
abbrev cpyList (bs : List Byte) (M W : Nat) : List Byte := (List.range W).map (cpy bs M)

theorem cpyList_take (bs : List Byte) (M W : Nat) : cpyList (bs.take W) M W = cpyList bs M W := by
  simp only [cpyList, List.map_inj_left, List.mem_range]
  intro j hj
  simp only [cpy, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj]
  split
  · rename_i h0; subst h0; rw [ite_eq_left hj]
  · rfl

theorem cpyList_cons (b : Byte) (bs : List Byte) (M : Nat) :
    cpyList (b :: bs) M (bs.length + 1) = (b &&& BitVec.ofNat 8 M) :: bs := by
  apply List.ext_getElem
  · simp [cpyList]
  · intro i h₁ h₂
    simp only [cpyList, List.getElem_map, List.getElem_range, cpy]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.add_one_ne_zero, ite_false, List.getElem_cons_succ]
      simp only [List.length_cons] at h₂
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < bs.length by omega)]

/-- The copied draw decodes to the candidate. -/
theorem SE.Q.cand {E : SE} {qb : List Byte} (h : E.Q qb) {bs : List Byte} (hl : E.W ≤ bs.length) :
    Spec.Dsa.decodeBE (cpyList bs E.M E.W) = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qb) (bs.take E.W) := by
  have hW := h.W_pos
  rw [← cpyList_take]
  obtain ⟨b, rest, he⟩ : ∃ b rest, bs.take E.W = b :: rest := by
    cases hc : bs.take E.W with
    | nil =>
      have := congrArg List.length hc
      rw [List.length_take, Nat.min_eq_left hl, List.length_nil] at this; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hrl : rest.length + 1 = E.W := by
    have := congrArg List.length he
    rw [List.length_take, List.length_cons, Nat.min_eq_left hl] at this; omega
  rw [he, ← hrl, cpyList_cons, Dsa.random_candidate_mask qb b rest (by rw [hrl, h.W]), h.M]

end VG.Proof.Dsa.RISCV64.Rnd
