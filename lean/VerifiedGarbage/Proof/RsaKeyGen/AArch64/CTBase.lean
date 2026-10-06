import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KMain
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase

/-!
# A candidate on AArch64: constant time, the public data and the stages

The taint analysis knows only registers, so every public value the code
loads from the header is pinned by correctness (`pin_ct`, `ws_ct`): the
stages are related by what correctness says about two runs with the same
public data `q : FPub` (the layout, the arguments, `e`'s octets, `p`'s and
`rand`'s lengths, and the schedule `q.sch` the leak fixes). `K0 q`: before
`loadC`; `KSt q`: between the stages, with the candidate in `aN`; `TS q`:
before `montSetup`, when the schedule goes on to Miller–Rabin.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.RsaKeyGen (Sched schedOf)
open VG.Impl.Bignum.Public (aN)

/-- What the stages may depend on: the layout, the arguments, `e`'s octets,
`p`'s and `rand`'s lengths, and the schedule. -/
structure FPub where
  B : Addr
  Z : Nat
  w : Nat
  wr : List Region
  op : Addr
  up : Addr
  eP : Addr
  eB : List Byte
  pP : Addr
  pl : Nat
  rP : Addr
  rl : Nat
  sch : Sched

/-- The public bounds. -/
structure FDims (q : FPub) : Prop where
  z : 1024 * q.w ≤ q.Z
  w4 : 4 ≤ q.w
  w64 : q.w ≤ 64
  rl : q.rl < 2 ^ 64
  rk : 8 * q.w ≤ q.rl
  el1 : 1 ≤ q.eB.length
  el8 : q.eB.length ≤ 8
  pl : q.pl = 0 ∨ q.pl = 8 * q.w

/-- The header words the stages keep: the arguments, `used` and the mask. -/
structure KHdr (m : Mem) (q : FPub) : Prop where
  out : word m q.B (8 * kOut) = q.op
  len : word m q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w)
  usedP : word m q.B (8 * kUsedP) = q.up
  e : word m q.B (8 * kE) = q.eP
  elen : word m q.B (8 * kElen) = BitVec.ofNat 64 q.eB.length
  p : word m q.B (8 * kP) = q.pP
  plen : word m q.B (8 * kPlen) = BitVec.ofNat 64 q.pl
  rand : word m q.B (8 * kRand) = q.rP
  rlen : word m q.B (8 * kRandLen) = BitVec.ofNat 64 q.rl
  used : word m q.B (8 * kUsed) = BitVec.ofNat 64 (8 * q.w)
  mask : word m q.B (8 * Public.sMask) = mask true

/-- `KHdr` survives changes past the header words it keeps: in the arrays,
in the first 16 header words, or in `kT0` (word 26). -/
theorem KHdr.frm {m m' : Mem} {q : FPub} (h : KHdr m q) {rs : List (Nat × Nat)} (hf : Frm q.B rs m m')
    (hd : ∀ r ∈ rs, 8 * 28 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 16 ∨ r = (8 * 26, 8)) :
    KHdr m' q := by
  have k : ∀ {i : Nat}, 16 ≤ i → i < 28 → i ≠ 26 → word m' q.B (8 * i) = word m q.B (8 * i) := fun h1 h2 h3 =>
    hf.word_eq (fun r hr => by
      rcases hd r hr with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
      · subst h; dsimp only; omega) (by omega)
  exact ⟨(k (by decide) (by decide) (by decide)).trans h.out, (k (by decide) (by decide) (by decide)).trans h.len,
    (k (by decide) (by decide) (by decide)).trans h.usedP, (k (by decide) (by decide) (by decide)).trans h.e,
    (k (by decide) (by decide) (by decide)).trans h.elen, (k (by decide) (by decide) (by decide)).trans h.p,
    (k (by decide) (by decide) (by decide)).trans h.plen, (k (by decide) (by decide) (by decide)).trans h.rand,
    (k (by decide) (by decide) (by decide)).trans h.rlen, (k (by decide) (by decide) (by decide)).trans h.used,
    (k (by decide) (by decide) (by decide)).trans h.mask⟩

/-- Between the stages: the working space, the header words, the candidate
in `aN`, `out` and `used`, the buffers, and the schedule. -/
def KSt (q : FPub) (s : State) : Prop :=
  s.wr = q.wr ∧ FDims q ∧ Ws s q.B q.Z q.w ∧ KHdr s.mem q ∧ OutUp s q.B q.Z q.op q.up (8 * q.w) ∧
    ∃ pB r : List Byte,
      wv s.mem q.B (slot q.w aN) q.w = Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w))) ∧
      Src s q.B q.Z q.pP pB ∧ Src s q.B q.Z q.eP q.eB ∧ Src s q.B q.Z q.rP r ∧ pB.length = q.pl ∧
      r.length = q.rl ∧ schedOf (8 * q.w) (Spec.Rsa.os2ip q.eB) (Spec.RsaKeyGen.otherPrime pB) r = q.sch

theorem KSt.ws {q : FPub} {s : State} (h : KSt q s) : Ws s q.B q.Z q.w := h.2.2.1

theorem KSt.hdr {q : FPub} {s : State} (h : KSt q s) : KHdr s.mem q := h.2.2.2.1

theorem KSt.dims {q : FPub} {s : State} (h : KSt q s) : FDims q := h.2.1

/-- `KSt` survives a stage that keeps the working space and changes only
memory in it, past the header words it keeps and away from `aN`. -/
theorem KSt.step {q : FPub} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg} (h : KSt q s)
    (hws : Ws t q.B q.Z q.w) (hf : Frm q.B rs s.mem t.mem)
    (hd : ∀ r ∈ rs, 8 * 28 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 16 ∨ r = (8 * 26, 8))
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ q.Z) (hN : ∀ r ∈ rs, slot q.w aN + 8 * q.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.w aN)
    (k : Keep regs s t) : KSt q t := by
  obtain ⟨hw, hdm, h₀, hh, ho, pB, r, hc, hp, he, hr, hpl, hrl, hS⟩ := h
  have hn := h₀.scr.nowrap
  have h256 := h₀.h256
  have sN := h₀.sl (show aN < 16 by decide)
  have hin := InScr.of_frm hf hZ
  refine ⟨k.wr.trans hw, hdm, hws, hh.frm hf hd, ho.congr k.wr, pB, r, ?_, hp.congrK hin k,
    he.congrK hin k, hr.congrK hin k, hpl, hrl, hS⟩
  rw [hf.wv_eq hN (by omega)]; exact hc

/-- Before `montSetup`: the schedule goes on to Miller–Rabin. -/
def TS (q : FPub) (s : State) : Prop :=
  KSt q s ∧ q.sch.close = false ∧ q.sch.comp = false ∧ q.sch.gbad = false

/-- Before `loadC`: what `kMain` needs, for the public data `q`. -/
def K0 (q : FPub) (s : State) : Prop :=
  s.wr = q.wr ∧ FDims q ∧ ∃ pB r : List Byte,
    MainCtx s q.B q.Z q.w q.op q.up q.eP q.pP q.rP q.eB pB r ∧ pB.length = q.pl ∧ r.length = q.rl ∧
    schedOf (8 * q.w) (Spec.Rsa.os2ip q.eB) (Spec.RsaKeyGen.otherPrime pB) r = q.sch

end VG.Proof.RsaKeyGen.AArch64
