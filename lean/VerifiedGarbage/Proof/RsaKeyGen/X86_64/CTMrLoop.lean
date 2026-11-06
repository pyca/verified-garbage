module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# A candidate on x86-64: constant time of Miller–Rabin's loop

The loop over the witnesses, for runs that agree on the public data and on
the shape of the test's result (`shapeOf`: what became of the candidate, and
how many octets of `rand` were left). The shape fixes how many iterations
remain from each offset (`itersOf`), and whether each witness passes
(`passS`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (shapeOf itersOf passS)

/-- Whether `rand` has the next witness. -/
theorem availCmp_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {rl u : Nat} (hrl : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 rl)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hul : u ≤ rl) (hrl' : rl < 2 ^ 64) (hw : 8 * w < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
      .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)]) s fun t =>
      t.cf = some (decide (rl < u + 8 * w)) ∧ t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  have hnw := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have e1 : BitVec.ofNat 64 rl - BitVec.ofNat 64 u = BitVec.ofNat 64 (rl - u) := ofNat_sub_ofNat' hul hrl'
  have e2 : rl - u < 2 ^ 64 := by omega_using [hrl']
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.cf = some (decide (rl < u + 8 * w)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kUsed (by decide), hl kLen (by decide), hl kRandLen (by decide), hu, hK,
      hrl, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt e2, Nat.mod_eq_of_lt hw]
    exact decide_eq_decide.mpr (by omega_using [hul])) rfl) fun t ⟨⟨hc, hm⟩, k⟩ => ⟨hc, hm, k⟩

/-- The public data of Miller–Rabin's loop: the offset of the first witness
and the shape of the result. -/
structure LPub where
  p : MrPub
  u0 : Nat
  S : Option (Bool × Nat)

/-- The offset of iteration `j`'s witness. -/
abbrev LPub.u (a : LPub) (j : Nat) : Nat := a.u0 + 8 * a.p.w * j

/-- The iterations of the loop. -/
abbrev LPub.N (a : LPub) : Nat := itersOf (8 * a.p.w) a.p.rl a.S a.u0

/-- Where the loop ends. -/
def LoopEnd (a : LPub) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ MrDims a.p.B a.p.Z a.p.w ∧
    ∃ (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)),
      MrEnd a.p.B a.p.Z a.p.w mi c r s₀ res s ∧ shapeOf res = a.S ∧ r.length = a.p.rl ∧
      word s₀.mem a.p.B (8 * kOut) = a.p.op ∧ word s₀.mem a.p.B (8 * kUsedP) = a.p.up ∧
      word s₀.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧ s₀.wr = a.p.wr

theorem hp_nil {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {s : State} (h : HP B wr vs s) :
    HP B wr [] s := ⟨h.rdi, h.wr, fun _ he => absurd he (List.not_mem_nil)⟩

/-- What Miller–Rabin needs, for the shape of its result. -/
def MrPre (a : LPub) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ HP a.p.B a.p.wr [] s ∧ MrDims a.p.B a.p.Z a.p.w ∧ a.p.ch < 2 ^ 62 ∧ a.p.rl < 2 ^ 64 ∧
    ∃ (mi : BitVec 64) (c bm : Nat) (r : List Byte), MrCtx s a.p.B a.p.Z a.p.w mi c bm ∧ ECtx s.mem a.p.B a.p.w c ∧
      wv s.mem a.p.B (slot a.p.w aR2) a.p.w = 2 ^ (64 * a.p.w) * 2 ^ (64 * a.p.w) % c ∧ 1 < c ∧
      VG.Proof.RsaKeyGen.PrimeShape (64 * a.p.w) c ∧ word s.mem a.p.B (8 * kOut) = a.p.op ∧
      word s.mem a.p.B (8 * kUsedP) = a.p.up ∧ word s.mem a.p.B (8 * kRand) = a.p.rP ∧
      word s.mem a.p.B (8 * kLen) = BitVec.ofNat 64 (8 * a.p.w) ∧
      word s.mem a.p.B (8 * kRandLen) = BitVec.ofNat 64 r.length ∧ r.length = a.p.rl ∧
      word s.mem a.p.B (8 * kChecks) = BitVec.ofNat 64 a.p.ch ∧ Src s a.p.B a.p.Z a.p.rP r ∧
      word s.mem a.p.B (8 * kUsed) = BitVec.ofNat 64 a.u0 ∧ 8 * a.p.w ≤ a.u0 ∧ a.u0 ≤ r.length ∧
      shapeOf (mrRest c a.p.ch r 1 0 a.u0) = a.S

end VG.Proof.RsaKeyGen.X86_64
