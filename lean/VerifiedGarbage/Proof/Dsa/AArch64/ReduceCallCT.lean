module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetupCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInitCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInitCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoopCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant time of complete DSA streaming reduction, including empty inputs -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ReduceCallBytes (p : ReducePublic) (s : State) : Prop := ∃ bs : List Byte,
  bs.length = p.bytes.len ∧ word s.mem p.bytes.x.B (8 * arg) = p.bytes.ptr ∧
  word s.mem p.bytes.x.B (8 * argLen) = BitVec.ofNat 64 bs.length ∧
  Src s p.bytes.x.B p.bytes.x.Z p.bytes.ptr bs

def ReduceCallPre (p : ReducePublic) (s : State) : Prop := ReduceSetupPre p s ∧ ReduceCallBytes p s

def ReduceCallPrepared (p : ReducePublic) (s : State) : Prop :=
  ReduceContext p s ∧ ReduceCallBytes p s ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aXm) p.bytes.x.wx =
    256 * 2 ^ (64 * p.bytes.x.wx) % p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx = 0 ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aX) p.bytes.x.wx = 0

def ReduceStart (p : ReducePublic) (s : State) : Prop :=
  ReduceLoopPre p 0 s ∧ s.gpr .x3 = BitVec.ofNat 64 p.bytes.len

theorem reduceCall_setup (M : Mont) {p : ReducePublic} {s : State} (h : ReduceCallPre p s) :
    WP isa (Arithmetic.reduceSetup M.mm) s (ReduceCallPrepared p) := by
  obtain ⟨⟨⟨hc, hm⟩, hw⟩, bs, hlen, hp, hl, hs⟩ := h
  refine WP.mono (reduceSetup_ok M hc p.lower hw p.greater p.odd hm.modulus hm.inverse)
    fun t ⟨hct, hmt, _, hr, hy, hx, hf, hk⟩ => ?_
  exact ⟨⟨hct, hmt⟩, ⟨bs, hlen, (work_parent hc hf (by decide)).trans hp,
    (work_parent hc hf (by decide)).trans hl, work_source hc hf hk hs⟩, hr, hy, hx⟩

theorem reduceCall_init {p : ReducePublic} {s : State} (h : ReduceCallPrepared p s) :
    WP isa (.block (Arithmetic.reduceInit arg argLen)) s (ReduceStart p) := by
  obtain ⟨⟨hc, hm⟩, ⟨bs, hlen, hp, hl, hs⟩, hr, hy, hx⟩ := h
  refine WP.mono (reduceInit_ok hc hm (by decide) (by decide) hp hl)
    fun t ⟨hct, hmt, harr, hptr, hrem, hz, hf, hk⟩ => ?_
  have ht : ReduceState t p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv p.bytes.ptr bs 0 :=
    ⟨hct, hmt, (harr aXm (by decide)).trans hr,
      fun i hi _ => (wv_eq_zero_iff _ _ _ _).mp ((harr aX (by decide)).trans hx) i hi,
      (harr aY (by decide)).trans hy, by have := p.greater; omega, hptr, hrem,
      work_source hc hf hk hs⟩
  refine ⟨⟨bs, 0, ?_, ?_⟩, ?_⟩
  · simpa only [Nat.sub_zero] using hlen
  · simpa only [BitVec.add_zero] using ht
  · simpa only [hlen] using hz

theorem reduceCall_ct (M : Mont) : RelCT isa (Two ReduceCallPre)
    (Arithmetic.reduce M.mm arg argLen) (fun _ _ => True) := by
  unfold Arithmetic.reduce seqs
  refine RelCT.seq (two_post (Ψ := ReduceCallPrepared)
    (two_map (fun p : ReducePublic => p) (fun _ _ h => h.1) (reduceSetup_ct M))
    (fun _ _ h => reduceCall_setup M h)) ?_
  refine RelCT.seq (two_post (Ψ := ReduceStart)
    (two_map (fun p : ReducePublic => p.bytes.x) (fun _ _ h => ⟨_, h.1.1⟩) reduceInit_ct)
    (fun _ _ h => reduceCall_init h)) ?_
  refine two_ite (fun p s t hs ht => by rw [eval_zero, eval_zero, hs.2, ht.2]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_map (fun p : ReducePublic => p) (fun p s h => by
      refine ⟨?_, h.1.1⟩
      have hz := h.1.2
      have he := h.2
      rw [eval_zero, hz, eq_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.lengthBound] at he
      simp only [Option.some.injEq, decide_eq_false_iff_not] at he
      omega) (reduceLoop_ct M)

end VG.Proof.Dsa.AArch64
