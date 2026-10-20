module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallFacts
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallPre
import VerifiedGarbage.Proof.Framework.Omega

/-! # The attempt's precondition holds at its entry -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController controllerValue)
open VG.Proof.Ffdh.X86_64.GenerateKey (gkPre)

theorem call_args {p : KeyPublic} {used : Nat} {s u : State} (hu : u.gpr .rsp = p.sp - 40)
    (hs : s.gpr .rsp = p.sp)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used)) :
    stackArg (callState p used u) 0 = BitVec.ofNat 64 p.len ∧
    stackArg (callState p used u) 1 = p.rp + BitVec.ofNat 64 used ∧
    stackArg (callState p used u) 2 = BitVec.ofNat 64 p.len ∧
    stackArg (callState p used u) 3 = p.B ∧
    stackArg (callState p used u) 4 = BitVec.ofNat 64 (p.Z / 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    [rw [call_arg hu hs hm 0 (by decide)]; rw [call_arg hu hs hm 1 (by decide)];
      rw [call_arg hu hs hm 2 (by decide)]; rw [call_arg hu hs hm 3 (by decide)];
      rw [call_arg hu hs hm 4 (by decide)]] <;>
    simp only [callValues, controllerValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]

theorem call_gpr {p : KeyPublic} {used : Nat} {u : State} {r : Reg} (hr : r ≠ .rsp) :
    (callState p used u).gpr r = u.gpr r := by
  simp only [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_attempt_pre {p : KeyPublic} {used : Nat} {s u : State} (hf : CallFacts p used)
    (hs : s.gpr .rsp = p.sp) (hu : u.gpr .rsp = p.sp - 40) (ha : KeyArgs p u)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used)) :
    attemptContract.pre (callState p used u) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := call_args hu hs hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.ns; omega)]
  have hargs : stackArgAddr (callState p used u) 0 = p.sp - 40 := call_argAddr hu
  have hrsp : (callState p used u).gpr .rsp = p.sp - 40 - 8 := call_rsp hu
  have hret := hf.ret
  have hhole := hf.hole
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hret hhole
  refine ⟨?_, ?_⟩
  · unfold gkPre
    simp only [call_gpr (by decide : Reg.rdi ≠ .rsp), call_gpr (by decide : Reg.rsi ≠ .rsp),
      call_gpr (by decide : Reg.rdx ≠ .rsp), call_gpr (by decide : Reg.rcx ≠ .rsp),
      call_gpr (by decide : Reg.r8 ≠ .rsp), call_gpr (by decide : Reg.r9 ≠ .rsp),
      hdi, hsi, hdx, hcx, h8, h9, h0, h1, h2, h3, h4, hargs, hrsp, hlen, hdl, hzw, hf.z8,
      State.withRegions_rd, State.withRegions_wr]
    refine ⟨?_, rfl, rfl, hf.xy, hf.xd, hf.xr, hf.xs, hf.xa, hf.yd, hf.yr, hf.ys, hf.ya, hf.ds, hf.rs,
      hf.sa, hf.nx, hf.ny, hf.nd, hf.nr, hf.ns, hret.1, hret.2.1, hret.2.2.1, hret.2.2.2.1,
      hret.2.2.2.2.1, hret.2.2.2.2.2, hf.len, hf.dlen, trivial, trivial, trivial, hf.scratch⟩
    have he : p.sp - 40 - 8 = p.sp - BitVec.ofNat 64 48 := by rw [BitVec.sub_sub]; rfl
    rw [he, BitVec.toNat_sub_of_le (by
      change (BitVec.ofNat 64 48).toNat ≤ p.sp.toNat
      have := hf.room
      simp only [BitVec.toNat_ofNat]
      omega)]
    have := p.sp.isLt
    simp only [BitVec.toNat_ofNat]
    omega
  · show Clear (hole ((callState p used u).gpr .rsp)) (callState p used u)
    rw [hrsp]
    intro r hr
    simp only [State.withRegions_rd, State.withRegions_wr, callReads, callWrites,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hhole.2.2.1
    · exact hhole.2.2.2.1
    · exact hhole.2.2.2.2.2
    · exact hhole.1
    · exact hhole.2.1
    · exact hhole.2.2.2.2.1

end VG.Proof.Ffdh.X86_64.KeyGeneration
