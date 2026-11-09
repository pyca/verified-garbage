module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.CallFacts
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.CallPre
import VerifiedGarbage.Proof.Framework.Omega

/-! # The attempt's precondition holds at its entry -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController controllerValue)
open VG.Proof.Ffdh.X86_64.Cached (cgPre)

theorem call_args {p : KeyPublic} {used : Nat} {s u : State} (hu : u.gpr .rsp = p.sp - 56)
    (hs : s.gpr .rsp = p.sp)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used)) :
    stackArg (callState p used u) 0 = BitVec.ofNat 64 p.len ∧
    stackArg (callState p used u) 1 = p.rp + BitVec.ofNat 64 used ∧
    stackArg (callState p used u) 2 = BitVec.ofNat 64 p.len ∧
    stackArg (callState p used u) 3 = p.B ∧
    stackArg (callState p used u) 4 = BitVec.ofNat 64 (p.Z / 8) ∧
    stackArg (callState p used u) 5 = p.ctx ∧
    stackArg (callState p used u) 6 = BitVec.ofNat 64 p.ctxLen := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    [rw [call_arg hu hs hm 0 (by decide)]; rw [call_arg hu hs hm 1 (by decide)];
      rw [call_arg hu hs hm 2 (by decide)]; rw [call_arg hu hs hm 3 (by decide)];
      rw [call_arg hu hs hm 4 (by decide)]; rw [call_arg hu hs hm 5 (by decide)];
      rw [call_arg hu hs hm 6 (by decide)]] <;>
    simp only [callValues, controllerValue, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]

theorem call_gpr {p : KeyPublic} {used : Nat} {u : State} {r : Reg} (hr : r ≠ .rsp) :
    (callState p used u).gpr r = u.gpr r := by
  simp only [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem call_attempt_pre {p : KeyPublic} {used : Nat} {s u : State} (hf : CallFacts p used)
    (hs : s.gpr .rsp = p.sp) (hu : u.gpr .rsp = p.sp - 56) (ha : KeyArgs p u)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used))
    (hdom : Spec.Rsa.bytesAt (callState p used u).mem p.dp p.dlen = p.dom)
    (hdv : Spec.Ffdh.domainValid p.len p.dom)
    (hcl : p.ctxLen = Spec.Ffdh.generationPrecomputedWords p.len)
    (hpc : Spec.Ffdh.generationPrecompute p.len p.dom = some (Spec.Rsa.wordsAt (callState p used u).mem p.ctx p.ctxLen)) :
    attemptContract.pre (callState p used u) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := call_args hu hs hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  have hzw : (BitVec.ofNat 64 (p.Z / 8)).toNat = p.Z / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.ns; omega)]
  have hcw : (BitVec.ofNat 64 p.ctxLen).toNat = p.ctxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.nc; omega)]
  have hargs : stackArgAddr (callState p used u) 0 = p.sp - 56 := call_argAddr hu
  have hrsp : (callState p used u).gpr .rsp = p.sp - 56 - 8 := call_rsp hu
  have hret := hf.ret
  have hhole := hf.hole
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hret hhole
  refine ⟨?_, ?_⟩
  · unfold cgPre
    simp only [call_gpr (by decide : Reg.rdi ≠ .rsp), call_gpr (by decide : Reg.rsi ≠ .rsp),
      call_gpr (by decide : Reg.rdx ≠ .rsp), call_gpr (by decide : Reg.rcx ≠ .rsp),
      call_gpr (by decide : Reg.r8 ≠ .rsp), call_gpr (by decide : Reg.r9 ≠ .rsp),
      hdi, hsi, hdx, hcx, h8, h9, h0, h1, h2, h3, h4, h5, h6, hargs, hrsp, hlen, hdl, hzw, hcw, hf.z8,
      State.withRegions_rd, State.withRegions_wr, hdom]
    refine ⟨?_, rfl, rfl, hf.xy, hf.xd, hf.xr, hf.xs, hf.xc, hf.xa, hf.yd, hf.yr, hf.ys, hf.yc, hf.ya,
      hf.ds, hf.rs, hf.sc, hf.sa, hf.nx, hf.ny, hf.nd, hf.nr, hf.ns, hf.nc, hret.1, hret.2.1, hret.2.2.1,
      hret.2.2.2.1, hret.2.2.2.2.1, hret.2.2.2.2.2.1, hret.2.2.2.2.2.2, hf.len, hf.dlen, trivial, trivial,
      trivial, hf.scratch, hdv, hcl, hpc⟩
    have he : p.sp - 56 - 8 = p.sp - BitVec.ofNat 64 64 := by rw [BitVec.sub_sub]; rfl
    rw [he, BitVec.toNat_sub_of_le (by
      change (BitVec.ofNat 64 64).toNat ≤ p.sp.toNat
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
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hhole.2.2.1
    · exact hhole.2.2.2.1
    · exact hhole.2.2.2.2.2.1
    · exact hhole.2.2.2.2.2.2
    · exact hhole.1
    · exact hhole.2.1
    · exact hhole.2.2.2.2.1

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
