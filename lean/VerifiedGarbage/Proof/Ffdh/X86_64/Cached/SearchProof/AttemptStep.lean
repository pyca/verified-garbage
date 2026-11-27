module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptRun
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Attempt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Data
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Ffdh.X86_64.Cached.SearchProof.CallEntry`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.Cached.SearchProof.CallFacts`, which this module and modules that import it used -/

section

/-! # Where the attempt's buffers are, from the controller's

The attempt's buffers are the controller's (`x`, `y`, the domain, a slice
of the tape, the working space and the context), and its stack arguments, return
address and its callee's return address are in the 72 octets of stack below
the controller's return address, which no buffer overlaps.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The attempt's regions: its outputs, the domain, the tape's slice, the
working space, its arguments; its return address and its callee's. -/
abbrev rX (p : KeyPublic) : Region := ⟨p.xp, p.len⟩
abbrev rY (p : KeyPublic) : Region := ⟨p.yp, p.len⟩
abbrev rD (p : KeyPublic) : Region := ⟨p.dp, p.dlen⟩
abbrev rR (p : KeyPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.len⟩
abbrev rS (p : KeyPublic) : Region := ⟨p.B, p.Z⟩
abbrev rC (p : KeyPublic) : Region := ⟨p.ctx, p.ctxLen * 8⟩
abbrev rA (p : KeyPublic) : Region := ⟨p.sp - 56, 56⟩
abbrev rRet (p : KeyPublic) : Region := ⟨p.sp - 56 - 8, 8⟩
abbrev rHole (p : KeyPublic) : Region := hole (p.sp - 56 - 8)

structure CallFacts (p : KeyPublic) (used : Nat) : Prop where
  room : 72 ≤ p.sp.toNat
  xy : (rX p).Disjoint (rY p)
  xd : (rX p).Disjoint (rD p)
  xr : (rX p).Disjoint (rR p used)
  xs : (rX p).Disjoint (rS p)
  xa : (rX p).Disjoint (rA p)
  yd : (rY p).Disjoint (rD p)
  yr : (rY p).Disjoint (rR p used)
  ys : (rY p).Disjoint (rS p)
  ya : (rY p).Disjoint (rA p)
  ds : (rD p).Disjoint (rS p)
  rs : (rR p used).Disjoint (rS p)
  sa : (rS p).Disjoint (rA p)
  xc : (rX p).Disjoint (rC p)
  yc : (rY p).Disjoint (rC p)
  sc : (rS p).Disjoint (rC p)
  ca : (rC p).Disjoint (rA p)
  nx : p.xp.toNat + p.len ≤ 2 ^ 64
  ny : p.yp.toNat + p.len ≤ 2 ^ 64
  nd : p.dp.toNat + p.dlen ≤ 2 ^ 64
  nr : (p.rp + BitVec.ofNat 64 used).toNat + p.len ≤ 2 ^ 64
  ns : p.B.toNat + p.Z ≤ 2 ^ 64
  nc : p.ctx.toNat + p.ctxLen * 8 ≤ 2 ^ 64
  ret : ∀ r ∈ [rX p, rY p, rD p, rR p used, rS p, rC p, rA p], (rRet p).Disjoint r
  hole : ∀ r ∈ [rX p, rY p, rD p, rR p used, rS p, rC p, rA p], r.Disjoint (rHole p)
  len : Spec.Ffdh.pLenValid p.len
  dlen : Spec.Ffdh.domainLenValid p.len p.dlen
  scratch : Spec.Rsa.scratchWords p.len ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  len64 : p.len < 2 ^ 64
  dlen64 : p.dlen < 2 ^ 64

private theorem sub_tape {r : Addr} {n used len : Nat}
    (hu : used + len ≤ n) : Region.Sub ⟨r + BitVec.ofNat 64 used, len⟩ ⟨r, n⟩ :=
  Offset.sub_base r hu

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ len = 0 := by omega_using [hn, hu]
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega_using [hn, hu]
    · omega_using [hn, hu]
  · subst hz; simp only [Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

private theorem sp_64 (sp : Addr) : sp - 56 - 8 = sp - BitVec.ofNat 64 64 := by
  rw [BitVec.sub_sub]; rfl

private theorem sp_72 (sp : Addr) : sp - 56 - 8 - 8 = sp - BitVec.ofNat 64 72 := by
  rw [BitVec.sub_sub, BitVec.sub_sub]; rfl

private theorem sp_56 (sp : Addr) : sp - 56 = sp - BitVec.ofNat 64 56 := rfl

theorem rRet_sub (p : KeyPublic) : Region.Sub (rRet p) (below p.sp stackUse) := by
  rw [rRet, sp_64]; exact Offset.sub_below _ (by decide) (by decide)

theorem rA_sub (p : KeyPublic) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, sp_56]; exact Offset.sub_below _ (by decide) (by decide)

theorem rHole_sub (p : KeyPublic) : Region.Sub (rHole p) (below p.sp stackUse) := by
  rw [rHole, hole, sp_72]; exact Offset.sub_below _ (by decide) (by decide)

theorem ret_args (p : KeyPublic) : (rRet p).Disjoint (rA p) := by
  have := Offset.base_disjoint (p.sp - 56 - 8) (k := 8) (e := 8) (n := 56) (by decide) (by decide)
  rwa [show p.sp - 56 - 8 + BitVec.ofNat 64 8 = p.sp - 56 from BitVec.sub_add_cancel _ _] at this

theorem hole_args (p : KeyPublic) : (rA p).Disjoint (rHole p) := by
  have := Offset.base_disjoint (p.sp - 56 - 8 - 8) (k := 8) (e := 16) (n := 56) (by decide) (by decide)
  rw [show p.sp - 56 - 8 - 8 + BitVec.ofNat 64 16 = p.sp - 56 by
    rw [BitVec.sub_sub (p.sp - 56) 8 8]
    exact BitVec.sub_add_cancel _ _] at this
  exact this.symm

theorem KeyLive.callFacts {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    CallFacts p used := by
  have hi := h.input
  obtain ⟨_, hsp, _, _, hnw, hpw, hwr, hstk, hlen, hdlen, hrsi, hrcx, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pxy, pxu, pxs, pxc⟩, ⟨pyu, pys, pyc⟩, ⟨pus, puc⟩, psc⟩ := hpw
  obtain ⟨⟨wxd, wxr, wxc, wxa⟩, ⟨wyd, wyr, wyc, wya⟩, -, ⟨wsd, wsr, wsc, wsa⟩, -⟩ := hwr
  obtain ⟨⟨-, bx⟩, ⟨-, by'⟩, -, ⟨-, bs⟩, -, ⟨-, bd⟩, ⟨-, br⟩, ⟨-, bc⟩, -⟩ := hstk
  obtain ⟨nx, ny, -, ns, -, nd, nr, nc, -⟩ := hnw
  have hX : rX (keyOfState original) = inX original := by
    simp only [rX, inX, keyOfState, hrsi]
  have hY : rY (keyOfState original) = inY original := by
    simp only [rY, inY, keyOfState, hrcx]
  have hD : rD (keyOfState original) = inDom original := rfl
  have hS : rS (keyOfState original) = inScr original := rfl
  have hC : rC (keyOfState original) = inContext original := rfl
  have hR : Region.Sub (rR (keyOfState original) used) (inRand original) :=
    sub_tape hroom
  have hA := rA_sub (keyOfState original)
  have hRet := rRet_sub (keyOfState original)
  have hH := rHole_sub (keyOfState original)
  have hsp' : (keyOfState original).sp = original.gpr .rsp := rfl
  rw [hsp'] at hA hRet hH
  rw [← hX] at pxy pxs wxd wxr wxc bx nx
  rw [← hY] at pxy pys wyd wyr wyc by' ny
  rw [← hD] at wxd wyd wsd bd nd
  rw [← hS] at pxs pys wsd wsr wsc bs ns
  rw [← hC] at wxc wyc wsc bc nc
  refine ⟨by rw [hsp']; exact hsp, pxy, wxd, wxr.sub_right hR, pxs, (bx.symm.sub_right hA),
    wyd, wyr.sub_right hR, pys, by'.symm.sub_right hA, wsd.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, wxc, wyc, wsc, bc.symm.sub_right hA, nx, ny, nd, nowrap_tape nr hroom, ns, nc, ?_, ?_, hlen, hdlen, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bx.sub_left hRet
    · exact by'.sub_left hRet
    · exact bd.sub_left hRet
    · exact (br.sub_left hRet).sub_right hR
    · exact bs.sub_left hRet
    · exact bc.sub_left hRet
    · exact ret_args _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (bx.sub_left hH).symm
    · exact (by'.sub_left hH).symm
    · exact (bd.sub_left hH).symm
    · exact ((br.sub_left hH).sub_right hR).symm
    · exact (bs.sub_left hH).symm
    · exact (bc.sub_left hH).symm
    · exact hole_args _
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
  · exact BitVec.isLt _
  · exact BitVec.isLt _

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

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
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.ns; omega_using [this])]
  have hcw : (BitVec.ofNat 64 p.ctxLen).toNat = p.ctxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.nc; omega_using [this])]
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
      omega_using [this])]
    have := p.sp.isLt
    simp only [BitVec.toNat_ofNat]
    omega_using []
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

end

end

/-! # The attempt, from the controller's loop state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated freed allocated_rsp allocated_reg
  freed_rsp freed_reg frame_alloc)
open VG.Proof.Ffdh.X86_64.Cached (cgPost attemptCode attemptCode_sp cgDom cgRand cgA cgS)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search hiding attemptRun attemptOrRequest iteration code
open VG.Impl.Ffdh.X86_64.Cached.Search

theorem KeyInput.domain_valid {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Spec.Ffdh.domainValid p.len p.dom := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -⟩ := h.1
  rw [← h.2]; exact hv

theorem KeyInput.context_pre {p : KeyPublic} {s : State} (h : KeyInput p s) :
    p.ctxLen = Spec.Ffdh.generationPrecomputedWords p.len ∧
      Spec.Ffdh.generationPrecompute p.len p.dom = some (Spec.Rsa.wordsAt s.mem p.ctx p.ctxLen) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcl, hpc⟩ := h.1
  rw [← h.2]; exact ⟨hcl, hpc⟩

/-- The attempt's view of the domain and the tape, at its entry. -/
theorem call_inputs {p : KeyPublic} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 56) (ha : KeyArgs p u) :
    cgDom (callState p used u) = p.dom ∧
      cgRand (callState p used u) = ((keyRand original).drop used).take p.len ∧
      (stackArg (callState p used u) 0).toNat = p.len ∧
      Spec.Rsa.wordsAt (callState p used u).mem p.ctx p.ctxLen = Spec.Rsa.wordsAt original.mem p.ctx p.ctxLen := by
  have hfr := call_mem_frame h hm hu
  obtain ⟨h0, h1, h2, -, -⟩ := call_args hu h.rsp hm
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  refine ⟨?_, ?_, by rw [h0, hlen], (h.input.context_frame hfr).trans h.context⟩
  · simp only [cgDom, call_gpr (by decide : Reg.r8 ≠ .rsp), call_gpr (by decide : Reg.r9 ≠ .rsp),
      ha.2.2.2.2.1, ha.2.2.2.2.2, hdl]
    exact (h.input.domain_frame hfr).trans h.domain
  · simp only [cgRand, h1, h2, hlen]
    have hr := (h.input.random_frame hfr).trans h.random
    rw [← VG.Proof.Dsa.bytesAt_slice _ _ hroom, ← hr]

/-- The attempt's precondition at its entry. -/
theorem call_pre {p : KeyPublic} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 56) (ha : KeyArgs p u) :
    attemptContract.pre (callState p used u) := by
  obtain ⟨hdom, -, -, hctx⟩ := call_inputs h hroom hf hm hu ha
  have hcp := h.input.context_pre
  have hdom' : Spec.Rsa.bytesAt (callState p used u).mem p.dp p.dlen = p.dom := by
    have := hdom
    simp only [cgDom, call_gpr (by decide : Reg.r8 ≠ .rsp), call_gpr (by decide : Reg.r9 ≠ .rsp),
      ha.2.2.2.2.1, ha.2.2.2.2.2] at this
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64] at this
  exact call_attempt_pre hf h.rsp hu ha hm hdom' h.input.domain_valid hcp.1 (by rw [hctx]; exact hcp.2)

theorem key_attempt_run (v : RoundImpl) {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun (attemptCall v)) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have hroom' : 56 ≤ (s.gpr .rsp).toNat := by rw [h.rsp]; have := hf.room; omega_using [this]
  unfold attemptRun
  apply frame_alloc (by decide) (by decide) (by decide) hroom'
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hu : u.gpr .rsp = p.sp - 56 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  obtain ⟨hdom, hrand, h0, -⟩ := call_inputs h hroom hf hm hu ha
  have hpre := call_pre h hroom hf hm hu ha
  have hd := attemptCode_depth v
  refine WP.callF (k := attemptContract) (attempt_correct v) (SpSafe.of_all (attemptCode_sp v))
    (by omega_using [hd]) hpre (call_covers_reads h hroom k.2.1 k.2.2) (call_covers_writes h k.2.2) ?_
  intro t hrd hwr hcs hfr ⟨s₂, hm₂, hg₂, hpost⟩ _
  have htsp : t.gpr .rsp = u.gpr .rsp := hcs .rsp (by decide)
  have hR : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 56, 56⟩ (below (original.gpr .rsp) stackUse) := by
    rw [show s.gpr .rsp = original.gpr .rsp by rw [h.rsp, ← h.input.2]; rfl]
    exact Offset.sub_below _ (by decide) (by decide)
  refine ⟨htsp.trans (k.gpr (by decide)), hwr.trans k.2.2, fun m uu fm => ⟨?_, ?_⟩⟩
  · -- The loop state, after the frame.
    apply h.restore (t := { freed 56 t with mem := m, unknowns := uu }) (show (freed 56 t).rd = s.rd from hrd.trans k.2.1)
      (show (freed 56 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.2.2]; rfl)
    · intro r hr
      by_cases he : r = .rsp
      · subst he
        rw [freed_rsp, htsp, k.gpr (by decide), allocated_rsp]
        exact BitVec.sub_add_cancel _ _
      · rw [freed_reg _ _ _ he, hcs r hr, k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
          allocated_reg _ _ _ he]
    · exact (attempt_frame h hm hu hd hfr).trans (fm.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp [KeyInput.callChanges], hR⟩)
  · -- The attempt's status and outputs.
    refine AttemptPost.lost (t := freed 56 t) h.input ?_ (freed_reg 56 t .rax (by decide)) fm hR
    have hp := hpost
    simp only [attemptContract, cgPost, cgA, cgS, hdom, hrand, h0] at hp
    obtain ⟨hst, hout⟩ := hp
    have hrax : (freed 56 t).gpr .rax = s₂.gpr .rax := by
      rw [freed_reg _ _ _ (by decide), hg₂ .rax (by decide)]
    have hmem : (freed 56 t).mem = s₂.mem := hm₂.symm
    simp only [call_gpr (by decide : Reg.rdi ≠ .rsp), call_gpr (by decide : Reg.rdx ≠ .rsp),
      ha.1, ha.2.2.1] at hout
    unfold AttemptPost
    rw [hrax, hmem]
    exact ⟨hst, hout⟩

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
