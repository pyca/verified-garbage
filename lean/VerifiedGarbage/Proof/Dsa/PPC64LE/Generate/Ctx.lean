module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Ctx
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on PPC64LE: the layout of a call, and its context

`GL`: a call's public data (`glOf`): the stack pointer on entry, the
buffers' addresses and the lengths; `GL.Ok`, what `gkContract.pre` says of
them (`glOf_ok`). The frame is at `F`, 304 octets below the stack pointer.

`Ctx L s₀ t`: in the frame's body, the registers that hold the call's data,
the frame's saved registers, return address and `vg_dsa_derive_key`'s stack
argument, and the domain and the tape as on entry. A change of memory in
`out`, `scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- A call's public data. -/
structure GL where
  sp : Addr
  out : Addr
  used : Addr
  par : Addr
  rand : Addr
  scr : Addr
  pl : Nat
  ql : Nat
  rl : Nat
  sl : Nat

def glOf (s : State) : GL :=
  ⟨s.sp, s.gpr .r3, s.gpr .r5, s.gpr .r6, s.gpr .r10, stackArg s 1, (s.gpr .r8).toNat,
    (s.gpr .r9).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat⟩

namespace GL

variable (L : GL)

abbrev F : Addr := L.sp - BitVec.ofNat 64 frameBytes
/-- The domain's length. -/
abbrev kl : Nat := 2 * L.pl + L.ql
/-- The key's length. -/
abbrev ol : Nat := 3 * L.pl + 2 * L.ql
abbrev outR : Region := ⟨L.out, L.ol⟩
abbrev usedR : Region := ⟨L.used, 8⟩
abbrev parR : Region := ⟨L.par, L.kl⟩
abbrev randR : Region := ⟨L.rand, L.rl⟩
abbrev scrR : Region := ⟨L.scr, L.sl * 8⟩
abbrev frR : Region := ⟨L.F, frameBytes⟩
/-- The nonce. -/
abbrev nR : Region := ⟨off L.F oNonce, 32⟩

end GL

/-- What the precondition says of a call's data. -/
structure GL.Ok (L : GL) : Prop where
  lv : Spec.Dsa.lengthsValid L.pl L.ql
  sw : 64 * L.pl + 1024 ≤ L.sl
  spF : frameBytes ≤ L.sp.toNat
  spTop : L.sp.toNat + 120 ≤ 2 ^ 64
  nwOut : L.out.toNat + L.ol ≤ 2 ^ 64
  nwUsed : L.used.toNat + 8 ≤ 2 ^ 64
  nwPar : L.par.toNat + L.kl ≤ 2 ^ 64
  nwRand : L.rand.toNat + L.rl ≤ 2 ^ 64
  nwScr : L.scr.toNat + L.sl * 8 ≤ 2 ^ 64
  rl : L.rl < 2 ^ 64
  sl : L.sl < 2 ^ 64
  dOU : L.outR.Disjoint L.usedR
  dOK : L.outR.Disjoint L.parR
  dOR : L.outR.Disjoint L.randR
  dOS : L.outR.Disjoint L.scrR
  dUK : L.usedR.Disjoint L.parR
  dUR : L.usedR.Disjoint L.randR
  dUS : L.usedR.Disjoint L.scrR
  dKS : L.parR.Disjoint L.scrR
  dRS : L.randR.Disjoint L.scrR
  dFO : L.frR.Disjoint L.outR
  dFU : L.frR.Disjoint L.usedR
  dFK : L.frR.Disjoint L.parR
  dFR : L.frR.Disjoint L.randR
  dFS : L.frR.Disjoint L.scrR

theorem glOf_ok {s : State} (h : gkContract.pre s) : (glOf s).Ok := by
  obtain ⟨hF, hT, -, -, dOU, dOK, dOR, dOS, -, dUK, dUR, dUS, -, dKS, dRS, -,
    dFO, dFU, dFK, dFR, dFS, -, nO, nU, nK, nR, nS, lv, hol, hkl, hsw⟩ := h
  simp only [Spec.Dsa.generationScratchWords] at hsw
  have e4 : 3 * (s.gpr .r8).toNat + 2 * (s.gpr .r9).toNat = (s.gpr .r4).toNat := hol.symm
  have e7 : 2 * (s.gpr .r8).toNat + (s.gpr .r9).toNat = (s.gpr .r7).toNat := hkl.symm
  have hT' : s.sp.toNat + 120 ≤ 2 ^ 64 := by omega
  refine ⟨lv, hsw, hF, hT', ?_, nU, ?_, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
    ?_, ?_, ?_, ?_, ?_, dUR, dUS, ?_, dRS, ?_, dFU, ?_, dFR, dFS⟩ <;>
  simp only [GL.outR, GL.parR, GL.kl, GL.ol, GL.frR, GL.F, glOf, e4, e7]
  · exact nO
  · exact nK
  · exact dOU
  · exact dOK
  · exact dOR
  · exact dOS
  · exact dUK
  · exact dKS
  · exact dFO
  · exact dFK

namespace GL.Ok

variable {L : GL} (hL : L.Ok)
include hL

theorem ql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega

theorem pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega

theorem F_toNat : L.F.toNat = L.sp.toNat - frameBytes := by
  have h1 := hL.spF
  have h2 := L.sp.isLt
  simp only [GL.F, frameBytes] at h1 ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem fnw : L.F.toNat + frameBytes ≤ 2 ^ 64 := by
  have := hL.F_toNat; have := hL.spF; have := hL.spTop; omega

omit hL in
/-- A range of the frame is apart from a region apart from the frame. -/
theorem frame_disj {r : Region} (hd : L.frR.Disjoint r) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off L.F d, n⟩ : Region).Disjoint r :=
  hd.sub_left (VG.Offset.sub_base _ h)

end GL.Ok

/-- In the frame's body. -/
structure Ctx (L : GL) (s₀ : State) (t : State) : Prop where
  sp : t.sp = L.F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr
  r2 : t.gpr .r2 = s₀.gpr .r2
  r18 : t.gpr .r18 = L.out
  r19 : t.gpr .r19 = L.par
  r20 : t.gpr .r20 = BitVec.ofNat 64 L.pl
  r21 : t.gpr .r21 = BitVec.ofNat 64 L.ql
  r22 : t.gpr .r22 = L.scr
  r23 : t.gpr .r23 = L.rand
  r24 : t.gpr .r24 = BitVec.ofNat 64 L.rl
  r26 : t.gpr .r26 = BitVec.ofNat 64 L.sl
  r30 : t.gpr .r30 = L.used
  sav : ∀ i < 18, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (nv i)
  lr : t.mem.readW (off L.F oLr) 64 = s₀.lr
  a0 : t.mem.readW (off L.F oArgs) 64 = BitVec.ofNat 64 L.sl
  par : Spec.Rsa.bytesAt t.mem L.par L.kl = Spec.Rsa.bytesAt s₀.mem L.par L.kl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.r2, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r26, .r30]

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : GL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
  have hq := hL.ql
  simp only [frameBytes] at hF
  have fw : ∀ d, d + 8 ≤ frameBytes → (d + 8 ≤ oNonce ∨ oNonce + 32 ≤ d) →
      t'.mem.readW (off L.F d) 64 = t.mem.readW (off L.F d) 64 := fun d hd hn =>
    hf.readW (r := ⟨off L.F d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact GL.Ok.frame_disj hL.dFO hd
      · exact GL.Ok.frame_disj hL.dFS hd
      · exact VG.Offset.disjoint L.F (by simp only [oNonce] at hn ⊢; omega) (by simp only [frameBytes] at hd; omega)
          (by simp only [oNonce]; omega)) (by decide)
  have nr : ∀ {A : Addr} {k : Nat}, L.frR.Disjoint ⟨A, k⟩ → (⟨A, k⟩ : Region).Disjoint L.nR := fun hd =>
    (GL.Ok.frame_disj hd (d := oNonce) (n := 32) (by decide)).symm
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.r2,
    (hg _ (by decide)).trans h.r18, (hg _ (by decide)).trans h.r19, (hg _ (by decide)).trans h.r20,
    (hg _ (by decide)).trans h.r21, (hg _ (by decide)).trans h.r22, (hg _ (by decide)).trans h.r23,
    (hg _ (by decide)).trans h.r24, (hg _ (by decide)).trans h.r26, (hg _ (by decide)).trans h.r30,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega) (by simp only [oSave, oNonce]; omega)).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.lr, (fw _ (by decide) (by decide)).trans h.a0, ?_, ?_⟩
  · refine (RS.bytes_frame hf (fun r hr => ?_) (by have := hL.nwPar; omega)).trans h.par
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (RS.bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.PPC64LE.GK
