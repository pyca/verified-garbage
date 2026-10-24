module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on PPC64LE: the layout of a call, and its context

`RL`: a call's public data (`rlOf`): the stack pointer on entry, the
buffers' addresses and the lengths; `RL.Ok`, what `rsContract.pre` says of
them (`rlOf_ok`). The frame is at `F`, 304 octets below the stack pointer.

`Ctx L s₀ t`: in the frame's body, the registers that hold the call's data,
the frame's saved registers, return address and `vg_dsa_sign`'s stack
arguments, and the key, the digest and the tape as on entry. A change of
memory in `out`, `scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- A call's public data. -/
structure RL where
  sp : Addr
  out : Addr
  used : Addr
  key : Addr
  dig : Addr
  rand : Addr
  scr : Addr
  pl : Nat
  ql : Nat
  dl : Nat
  rl : Nat
  sl : Nat

def rlOf (s : State) : RL :=
  ⟨s.sp, s.gpr .r3, s.gpr .r5, s.gpr .r6, s.gpr .r10, stackArg s 1, stackArg s 3, (s.gpr .r8).toNat,
    (s.gpr .r9).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat, (stackArg s 4).toNat⟩

namespace RL

variable (L : RL)

abbrev F : Addr := L.sp - BitVec.ofNat 64 frameBytes
abbrev kl : Nat := 3 * L.pl + 2 * L.ql
abbrev outR : Region := ⟨L.out, 2 * L.ql⟩
abbrev usedR : Region := ⟨L.used, 8⟩
abbrev keyR : Region := ⟨L.key, L.kl⟩
abbrev digR : Region := ⟨L.dig, L.dl⟩
abbrev randR : Region := ⟨L.rand, L.rl⟩
abbrev scrR : Region := ⟨L.scr, L.sl * 8⟩
abbrev frR : Region := ⟨L.F, frameBytes⟩
/-- The nonce. -/
abbrev nR : Region := ⟨off L.F oNonce, 32⟩

end RL

/-- What the precondition says of a call's data. -/
structure RL.Ok (L : RL) : Prop where
  lv : Spec.Dsa.lengthsValid L.pl L.ql
  sw : 16 * L.pl + 64 ≤ L.sl
  spF : frameBytes ≤ L.sp.toNat
  spTop : L.sp.toNat + 136 ≤ 2 ^ 64
  nwOut : L.out.toNat + 2 * L.ql ≤ 2 ^ 64
  nwUsed : L.used.toNat + 8 ≤ 2 ^ 64
  nwKey : L.key.toNat + L.kl ≤ 2 ^ 64
  nwDig : L.dig.toNat + L.dl ≤ 2 ^ 64
  nwRand : L.rand.toNat + L.rl ≤ 2 ^ 64
  nwScr : L.scr.toNat + L.sl * 8 ≤ 2 ^ 64
  dl : L.dl < 2 ^ 64
  rl : L.rl < 2 ^ 64
  sl : L.sl < 2 ^ 64
  dOU : L.outR.Disjoint L.usedR
  dOK : L.outR.Disjoint L.keyR
  dOD : L.outR.Disjoint L.digR
  dOR : L.outR.Disjoint L.randR
  dOS : L.outR.Disjoint L.scrR
  dUK : L.usedR.Disjoint L.keyR
  dUD : L.usedR.Disjoint L.digR
  dUR : L.usedR.Disjoint L.randR
  dUS : L.usedR.Disjoint L.scrR
  dKS : L.keyR.Disjoint L.scrR
  dDS : L.digR.Disjoint L.scrR
  dRS : L.randR.Disjoint L.scrR
  dFO : L.frR.Disjoint L.outR
  dFU : L.frR.Disjoint L.usedR
  dFK : L.frR.Disjoint L.keyR
  dFD : L.frR.Disjoint L.digR
  dFR : L.frR.Disjoint L.randR
  dFS : L.frR.Disjoint L.scrR

theorem rlOf_ok {s : State} (h : rsContract.pre s) : (rlOf s).Ok := by
  obtain ⟨hF, hT, -, -, dOU, dOK, dOD, dOR, dOS, -, dUK, dUD, dUR, dUS, -, dKS, dDS, dRS, -,
    dFO, dFU, dFK, dFD, dFR, dFS, -, nO, nU, nK, nD, nR, nS, lv, hol, hkl, hsw⟩ := h
  simp only [Spec.Dsa.randomSignScratchWords, Spec.Dsa.scratchWords] at hsw
  have e4 : 2 * (s.gpr .r9).toNat = (s.gpr .r4).toNat := hol.symm
  have e7 : 3 * (s.gpr .r8).toNat + (s.gpr .r4).toNat = (s.gpr .r7).toNat := by omega
  have hT' : s.sp.toNat + 136 ≤ 2 ^ 64 := by omega
  refine ⟨lv, hsw, hF, hT', ?_, nU, ?_, nD, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
    (stackArg s 4).isLt, ?_, ?_, ?_, ?_, ?_, ?_, dUD, dUR, dUS, ?_, dDS, dRS, ?_, dFU, ?_, dFD, dFR, dFS⟩ <;>
  simp only [RL.outR, RL.keyR, RL.kl, RL.frR, RL.F, rlOf, e4, e7]
  · exact nO
  · exact nK
  · exact dOU
  · exact dOK
  · exact dOD
  · exact dOR
  · exact dOS
  · exact dUK
  · exact dKS
  · exact dFO
  · exact dFK

namespace RL.Ok

variable {L : RL} (hL : L.Ok)
include hL

theorem ql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega

theorem pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega

theorem F_toNat : L.F.toNat = L.sp.toNat - frameBytes := by
  have h1 := hL.spF
  have h2 := L.sp.isLt
  simp only [RL.F, frameBytes] at h1 ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem fnw : L.F.toNat + frameBytes ≤ 2 ^ 64 := by
  have := hL.F_toNat; have := hL.spF; have := hL.spTop; omega

omit hL in
/-- A range of the frame is apart from a region apart from the frame. -/
theorem frame_disj {r : Region} (hd : L.frR.Disjoint r) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off L.F d, n⟩ : Region).Disjoint r :=
  hd.sub_left (VG.Offset.sub_base _ h)

end RL.Ok

/-- In the frame's body. -/
structure Ctx (L : RL) (s₀ : State) (t : State) : Prop where
  sp : t.sp = L.F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr
  r2 : t.gpr .r2 = s₀.gpr .r2
  r18 : t.gpr .r18 = L.out
  r19 : t.gpr .r19 = L.key
  r20 : t.gpr .r20 = BitVec.ofNat 64 L.pl
  r21 : t.gpr .r21 = BitVec.ofNat 64 L.ql
  r22 : t.gpr .r22 = L.dig
  r23 : t.gpr .r23 = L.rand
  r24 : t.gpr .r24 = BitVec.ofNat 64 L.rl
  r30 : t.gpr .r30 = L.used
  sav : ∀ i < 18, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (nv i)
  lr : t.mem.readW (off L.F oLr) 64 = s₀.lr
  a0 : t.mem.readW (off L.F oArgs) 64 = BitVec.ofNat 64 L.dl
  a1 : t.mem.readW (off L.F (oArgs + 8)) 64 = L.scr
  a2 : t.mem.readW (off L.F (oArgs + 16)) 64 = BitVec.ofNat 64 L.sl
  key : Spec.Rsa.bytesAt t.mem L.key L.kl = Spec.Rsa.bytesAt s₀.mem L.key L.kl
  dig : Spec.Rsa.bytesAt t.mem L.dig L.dl = Spec.Rsa.bytesAt s₀.mem L.dig L.dl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.r2, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r30]

/-- The octets of a region apart from the regions a change is within are kept. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {A : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨A, k⟩ : Region).Disjoint r) (hk : k ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  exact hf.bytes (R := ⟨A, k⟩) hd hk hi

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : RL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
  have hq := hL.ql
  simp only [frameBytes] at hF
  -- The frame's words other than the nonce are apart from the three regions.
  have fw : ∀ d, d + 8 ≤ frameBytes → (d + 8 ≤ oNonce ∨ oNonce + 32 ≤ d) →
      t'.mem.readW (off L.F d) 64 = t.mem.readW (off L.F d) 64 := fun d hd hn =>
    hf.readW (r := ⟨off L.F d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact RL.Ok.frame_disj hL.dFO hd
      · exact RL.Ok.frame_disj hL.dFS hd
      · exact VG.Offset.disjoint L.F (by simp only [oNonce] at hn ⊢; omega) (by simp only [frameBytes] at hd; omega)
          (by simp only [oNonce]; omega)) (by decide)
  have nr : ∀ {A : Addr} {k : Nat}, L.frR.Disjoint ⟨A, k⟩ → (⟨A, k⟩ : Region).Disjoint L.nR := fun hd =>
    (RL.Ok.frame_disj hd (d := oNonce) (n := 32) (by decide)).symm
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.r2,
    (hg _ (by decide)).trans h.r18, (hg _ (by decide)).trans h.r19, (hg _ (by decide)).trans h.r20,
    (hg _ (by decide)).trans h.r21, (hg _ (by decide)).trans h.r22, (hg _ (by decide)).trans h.r23,
    (hg _ (by decide)).trans h.r24, (hg _ (by decide)).trans h.r30,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega) (by simp only [oSave, oNonce]; omega)).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.lr, (fw _ (by decide) (by decide)).trans h.a0,
    (fw _ (by decide) (by decide)).trans h.a1, (fw _ (by decide) (by decide)).trans h.a2, ?_, ?_, ?_⟩
  · refine (bytes_frame hf (fun r hr => ?_) (by have := hL.nwKey; omega)).trans h.key
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.dl)).trans h.dig
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOD.symm
    · exact hL.dDS
    · exact nr hL.dFD
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.PPC64LE.RS
