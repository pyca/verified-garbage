module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndEnv
public import VerifiedGarbage.Proof.Dsa.RISCV64.RndSave
public import VerifiedGarbage.Impl.Dsa.RISCV64.RandomSign
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on RISC-V: the contract on the registers, and the frame's state

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Contract.lean` and `Ctx.lean`).
`rsContract`: `vg_dsa_sign_random(out = a0, out_len = a1, used = a2,
key = a3, key_len = a4, p_len = a5, q_len = a6, digest = a7, digest_len,
rand, rand_len, scratch, scratch_len)`, the last five on the stack. `RL`: a
call's public data (`rlOf`), `Ctx`: what holds in the frame's body: the
registers `entry` sets, the saved registers and the callee's arguments in
the frame, and the key, the digest and the tape unchanged. A change of
memory in `out`, `scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev rsStack : Nat := 192

/-- The arguments on the stack. -/
abbrev rsStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- The result `randomSignBytes` gives, on entry. -/
def rsRes (s : State) : Spec.Dsa.RandomSignResult :=
  Spec.Dsa.randomSignBytes (s.gpr .a5).toNat (s.gpr .a6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)

/-- `vg_dsa_sign_random`, on the registers and the stack. -/
def rsContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let used : Region := ⟨s.gpr .a2, 8⟩
    let key : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let dg : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let rnd : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 rsStack, rsStack⟩
    rsStack ≤ s.sp.toNat ∧ s.sp.toNat + 8 * 5 ≤ 2 ^ 64 ∧
      s.rd = [key, dg, rnd, rsStackArgs s] ∧ s.wr = [out, used, scr] ∧
      out.Disjoint used ∧ out.Disjoint key ∧ out.Disjoint dg ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧
      out.Disjoint (rsStackArgs s) ∧ used.Disjoint key ∧ used.Disjoint dg ∧ used.Disjoint rnd ∧
      used.Disjoint scr ∧ used.Disjoint (rsStackArgs s) ∧ key.Disjoint scr ∧ dg.Disjoint scr ∧
      rnd.Disjoint scr ∧ scr.Disjoint (rsStackArgs s) ∧
      stk.Disjoint out ∧ stk.Disjoint used ∧ stk.Disjoint key ∧ stk.Disjoint dg ∧ stk.Disjoint rnd ∧
      stk.Disjoint scr ∧ stk.Disjoint (rsStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a5).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a4).toNat = 3 * (s.gpr .a5).toNat + 2 * (s.gpr .a6).toNat ∧
      Spec.Dsa.randomSignScratchWords (s.gpr .a5).toNat ≤ (stackArg s 4).toNat ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = (rsRes s).status ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
        (rsRes s).signature.getD (List.replicate (s.gpr .a1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a2) 1 = [BitVec.ofNat 64 (rsRes s).used]
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
      stackArg s₁ 4 = stackArg s₂ 4 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .a5).toNat (s₁.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat) ++ [(rsRes s₁).status, (rsRes s₁).used] ++
          (rsRes s₁).trace =
      Spec.Dsa.publicBytesLeak (s₂.gpr .a5).toNat (s₂.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat) ++ [(rsRes s₂).status, (rsRes s₂).used] ++
          (rsRes s₂).trace

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
  ⟨s.sp, s.gpr .a0, s.gpr .a2, s.gpr .a3, s.gpr .a7, stackArg s 1, stackArg s 3, (s.gpr .a5).toNat,
    (s.gpr .a6).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat, (stackArg s 4).toNat⟩

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
  spTop : L.sp.toNat + 40 ≤ 2 ^ 64
  sp16 : L.sp.toNat % 16 = 0
  alU : L.used.toNat % 8 = 0
  alS : L.scr.toNat % 8 = 0
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
    dFO, dFU, dFK, dFD, dFR, dFS, -, nO, nU, nK, nD, nR, nS, lv, hol, hkl, hsw, alU, alS, sp16⟩ := h
  simp only [Spec.Dsa.randomSignScratchWords, Spec.Dsa.scratchWords] at hsw
  have e4 : 2 * (s.gpr .a6).toNat = (s.gpr .a1).toNat := hol.symm
  have e7 : 3 * (s.gpr .a5).toNat + (s.gpr .a1).toNat = (s.gpr .a4).toNat := by omega
  refine ⟨lv, hsw, hF, hT, sp16, alU, alS, ?_, nU, ?_, nD, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
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

theorem fal : L.F.toNat % 8 = 0 := by
  have := hL.F_toNat; have := hL.spF; have := hL.sp16; simp only [frameBytes] at *; omega

omit hL in
/-- A range of the frame is apart from a region apart from the frame. -/
theorem frame_disj {r : Region} (hd : L.frR.Disjoint r) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off L.F d, n⟩ : Region).Disjoint r :=
  hd.sub_left (VG.Offset.sub_base _ h)

end RL.Ok

/-- The frame's region. -/
abbrev frameR (s₀ : State) : Region := ⟨s₀.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩

/-- In the frame's body. -/
structure Ctx (L : RL) (s₀ : State) (t : State) : Prop where
  sp : t.sp = L.F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR s₀ :: s₀.wr
  s1 : t.gpr .s1 = L.key
  s2 : t.gpr .s2 = lens L.pl L.ql
  s3 : t.gpr .s3 = L.rand
  s4 : t.gpr .s4 = BitVec.ofNat 64 L.rl
  sav : ∀ i < 12, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (cs i)
  ra : t.mem.readW (off L.F (oSave + 96)) 64 = s₀.gpr .ra
  a0 : t.mem.readW (off L.F 0) 64 = BitVec.ofNat 64 L.dl
  a1 : t.mem.readW (off L.F 8) 64 = L.scr
  a2 : t.mem.readW (off L.F 16) 64 = BitVec.ofNat 64 L.sl
  out : t.mem.readW (off L.F oOut) 64 = L.out
  used : t.mem.readW (off L.F oUsed) 64 = L.used
  dig : t.mem.readW (off L.F oDig) 64 = L.dig
  key : Spec.Rsa.bytesAt t.mem L.key L.kl = Spec.Rsa.bytesAt s₀.mem L.key L.kl
  digB : Spec.Rsa.bytesAt t.mem L.dig L.dl = Spec.Rsa.bytesAt s₀.mem L.dig L.dl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.s1, .s2, .s3, .s4]

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
  simp only [frameBytes] at hF
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
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.s1,
    (hg _ (by decide)).trans h.s2, (hg _ (by decide)).trans h.s3, (hg _ (by decide)).trans h.s4,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega) (by simp only [oSave, oNonce]; omega)).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.ra, (fw _ (by decide) (by decide)).trans h.a0,
    (fw _ (by decide) (by decide)).trans h.a1, (fw _ (by decide) (by decide)).trans h.a2,
    (fw _ (by decide) (by decide)).trans h.out, (fw _ (by decide) (by decide)).trans h.used,
    (fw _ (by decide) (by decide)).trans h.dig, ?_, ?_, ?_⟩
  · refine (bytes_frame hf (fun r hr => ?_) (by have := hL.nwKey; omega)).trans h.key
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.dl)).trans h.digB
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

end VG.Proof.Dsa.RISCV64.RS
