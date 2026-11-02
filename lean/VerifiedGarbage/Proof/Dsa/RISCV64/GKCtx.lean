module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCtx
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on RISC-V: the contract on the registers, and the frame's state

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Contract.lean` and `Ctx.lean`).
`gkContract`: `vg_dsa_generate_key(out = a0, out_len = a1, used = a2,
params = a3, params_len = a4, p_len = a5, q_len = a6, rand = a7, rand_len,
scratch, scratch_len)`, the last three on the stack, with the 192 bytes of
stack below the stack pointer that its frame uses (the functions it calls
use none). `GL`: a call's public data (`glOf`); `Ctx`: what holds in the
frame's body: the registers `entry` sets, the saved registers, `out`,
`used` and `vg_dsa_derive_key`'s argument on the stack in the frame, and
the domain and the tape as on entry. A change of memory in `out`,
`scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (frameR bytes_frame)

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev gkStack : Nat := 192

/-- The arguments on the stack. -/
abbrev gkStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The result `generateKeyBytes` gives, on entry. -/
def gkRes (s : State) : Spec.Dsa.GenerateKeyResult :=
  Spec.Dsa.generateKeyBytes (s.gpr .a5).toNat (s.gpr .a6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)

/-- `vg_dsa_generate_key`, on the registers and the stack. -/
def gkContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let used : Region := ⟨s.gpr .a2, 8⟩
    let ps : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let rnd : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 gkStack, gkStack⟩
    gkStack ≤ s.sp.toNat ∧ s.sp.toNat + 8 * 3 ≤ 2 ^ 64 ∧
      s.rd = [ps, rnd, gkStackArgs s] ∧ s.wr = [out, used, scr] ∧
      out.Disjoint used ∧ out.Disjoint ps ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧
      out.Disjoint (gkStackArgs s) ∧ used.Disjoint ps ∧ used.Disjoint rnd ∧
      used.Disjoint scr ∧ used.Disjoint (gkStackArgs s) ∧ ps.Disjoint scr ∧
      rnd.Disjoint scr ∧ scr.Disjoint (gkStackArgs s) ∧
      stk.Disjoint out ∧ stk.Disjoint used ∧ stk.Disjoint ps ∧ stk.Disjoint rnd ∧
      stk.Disjoint scr ∧ stk.Disjoint (gkStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a5).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 3 * (s.gpr .a5).toNat + 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a4).toNat = 2 * (s.gpr .a5).toNat + (s.gpr .a6).toNat ∧
      Spec.Dsa.generationScratchWords (s.gpr .a5).toNat ≤ (stackArg s 2).toNat ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 1).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = (gkRes s).status ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
        (gkRes s).key.getD (List.replicate (s.gpr .a1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a2) 1 = [BitVec.ofNat 64 (gkRes s).used]
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat).map (·.toNat) ++
          [(gkRes s₁).status, (gkRes s₁).used] ++ (gkRes s₁).trace =
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat).map (·.toNat) ++
          [(gkRes s₂).status, (gkRes s₂).used] ++ (gkRes s₂).trace

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
  ⟨s.sp, s.gpr .a0, s.gpr .a2, s.gpr .a3, s.gpr .a7, stackArg s 1, (s.gpr .a5).toNat,
    (s.gpr .a6).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat⟩

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
  spTop : L.sp.toNat + 24 ≤ 2 ^ 64
  sp16 : L.sp.toNat % 16 = 0
  alU : L.used.toNat % 8 = 0
  alS : L.scr.toNat % 8 = 0
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
    dFO, dFU, dFK, dFR, dFS, -, nO, nU, nK, nR, nS, lv, hol, hkl, hsw, alU, alS, sp16⟩ := h
  simp only [Spec.Dsa.generationScratchWords] at hsw
  have e4 : 3 * (s.gpr .a5).toNat + 2 * (s.gpr .a6).toNat = (s.gpr .a1).toNat := hol.symm
  have e7 : 2 * (s.gpr .a5).toNat + (s.gpr .a6).toNat = (s.gpr .a4).toNat := hkl.symm
  refine ⟨lv, hsw, hF, hT, sp16, alU, alS, ?_, nU, ?_, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
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

theorem fal : L.F.toNat % 8 = 0 := by
  have := hL.F_toNat; have := hL.spF; have := hL.sp16; simp only [frameBytes] at *; omega

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
  wr : t.wr = frameR s₀ :: s₀.wr
  s1 : t.gpr .s1 = L.par
  s2 : t.gpr .s2 = lens L.pl L.ql
  s3 : t.gpr .s3 = L.rand
  s4 : t.gpr .s4 = BitVec.ofNat 64 L.rl
  s6 : t.gpr .s6 = L.scr
  sav : ∀ i < 12, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (cs i)
  ra : t.mem.readW (off L.F (oSave + 96)) 64 = s₀.gpr .ra
  a0 : t.mem.readW (off L.F 0) 64 = BitVec.ofNat 64 L.sl
  out : t.mem.readW (off L.F oOut) 64 = L.out
  used : t.mem.readW (off L.F oUsed) 64 = L.used
  par : Spec.Rsa.bytesAt t.mem L.par L.kl = Spec.Rsa.bytesAt s₀.mem L.par L.kl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.s1, .s2, .s3, .s4, .s6]

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : GL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
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
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.s1,
    (hg _ (by decide)).trans h.s2, (hg _ (by decide)).trans h.s3, (hg _ (by decide)).trans h.s4,
    (hg _ (by decide)).trans h.s6,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega) (by simp only [oSave, oNonce]; omega)).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.ra, (fw _ (by decide) (by decide)).trans h.a0,
    (fw _ (by decide) (by decide)).trans h.out, (fw _ (by decide) (by decide)).trans h.used, ?_, ?_⟩
  · refine (bytes_frame hf (fun r hr => ?_) (by have := hL.nwPar; omega)).trans h.par
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.RISCV64.GK
