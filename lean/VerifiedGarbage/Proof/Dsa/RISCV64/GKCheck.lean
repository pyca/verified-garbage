module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.RISCV64.RSEntry
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCtx
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate
public import VerifiedGarbage.Spec.Dsa.Generate

/-! ### `Dsa.RISCV64.GKEntry`, which this module and modules that import it used -/

section

/-! ### `Dsa.RISCV64.GKCtx`, which this module and modules that import it used -/

section

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
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem F_toNat : L.F.toNat = L.sp.toNat - frameBytes := by
  have h1 := hL.spF
  have h2 := L.sp.isLt
  simp only [GL.F, frameBytes] at h1 ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [h1]

theorem fnw : L.F.toNat + frameBytes ≤ 2 ^ 64 := by
  have := hL.F_toNat; have := hL.spF; have := hL.spTop; omega_arith

theorem fal : L.F.toNat % 8 = 0 := by
  have := hL.F_toNat; have := hL.spF; have := hL.sp16; simp only [frameBytes] at *; omega_arith

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
      · exact VG.Offset.disjoint L.F (by simp only [oNonce] at hn ⊢; omega_using [hn]) (by simp only [frameBytes] at hd; omega_using [hd])
          (by simp only [oNonce]; omega_using [])) (by decide)
  have nr : ∀ {A : Addr} {k : Nat}, L.frR.Disjoint ⟨A, k⟩ → (⟨A, k⟩ : Region).Disjoint L.nR := fun hd =>
    (GL.Ok.frame_disj hd (d := oNonce) (n := 32) (by decide)).symm
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.s1,
    (hg _ (by decide)).trans h.s2, (hg _ (by decide)).trans h.s3, (hg _ (by decide)).trans h.s4,
    (hg _ (by decide)).trans h.s6,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave, oNonce]; omega_using [])).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.ra, (fw _ (by decide) (by decide)).trans h.a0,
    (fw _ (by decide) (by decide)).trans h.out, (fw _ (by decide) (by decide)).trans h.used, ?_, ?_⟩
  · refine (bytes_frame hf (fun r hr => ?_) (by have := hL.nwPar; omega_using [this])).trans h.par
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

end

end

/-!
# DSA key generation on RISC-V: the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Entry.lean`). `entry_ok`: in
the frame, `entry` saves `s0`–`s11` and `ra`, keeps `out` and `used` in the
frame, the domain, the lengths, the tape, its length and `scratch` in
`s1`–`s4` and `s6`, `vg_dsa_derive_key`'s argument on the stack
(`scratch_len`) in the frame, `s5 := 0`, and zeroes the nonce (`Entered`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (frameR lens_entry word_wW)

/-- The frame contains its offsets. -/
theorem frameR_contains {L : GL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat}
    (h : d + n ≤ frameBytes) : (frameR s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp]
  exact VG.Offset.contains_base _ h (by simp only [frameBytes] at h; omega_using [h])

/-- The frame's offsets past it are the stack pointer's. -/
theorem F_add (L : GL) (d : Nat) : off L.F (frameBytes + d) = L.sp + BitVec.ofNat 64 d := by
  simp only [off, GL.F]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The octets of a region apart from the frame are kept by a change within it. -/
theorem bytes_outside {L : GL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : k ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (.inr ?_)
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega_using [hi]) (by omega_using [hk, hi])
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- A word of a region apart from the frame is kept by a change within it. -/
theorem readW_outside {L : GL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : 8 ≤ k) (hk' : k ≤ 2 ^ 64) : m'.readW A 64 = m.readW A 64 := by
  refine Mem.readW_congr fun i hi => ho _ (.inr ?_)
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega) (by omega_using [hi])
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) : Scr t (off L.F oNonce) 32 := by
  have hF := hL.fnw
  have ha := hL.fal
  simp only [frameBytes] at hF
  refine ⟨⟨(frameR s₀).base, oNonce, frameBytes, by rw [hw]; exact List.mem_cons_self .., ?_, by decide,
    by decide⟩, ?_, ?_⟩
  · simp only [hsp]
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [hF]
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [ha]

/-- A word of the frame is writable and aligned. -/
theorem frame_word {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) {d : Nat} (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) :
    InRegions t.wr (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 := by
  have hF := hL.fnw
  have ha := hL.fal
  refine ⟨⟨_, by rw [hw]; exact List.mem_cons_self .., frameR_contains hL hsp hd⟩, ?_⟩
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by simp only [frameBytes] at hd; omega_using [hd])]
  simp only [frameBytes] at hF hd
  omega_using [h8, ha]

/-- What `entry` leaves. -/
structure Entered (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : gkContract.pre s₀) :
    WP isa (.block entry) (allocd frameBytes s₀) (Entered (glOf s₀) s₀) := by
  obtain hL := glOf_ok h
  generalize hLd : glOf s₀ = L at hL
  obtain hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  have hspT := hL.spTop
  have hsp16 := hL.sp16
  obtain hE : (allocd frameBytes s₀).sp = L.F := by simp only [allocd, hsp]
  have hwA : (allocd frameBytes s₀).wr = frameR s₀ :: s₀.wr := rfl
  obtain hsw : SaveW (allocd frameBytes s₀) L.F := fun i hi =>
    frame_word hL hsp hwA (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave]; omega_using [])
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hsw) fun t₁ h₁ => ?_
  -- The call's data.
  obtain eo : s₀.gpr .a0 = L.out := by rw [← hLd]; rfl
  obtain eu : s₀.gpr .a2 = L.used := by rw [← hLd]; rfl
  obtain ek : s₀.gpr .a3 = L.par := by rw [← hLd]; rfl
  obtain ed : s₀.gpr .a7 = L.rand := by rw [← hLd]; rfl
  obtain el : s₀.gpr .a6 <<< 16 + s₀.gpr .a5 = lens L.pl L.ql := by
    rw [lens_entry _ _ (by have := hL.ql; rw [← hLd] at this; simp only [glOf] at this; omega_using [this])]
    rw [← hLd]; rfl
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a1 : stackArg s₀ 1 = L.scr := by rw [← hLd]; rfl
  obtain a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain hr : ∀ r, r ≠ .t0 → t₁.gpr r = s₀.gpr r := fun r h0 => h₁.others r h0
  obtain o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    h₁.out.mono (by omega_using []) (by simp only [oSave, frameBytes]; omega_using [])
  obtain fw := fun (d : Nat) (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) => frame_word hL hsp (t := t₁)
    (by rw [h₁.wr]; rfl) hd h8
  obtain ⟨w64, l64⟩ := fw 64 (by decide) (by decide)
  obtain ⟨w72, l72⟩ := fw 72 (by decide) (by decide)
  obtain ⟨w0, l0⟩ := fw 0 (by decide) (by decide)
  rw [show ([.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .addi .s1 .a3 0, .shift .sll .d .s2 .a6 16,
      .add .s2 .s2 .a5, .addi .s3 .a7 0, .addSp .t6 frameBytes, .load .d .s4 .t6 0, .load .d .s6 .t6 8,
      .load .d .t1 .t6 16, .store .d .t1 .t0 0, .li .s5 0] : List Instr) =
    [.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .addi .s1 .a3 0, .shift .sll .d .s2 .a6 16,
      .add .s2 .s2 .a5, .addi .s3 .a7 0] ++ [.addSp .t6 frameBytes, .load .d .s4 .t6 0, .load .d .s6 .t6 8,
      .load .d .t1 .t6 16, .store .d .t1 .t0 0, .li .s5 0] from rfl, WP.block_append_iff]
  refine WP.mono (wp_sp (WP.keep [.s1, .s2, .s3] (Q := fun t =>
    t.gpr .s1 = L.par ∧ t.gpr .s2 = lens L.pl L.ql ∧ t.gpr .s3 = L.rand ∧
      t.mem = (t₁.mem.writeW (off L.F oOut) L.out).writeW (off L.F oUsed) L.used)
    (by
      brun [h₁.t0, hr .a0 (by decide), hr .a2 (by decide), hr .a3 (by decide), hr .a5 (by decide),
        hr .a6 (by decide), hr .a7 (by decide), eo, eu, ek, ed, el, oOut, oUsed, w64, l64, w72, l72,
        exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨b1, b2, b3, bm⟩, k₂⟩, sp₂⟩ => ?_
  obtain ⟨_, _, hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstk, _⟩ := h
  obtain hrd' : gkStackArgs s₀ ∈ s₀.rd := by rw [hrd]; simp
  obtain o₂ : Outside L.F 0 frameBytes s₀.mem t₂.mem := by
    rw [bm]
    refine o₁.trans (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_).trans
      ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_)) <;> decide
  obtain hstk' : L.frR.Disjoint (gkStackArgs s₀) := by
    simpa only [GL.frR, GL.F, hsp, show frameBytes = gkStack from rfl] using hstk
  obtain hsa0 : stackArgAddr s₀ 0 = L.sp := by simp only [stackArgAddr, hsp]; exact BitVec.add_zero _
  obtain sw : ∀ i < 3, t₂.mem.readW (off L.F (192 + 8 * i)) 64 = stackArg s₀ i ∧
      InRegions (t₂.rd ++ t₂.wr) (off L.F (192 + 8 * i)) 8 ∧
      (off L.F (192 + 8 * i)).toNat % 8 = 0 := by
    intro i hi
    rw [show 192 + 8 * i = frameBytes + 8 * i from rfl, F_add]
    obtain hsub : Region.Sub ⟨L.sp + BitVec.ofNat 64 (8 * i), 8⟩ (gkStackArgs s₀) := by
      simp only [gkStackArgs, hsa0]; exact VG.Offset.sub_base _ (by omega_using [hi])
    refine ⟨?_, ⟨_, List.mem_append_left _ (by rw [k₂.2.1, h₁.rd]; exact hrd'), ?_⟩, ?_⟩
    · rw [readW_outside o₂ (hstk'.sub_right hsub) (by omega_using []) (by omega_using [])]
      simp only [stackArg, stackArgAddr, hsp]
    · simp only [gkStackArgs, hsa0]; exact VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_using [hi])]; omega_using [hsp16]
  obtain ⟨r0, i0, al0⟩ := sw 0 (by decide)
  obtain ⟨r1, i1, al1⟩ := sw 1 (by decide)
  obtain ⟨r2, i2, al2⟩ := sw 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at r0 i0 al0 r1 i1 al1 r2 i2 al2
  have hF192 : L.F + BitVec.ofNat 64 192 = off L.F 192 := rfl
  obtain sp₂' : t₂.sp = L.F := by rw [sp₂, h₁.sp, hE]
  obtain t0₂ : t₂.gpr .t0 = L.F := by rw [k₂.1 .t0 (by decide), h₁.t0]
  have wr₂ : t₂.wr = t₁.wr := k₂.2.2
  rw [← wr₂] at w0
  refine WP.mono (wp_sp (WP.keep [.t6, .s4, .s6, .t1, .s5] (Q := fun t =>
    t.gpr .s4 = BitVec.ofNat 64 L.rl ∧ t.gpr .s6 = L.scr ∧ t.gpr .s5 = BitVec.ofNat 64 0 ∧
      t.mem = t₂.mem.writeW (off L.F 0) (BitVec.ofNat 64 L.sl))
    (by
      brun [exec_addSp (show 192 < 2048 by decide), exec_li_zero, sp₂', t0₂, hF192, frameBytes, r0, i0, al0,
        r1, i1, al1, r2, i2, al2, a0, a1, a2, w0, l0]
      rfl) (by decide) (by rfl))) fun t₃ ⟨⟨⟨c4, c6, c5, cm⟩, k₃⟩, sp₃⟩ => ?_
  obtain sp₃' : t₃.sp = L.F := by rw [sp₃, sp₂']
  obtain wr₃ : t₃.wr = frameR s₀ :: s₀.wr := by rw [k₃.2.2, wr₂, h₁.wr]; rfl
  refine WP.mono (wp_sp (clearNonce_ok t₃ hF sp₃' (scr_nonce hL hsp wr₃)))
    fun t₄ ⟨⟨⟨_, nz, o₄⟩, k₄⟩, sp₄⟩ => ?_
  -- Memory.
  obtain o₃ : Outside L.F 0 8 t₂.mem t₃.mem := by
    rw [cm]; exact writeW_outside _ _ _ (by decide)
  obtain o₂' : Outside L.F 64 16 t₁.mem t₂.mem := by
    rw [bm]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  obtain o₁₄ : Outside L.F 0 88 t₁.mem t₄.mem :=
    (o₂'.mono (Nat.zero_le _) (by decide)).trans ((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce]; omega_using [])))
  obtain o₀₄ : Outside L.F 0 frameBytes s₀.mem t₄.mem :=
    o₂.trans (((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce, frameBytes]; omega_using []))))
  obtain w₄ : ∀ d, 64 ≤ d → d + 8 ≤ 88 → t₄.mem.readW (off L.F d) 64 = t₂.mem.readW (off L.F d) 64 :=
    fun d hd hd' => (o₄.word (by simp only [oNonce]; omega_using [hd]) (by omega_using [hd'])).trans
      (o₃.word (by omega_using [hd]) (by omega_using [hd']))
  obtain g2 : ∀ r, r ∉ [Reg.t6, .s4, .s6, .t1, .s5] → r ∉ [Reg.t0, .t1] →
      t₄.gpr r = t₂.gpr r := fun r h h' => (k₄.1 r h').trans (k₃.1 r h)
  refine ⟨⟨by rw [sp₄, sp₃'], by rw [k₄.2.1, k₃.2.1, k₂.2.1, h₁.rd]; rfl,
    by rw [k₄.2.2, wr₃], by rw [g2 _ (by decide) (by decide), b1], by rw [g2 _ (by decide) (by decide), b2],
    by rw [g2 _ (by decide) (by decide), b3], by rw [k₄.1 _ (by decide), c4], by rw [k₄.1 _ (by decide), c6],
    fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [k₄.1 _ (by decide), c5], nz⟩
  · exact (o₁₄.word (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [hi])).trans (h₁.saved i hi)
  · exact (o₁₄.word (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [])).trans h₁.savedRa
  · rw [show t₄.mem.readW (off L.F 0) 64 = t₃.mem.readW (off L.F 0) 64 from
      o₄.word (d := 0) (by simp only [oNonce]; omega_using []) (by omega_using []), cm, Mem.readW_writeW_self64]
  · rw [w₄ oOut (by decide) (by decide), bm, word_wW _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [w₄ oUsed (by decide) (by decide), bm, Mem.readW_writeW_self64]
  · exact bytes_outside o₀₄ hL.dFK (by have := hL.nwPar; omega_using [this])
  · exact bytes_outside o₀₄ hL.dFR (by have := hL.nwRand; omega_using [this])
end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# DSA key generation on RISC-V: the check of the domain

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Check.lean`). `checkArgs` passes
the domain, its length, the lengths and `scratch` with `scratch_len` (from
the frame), so `vg_dsa_check_parameters`'s contract on the registers
(`pcContract`) holds; `check_ok` runs the call by `WP.call` from
`checkParameters_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The regions on entry, by the call's data. -/
theorem regions_eq {s₀ : State} (h : gkContract.pre s₀) :
    s₀.rd = [(glOf s₀).parR, (glOf s₀).randR, gkStackArgs s₀] ∧
      s₀.wr = [(glOf s₀).outR, (glOf s₀).usedR, (glOf s₀).scrR] := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, hkl, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hrd]; simp only [glOf, GL.parR, GL.randR, GL.kl, hkl]
  · rw [hwr]; simp only [glOf, GL.outR, GL.usedR, GL.scrR, GL.ol, hol]

/-- A word of the frame is readable and aligned. -/
theorem Ctx.word {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) (hc : Ctx L s₀ t) {d : Nat}
    (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) :
    InRegions (t.rd ++ t.wr) (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 :=
  have ⟨⟨r, hr, hc'⟩, ha⟩ := frame_word hL hsp hc.wr hd h8
  ⟨⟨r, List.mem_append_right _ hr, hc'⟩, ha⟩

/-- The registers `checkArgs` writes. -/
def checkRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .t3]

/-- The state after `checkArgs`. -/
structure CArgs (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  a0 : t.gpr .a0 = L.par
  a1 : t.gpr .a1 = BitVec.ofNat 64 L.kl
  a2 : t.gpr .a2 = BitVec.ofNat 64 L.pl
  a3 : t.gpr .a3 = BitVec.ofNat 64 L.ql
  a4 : t.gpr .a4 = L.scr
  a5 : t.gpr .a5 = BitVec.ofNat 64 L.sl

theorem checkArgs_ok {L : GL} {s₀ t : State} (hL : L.Ok) (hsp₀ : s₀.sp = L.sp) (hc : Ctx L s₀ t) :
    WP isa (.block checkArgs) t fun t' => (CArgs L s₀ t' ∧ t'.mem = t.mem ∧ Keep checkRegs t t') ∧
      t'.sp = t.sp := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ checkRegs := by decide
  obtain ⟨i0, l0⟩ := hc.word hL hsp₀ (d := 0) (by decide) (by decide)
  have o0 := hc.a0
  simp only [off, BitVec.add_zero] at i0 l0 o0
  have e1 := lenP_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
  have e2 := lenQ_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
  refine WP.mono (wp_sp (WP.keep checkRegs (Q := fun t' => t'.gpr .a0 = L.par ∧
    t'.gpr .a1 = BitVec.ofNat 64 L.kl ∧ t'.gpr .a2 = BitVec.ofNat 64 L.pl ∧ t'.gpr .a3 = BitVec.ofNat 64 L.ql ∧
    t'.gpr .a4 = L.scr ∧ t'.gpr .a5 = BitVec.ofNat 64 L.sl ∧ t'.mem = t.mem) ?_ (by decide) (by rfl)))
    fun t' ⟨⟨⟨a0, a1, a2, a3, a4, a5, am⟩, k⟩, hsp⟩ =>
      ⟨⟨⟨hc.step hL hsp k.2.1 k.2.2 (fun r hr => k.1 r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a0, a1, a2, a3, a4, a5⟩, am, k⟩, hsp⟩
  unfold checkArgs
  brun [lenP, lenQ, hc.s1, hc.s2, hc.s6, e1, e2, hc.sp, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero,
    i0, l0, o0, ← BitVec.ofNat_add]
  congr 1; simp only [GL.kl]; omega_using []

/-- `vg_dsa_check_parameters`'s contract on the registers holds when it is called. -/
theorem check_pre {s₀ t : State} (h : gkContract.pre s₀) (ha : CArgs (glOf s₀) s₀ t) :
    pcContract.pre (t.callEntry.withRegions [(glOf s₀).parR] [(glOf s₀).scrR]) := by
  have hL := glOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have hsw := hL.sw
  have hsl := hL.sl
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hsp16 : (glOf s₀).F.toNat % 16 = 0 := by
    have h1 := hL.F_toNat; have h2 := hL.spF; have h3 := hL.sp16; simp only [frameBytes] at h1 h2; omega_using [h1, h3]
  unfold pcContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ha.ctx.sp]
  rw [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, tn _ (by simp only [GL.kl]; omega_using [hp, hq]),
    tn (glOf s₀).pl (by omega_using [hp]), tn (glOf s₀).ql (by omega_using [hq]), tn _ hsl]
  exact ⟨rfl, rfl, hL.dKS, hL.nwPar, hL.nwScr, hL.lv, rfl, by simp only [Spec.Dsa.scratchWords]; omega_using [hsw],
    hL.alS, hsp16⟩

theorem check_cov {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    Covers ([(glOf s₀).parR] ++ [(glOf s₀).scrR]) (t.rd ++ t.wr) ∧ Covers [(glOf s₀).scrR] t.wr := by
  obtain ⟨hrd, hwr⟩ := regions_eq h
  refine ⟨VG.Covers.of_mem fun r hr => ?_, VG.Covers.of_mem fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hc.wr, hwr]; simp

/-- Whether the domain is valid, on entry. -/
abbrev chkOf (s₀ : State) : Bool :=
  Spec.Dsa.checkParametersBytes (glOf s₀).pl (glOf s₀).ql (Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl)

/-- What the call leaves. -/
structure Checked (L : GL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame [L.scrR] t.mem t'.mem
  a0 : ((t'.gpr .a0).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem check_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : CArgs (glOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_check_parameters" Impl.Dsa.RISCV64.Params.checkParameters) t
      (Checked (glOf s₀) s₀ t) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := check_cov h hc
  refine WP.call (k := pcContract) checkParameters_correct (check_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, ?_⟩
  have hpost' := hpost
  simp only [pcContract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem] at hpost'
  have e4 : (BitVec.ofNat 64 (glOf s₀).kl).toNat = (glOf s₀).kl := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [GL.kl]; omega_using [hp, hq])]
  have e5 : (BitVec.ofNat 64 (glOf s₀).pl).toNat = (glOf s₀).pl := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hp])]
  have e6 : (BitVec.ofNat 64 (glOf s₀).ql).toNat = (glOf s₀).ql := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hq])]
  simp only [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), ha.a0, ha.a1, ha.a2,
    ha.a3, e4, e5, e6, hc.par] at hpost'
  exact hpost'

end VG.Proof.Dsa.RISCV64.GK
