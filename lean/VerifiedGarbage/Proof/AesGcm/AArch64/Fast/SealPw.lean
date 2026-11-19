module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.AArch64.CalleePw
public import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified

/-! ### `AesGcm.AArch64.Fast.Verified`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal`, with the path for TLS records where PMULL is there

Untrusted: everything here is checked by Lean. `sealCode v` is `seal` with
the path for TLS records (`Impl/AesGcm/AArch64/Fast.lean`) for the
implementations whose CPUs have PMULL (`GhashImpl.pmull`), which the path
runs inline, and `seal` otherwise; both are `Verified` against `seal`'s
contract (`sealCode_framed`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-- `vg_aes_gcm_seal` for the implementations `v`. -/
def sealCode (v : GcmImpl) : Prog isa :=
  if v.gh.pmull then Impl.AesGcm.AArch64.Fast.«seal» v.callees else «seal» v.callees

theorem fastSealWithE_keepsV (v : GcmImpl) {k : Nat} (hk : k = 8 ∨ k = 16) {cl : Prog isa}
    (hcl : cl.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Fast.sealWithE v.callees k cl).allInstrs keepsV = true := by
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.sealWithE, Impl.AesGcm.AArch64.Fast.runWithP, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT, Impl.AesGcm.AArch64.Tail.cryptAlT,
    Impl.AesGcm.AArch64.Tail.crSeg2T, Impl.AesGcm.AArch64.Tail.crTailT, crSeg2, crTail,
    sealRest, j0, j0hash, oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.gh.keepsV, hcl] <;> decide +kernel

theorem fastSealWith_keepsV (v : GcmImpl) {gh : Fn} (hgh : gh.code.allInstrs keepsV = true) :
    (Impl.AesGcm.AArch64.Fast.sealWith v.callees gh).allInstrs keepsV = true :=
  fastSealWithE_keepsV v (.inl rfl) (by simp only [Code.allInstrs, hgh])

theorem fastSeal_keepsV (v : GcmImpl) : (Impl.AesGcm.AArch64.Fast.«seal» v.callees).allInstrs keepsV = true :=
  fastSealWith_keepsV v v.gh.keepsV

theorem fastSeal_correct {Wn : Nat} (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (s : State) (hs : (sealAArch64 Wn).pre s) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.«seal» v.callees) s t s' ∧ abiPreserved s s' ∧
      (sealAArch64 Wn).post s s' :=
  WP.withPreservedV (Fast.seal_wp v hMK hs) (fastSeal_keepsV v)

theorem fastSeal_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.«seal» v.callees)
      (Proof.AesGcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (fastSeal_correct v hMK) (Fast.seal_ct v hMK) (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Proof.AesGcm.sealRoundsPost, sealAArch64, sealPre, sealPreX, List.append_nil, onePub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem sealCode_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (sealCode v) (Proof.AesGcm.sealScratchContract AArch64.abi) := by
  unfold sealCode
  split
  · exact fastSeal_verified v hMK
  · exact seal_verified v

theorem sealCode_framed (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v))
      (Proof.AesGcm.sealRoundsContract AArch64.abi 2576) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre AArch64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2576)
    (sealCode_verified v hMK) (by decide) (by decide) (sealPre_local _) (sealPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre

open VG.Proof.AesGcm.AArch64.Gather in
/-- `sealWithE` has no frames of its own. -/
theorem fastSealWithE_depth0 (v : GcmImpl) {k : Nat} (hk : k = 8 ∨ k = 16) {cl : Prog isa}
    (hcl : cl.aarch64Depth = 0) : (Impl.AesGcm.AArch64.Fast.sealWithE v.callees k cl).aarch64Depth = 0 := by
  rcases hk with rfl | rfl <;>
  simp only [Impl.AesGcm.AArch64.Fast.sealWithE, Impl.AesGcm.AArch64.Fast.runWithP, Impl.AesGcm.AArch64.Fast.front,
    Impl.AesGcm.AArch64.Fast.cond, Impl.AesGcm.AArch64.Fast.padMul, Impl.AesGcm.AArch64.Fast.padMulT, Impl.AesGcm.AArch64.Tail.cryptAlT,
    Impl.AesGcm.AArch64.Tail.crSeg2T, Impl.AesGcm.AArch64.Tail.crTailT, crSeg2, crTail, sealRest, j0, j0hash,
    oneAad, absorbAl, encBody, fo, textAbs, finBody, tag, crypt, crSeg1, ctrCall, ghCall, absorb, absSeg1, absTail,
    minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.aarch64Depth,
    depth_of_noFrames v.ctr.noFrames, depth_of_noFrames v.gh.noFrames, hcl] <;> decide

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `sealWith v gh`, in its frame of 2576 bytes, use at most those. -/
theorem fastSealWith_depth (v : GcmImpl) {gh : Fn} (hgh : gh.code.noFrames = true) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2576 1
      (Impl.AesGcm.AArch64.Fast.sealWith v.callees gh)).aarch64Depth ≤ 2576 := by
  simp only [Impl.StackScratch.AArch64.withStackArgScratch, Impl.AesGcm.AArch64.Fast.sealWith, Code.aarch64Depth,
    Instr.frameUnits, fastSealWithE_depth0 v (.inl rfl) (cl := .call gh.name gh.code)
      (by simp only [Code.aarch64Depth, depth_of_noFrames hgh])]
  decide

open VG.Proof.AesGcm.AArch64.Gather in
/-- The frames of `sealCode v`, in its frame of 2576 bytes, use at most those. -/
theorem sealCode_depth (v : GcmImpl) :
    16 * (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)).aarch64Depth ≤ 2576 := by
  unfold sealCode
  split
  · exact fastSealWith_depth v v.gh.noFrames
  · exact seal_depth v

end VG.Proof.AesGcm.AArch64

end

end

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal_with_powers`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_with_powers`
is `seal` with `pw` a stack argument after `tag` (so `work` one slot further,
`Fast.sealWithPw`), its whole blocks on the path for TLS records hashed by
`vg_ghash_with_powers` (`GhashWithImpl`), called with `pw` loaded from the
stack (`Fast.pwCall 8`), unless at most one block is left, which
`vg_ghash` hashes (`Fast.pwSel 8`). The proofs of `seal` hold for any such call
(`sealWithE_wp`, `sealWithE_ct`), given `pw` readable beside the other
regions (`sealPwN`): the call finds the powers there, as the code before it
writes only the working space and the text (`gwCall_of`).

The shared contract lists `pw` before the stack arguments; the proofs read it
after them (`narrow`), and the code runs as it does with either order
(`Exec.widen`), with the same trace.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

/-- The powers' buffer, the stack argument 1. -/
abbrev pwR (s : State) : Region := ⟨stackArg s 1, 128⟩

/-- What `vg_aes_gcm_seal_with_powers` needs, on the regions its proofs run
on: `sealPreXW 2`, with `pw` readable, apart from the text and the working
space, and holding the powers of the hash subkey. -/
def sealPwN (Wn : Nat) (s : State) : Prop :=
  sealPreXW 2 [pwR s] s ∧ (pwR s).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ ∧
    (pwR s).Disjoint ⟨stackArg s 2, Wn⟩ ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 1) (Spec.Gcm.ctxH s.mem (s.gpr .x0))

/-- What `vg_aes_gcm_seal_with_powers` needs: `sealPreXW 2`, with `pw`
readable before the stack arguments, holding the powers. -/
def sealPwW (Wn : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let pw : Region := pwR s
  let work : Region := ⟨stackArg s 2, Wn⟩
  s.rd = [ctx, nonce, aad, pw, args s 3] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧ pw.Disjoint data ∧
    data.Disjoint work ∧ data.Disjoint (args s 3) ∧ tag.Disjoint work ∧ pw.Disjoint work ∧
    work.Disjoint (args s 3) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + Wn ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * 3 ≤ 2 ^ 64 ∧ rounds (s.gpr .x1) ∧
    Spec.Gcm.Powers8Repr s.mem (stackArg s 1) (Spec.Gcm.ctxH s.mem (s.gpr .x0))

/-- `vg_aes_gcm_seal_with_powers`. -/
def sealPwAArch64 : Contract isa where
  pre := sealPwW
  post := (sealAArch64 Wn).post
  pub := onePub 3

/-! ## The call of `vg_ghash_with_powers` -/

/-- At the call, with memory changed since the entry only in the working
space and the text: `pw` is at `[sp + 8]`, readable, apart from the
accumulator and the working space of the call, and holds the powers. -/
theorem gwCall_of {Wn : Nat} {σ s : State} {Y S : Addr} (hs : sealPwN Wn σ) (sY : Region.Sub ⟨Y, 16⟩ (workR Wn (stackArg σ 2)))
    (sS : Region.Sub ⟨S, 256⟩ (workR Wn (stackArg σ 2))) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (hsp : s.sp = σ.sp)
    (hf : Frame [workR Wn (stackArg σ 2), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem) :
    s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg σ 1 ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 ∧
      GhWCall s (σ.gpr .x0) Y S (stackArg σ 1) := by
  obtain ⟨hpx, pd, pw, rep⟩ := hs
  obtain ⟨ol, -, -, -⟩ := sealLay hpx
  have hrd₀ := hpx.1
  have hp' := hpx
  simp only [sealPreXW] at hp'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dda, -⟩ := hp'
  have hspA := ol.hsp 1 (by decide)
  have sA : Region.Sub ⟨σ.sp + BitVec.ofNat 64 8, 8⟩ (args σ 3) := by
    show Region.Sub ⟨σ.sp + BitVec.ofNat 64 8, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * 3⟩
    rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
    exact Offset.sub_base _ (by decide)
  refine ⟨?_, by rw [hrd, hwr, hsp]; exact hspA, ⟨?_, (pw.sub_right sY).symm, (pw.sub_right sS).symm, ?_⟩⟩
  · rw [hsp, hf.readW (r := ⟨σ.sp + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ol.args.sub_left sA
      · exact (dda.sub_right sA).symm) (by decide)]
    rfl
  · refine Covers.left (Covers.of_mem fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [hrd, hrd₀]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hH : Spec.Gcm.blockAt s.mem (σ.gpr .x0 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH σ.mem (σ.gpr .x0) :=
      blockAt_frame hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ol.ctx.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
        · exact ol.cd.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))
    rw [hH]
    exact Proof.AesGcm.powers8Repr_congr (fun i hi => hf.bytes (R := pwR σ) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact pw
        · exact pd) (show 128 ≤ 2 ^ 64 by decide) hi) rep

/-! ## On the regions of the proofs -/

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem sealPw_wp {Wn : Nat} {s : State} (hs : sealPwN Wn s) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    WP isa (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) s fun s' =>
      GprAbi s s' ∧ (sealAArch64 Wn).post s s' :=
  sealWithE_wp (w := 2) v _ hMK (.inr rfl) hs.1 fun _ _ _ _ _ hc sY sS hrd hwr hsp hf =>
    have q := gwCall_of hs sY sS hrd hwr hsp hf
    pwSel_call v g (k := 8) (by decide) q.1 q.2.1 hc q.2.2

theorem sealPw_correctN {Wn : Nat} (s : State) (hs : sealPwN Wn s) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      (sealAArch64 Wn).post s s' :=
  WP.withPreservedV (sealPw_wp v g hMK hs) (fastSealWithE_keepsV v (.inr rfl) (pwSel_keepsV v g (.inl rfl)))

theorem sealPw_ctN {Wn : Nat} :
    ConstantTime isa sealPwN Wn (onePub 3) (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) :=
  sealWithE_ct (w := 2) v _ hMK (.inr rfl) (extra := fun s => [pwR s]) (fun _ h => h.1)
    (fun p hc sY sS hrd hwr hsp hf =>
      have q := gwCall_of p sY sS hrd hwr hsp hf
      pwSel_call v g (k := 8) (by decide) q.1 q.2.1 hc q.2.2)
    fun {σ₁ σ₂ s₁ s₂ _ _ _ _} p₁ p₂ hq c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => by
      obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
      have e2 : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by decide)
      have e1 : stackArg σ₁ 1 = stackArg σ₂ 1 := qa 1 (by decide)
      obtain ⟨hP₁, hs₁, k₁⟩ := gwCall_of p₁ sY sS r₁ w₁ sp₁ f₁
      obtain ⟨hP₂, hs₂, k₂⟩ := gwCall_of p₂ (by rw [← e2]; exact sY) (by rw [← e2]; exact sS) r₂ w₂
        (sp₂.trans qsp) (by rw [← e2, ← q6, ← q7]; exact f₂)
      rw [← e1] at hP₂ k₂
      rw [← q0] at k₂
      exact pwSel_rel v g (.inl rfl) hP₁ hs₁ hP₂ hs₂ c₁ k₁ c₂ k₂ (sp₁.trans sp₂.symm)

end

/-! ## On the shared contract's regions -/

/-- The readable regions of the proofs: `pw` after the stack arguments. -/
def narrowRdP (s : State) : List Region :=
  [⟨s.gpr .x0, 256⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩, args s 3, pwR s]

/-- `s` with the readable regions of the proofs. -/
def narrowP (s : State) : State := s.withRegions (narrowRdP s) s.wr

theorem narrowP_pre {Wn : Nat} {s : State} (h : sealPwW Wn s) : sealPwN Wn (narrowP s) := by
  obtain ⟨-, hwr, cd, cw, nd, nw, ad, aw, dt, pd, dw, da, tw, pw, wa, b0, b2, b4, b6, b1, bsp, hr, rep⟩ := h
  exact ⟨⟨rfl, hwr, cd, cw, nd, nw, ad, aw, dt, dw, da, tw, wa, b0, b2, b4, b6, b1, bsp, hr⟩, pd, pw, rep⟩

theorem narrowP_covers {Wn : Nat} {s : State} (h : sealPwW Wn s) :
    Covers ((narrowP s).rd ++ (narrowP s).wr) (s.rd ++ s.wr) := by
  rw [show (narrowP s).rd = narrowRdP s from rfl, show (narrowP s).wr = s.wr from rfl, h.1]
  refine Covers.append (Covers.of_mem fun r hr => ?_) (Covers.refl _)
  simp only [narrowRdP, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

theorem narrowP_exec {Wn : Nat} {c : Prog isa} {s s₁ : State} {t : List Leak} (h : sealPwW Wn s)
    (he : Exec isa c (narrowP s) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (narrowP_covers h) (Covers.refl _)
  rwa [show (narrowP s).withRegions s.rd s.wr = s from rfl] at this

/-- A state satisfying `vg_aes_gcm_seal_with_powers`'s precondition: `sealSat`
with `pw` at `0x6000` (`[sp + 8]`) and `work` at `0x5000` (`[sp + 16]`). -/
def sealSatPw : State :=
  { sealSat with
    mem := fun a => if a = 0x8011 then 0x50 else if a = 0x8009 then 0x60 else 0
    rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 128⟩, ⟨0x8000, 24⟩] }

/-- `pw`'s bytes in `sealSatPw` are zero. -/
theorem sealSatPw_zero : ∀ i < 16 * 8, sealSatPw.mem (stackArg sealSatPw 1 + BitVec.ofNat 64 i) = 0 := by
  intro i hi
  have hP : stackArg sealSatPw 1 = 0x6000 := by decide
  rw [hP]
  show (if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8011 then 0x50
    else if (0x6000 : BitVec 64) + BitVec.ofNat 64 i = 0x8009 then 0x60 else 0) = 0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega)), ite_eq_right_of_eq_false _ _ (eq_false (by bv_omega))]

section
variable (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey)
include hMK

theorem sealPw_correct (s : State) (hs : sealPwAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) s t s' ∧ abiPreserved s s' ∧
      sealPwAArch64.post s s' := by
  obtain ⟨t, s₁, he, ha, hp⟩ := sealPw_correctN v g hMK _ (narrowP_pre hs)
  exact ⟨t, _, narrowP_exec hs he, ha, hp⟩

theorem sealPw_ct :
    ConstantTime isa sealPwAArch64.pre sealPwAArch64.pub (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨u₁, r₁, f₁, -⟩ := sealPw_correctN v g hMK _ (narrowP_pre h₁)
  obtain ⟨u₂, r₂, f₂, -⟩ := sealPw_correctN v g hMK _ (narrowP_pre h₂)
  rw [(Exec.det e₁ (narrowP_exec h₁ f₁)).1, (Exec.det e₂ (narrowP_exec h₂ f₂)).1]
  exact sealPw_ctN v g hMK _ _ _ _ _ _ (narrowP_pre h₁) (narrowP_pre h₂) hq f₁ f₂

theorem sealPw_verified :
    Verified AArch64.target (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn)
      (Proof.AesGcm.sealWithPowersScratchContract AArch64.abi) :=
  Verified.of_correct (sealPw_correct v g hMK) (sealPw_ct v g hMK)
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, Proof.AesGcm.sealWithPowersRoundsPost, Proof.AesGcm.sealRoundsPost,
          sealPwAArch64, sealPwW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, Proof.AesGcm.sealWithPowersRoundsPost, Proof.AesGcm.sealRoundsPost,
          sealPwAArch64, sealPwW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, Proof.AesGcm.sealWithPowersRoundsPost, Proof.AesGcm.sealRoundsPost,
          sealPwAArch64, sealPwW, pwR, sealAArch64, onePub, args, rounds, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := ⟨sealSatPw, by
        sig_pre [Proof.AesGcm.sealWithPowersScratchContract, Proof.AesGcm.sealWithPowersScratchSig,
          Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, AArch64.abi, AArch64.argRegs,
          AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop, sealSatPw, sealSat,
          stackArg, stackArgAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) sealSatPw_zero⟩ }

end

/-! ## With its working space on the stack -/

/-- `sealSatPw` with its stack arguments `tag` and `pw` only. -/
def sealFrameSatPw : State :=
  { sealSatPw with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x6000, 128⟩, ⟨0x8000, 16⟩],
                   wr := [⟨0x4000, 0⟩, ⟨0, 16⟩] }

theorem sealFrameSatPw_pre : ∃ s, (Proof.AesGcm.sealWithPowersRoundsContract AArch64.abi 2592).pre s := by
  refine ⟨sealFrameSatPw, ?_⟩
  sig_pre [Proof.AesGcm.sealWithPowersRoundsContract, Spec.Gcm.sealWithPowersSig, Spec.Gcm.sealSig, Spec.Gcm.withPowersParam,
    Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre, Proof.AesGcm.sealWithPowersRoundsPost, Proof.AesGcm.sealRoundsPost, AArch64.abi,
    AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop,
    List.cons_append, List.nil_append, sealFrameSatPw, sealSatPw, sealSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) sealSatPw_zero

theorem sealPw_framed (v : GcmImpl) (g : GhashWithImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn))
      (Proof.AesGcm.sealWithPowersRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Gcm.sealWithPowersSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealWithPowersPre AArch64.abi.ptrBits)
    (post := Proof.AesGcm.sealWithPowersRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (sealPw_verified v g hMK) (by decide) (by decide) (Proof.AesGcm.sealWithPowersPre_local _)
    (Proof.AesGcm.sealWithPowersPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.sealWithPowersPostOut_local _ vs m m₁ m₂ r hl) sealFrameSatPw_pre

end VG.Proof.AesGcm.AArch64.Fast
