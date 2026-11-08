module

public import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Dec
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Frame
import VerifiedGarbage.Proof.AesGcm.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Dec
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

/-!
# AES-GCM decryption out of place on x86: `vg_aes_gcm_open_to`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to` runs
`open`'s body (`Open.lean`) in a frame of 48 bytes of its own (`Open.openTo`):
the entry copies `open`'s arguments into it, the data being `src`, and `dst`
into the word at its `esp` (`frameArgs_ok`), and the body runs in the mode
out of place (`toMode`, `Dec.lean`): the data decrypted to `dst`, or `dst`
zeroed. With its working space as an argument, it is proven against the
contract the frame of `withStackScratch` needs (`openTo_verified`), and so,
in that frame, against `Proof.AesGcm.openToRoundsContract` (`openTo_framed`),
from which `Spec.Gcm.openToContract` follows (`Proof.AesGcm.openTo_keyed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.OpenTo

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Open
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)

/-! ## The mode out of place -/

/-- `open`'s body out of place: the data decrypted to `dst`, the word at
`esp`, and `dst` zeroed if the tag length is not allowed or the tag is
wrong. -/
def toMode (vg : GcmImpl) : OMode vg where
  Pre := BodyTo
  op := fun _ h => h.op
  tg := fun _ h => h.tg
  x := dstOf
  out := outTo
  fb := fbTo
  out_mem := fun _ _ _ _ h => by simp only [outTo, h]
  bad := wipe
  fail := wipe
  dec := decTo vg.callees ⟨vg.ctr.calleeTo.name, vg.ctr.calleeTo.code⟩
  hbad := fun q _ => wipeBad_pc q
  hfail := fun q hf => wipeFail_pc q hf
  hdec := fun q ht => decTo_pc vg q ht

/-! ## The contract -/

/-- `vg_aes_gcm_open_to(ctx, rounds, nonce, nonce_len, aad, aad_len, src, len, dst, dst_len, tag, tag_len, work)`. -/
def toPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  let aad : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let src : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
  let dst : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
  let tag : Region := ⟨(arg s 10).setWidth 64, (arg s 11).toNat⟩
  let scr : Region := ⟨(arg s 12).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 52⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 76, 76⟩
  s.rd = [ctx, nonce, aad, src, tag] ∧ s.wr = [dst, scr, args] ∧
  ctx.Disjoint dst ∧ ctx.Disjoint scr ∧ nonce.Disjoint dst ∧ nonce.Disjoint scr ∧ aad.Disjoint dst ∧
  aad.Disjoint scr ∧ src.Disjoint dst ∧ src.Disjoint scr ∧ dst.Disjoint tag ∧ dst.Disjoint scr ∧
  dst.Disjoint args ∧ tag.Disjoint scr ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint src ∧ ret.Disjoint dst ∧
  ret.Disjoint tag ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint src ∧
  stack.Disjoint dst ∧ stack.Disjoint tag ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧ (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32 ∧
  (arg s 12).toNat + 2560 ≤ 2 ^ 32 ∧ 76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 56 ≤ 2 ^ 32 ∧
  roundsOk s 1 ∧ (arg s 9).toNat = (arg s 7).toNat

/-- What `open_to` computes. -/
abbrev toRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxH s.mem ((arg s 0).setWidth 64))
    (arg s 11).toNat (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat) (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (bytesAt s.mem ((arg s 10).setWidth 64) (arg s 11).toNat)

def toX86 : Contract isa where
  pre := toPre
  post s s' :=
    match toRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧
        bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
        bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 7).toNat = List.replicate (arg s 7).toNat 0
  pub s₁ s₂ := pubN 13 s₁ s₂ ∧ (toRes s₁).isSome = (toRes s₂).isSome

/-- What the frame of `withStackScratch` needs of the code: the shared contract
with the working space as a last argument, whatever it holds, and 76 bytes of
stack (the frame of 48 and the calls' 28). -/
abbrev toScratchK : Contract isa :=
  Sig.scratchContract X86.abi Spec.Gcm.openToSig "work" .u64 320 (Spec.Gcm.openToPre X86.abi.ptrBits)
    (Proof.AesGcm.openToRoundsPost X86.abi.ptrBits) true 76 (some (Spec.Gcm.openToLeak X86.abi.ptrBits))

theorem to_pre : ∀ s, toScratchK.pre s → toX86.pre s := by
  sig_implies_pre [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
    pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-! ## The frame's entry -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 104 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 104) : w64 (P + BitVec.ofNat 32 d) = w64 P + BitVec.ofNat 64 d :=
  w64_add (by omega_arith)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 104) (he : e + 4 ≤ 104) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 =
      m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega_arith), aP hP (by omega_arith)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 104) (h : 4 ≤ e) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 P) 32 = m.readW (w64 P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_zero32] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 104) (h : 4 ≤ d) :
    (m.writeW (w64 P) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 = m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_zero32] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

theorem frameArgs_eq : frameArgs =
    [.mov .eax (.mem (at_ .esp 84)), .store (at_ .esp 0) .eax,
      .mov .eax (.mem (at_ .esp 52)), .store (at_ .esp 4) .eax, .mov .eax (.mem (at_ .esp 56)), .store (at_ .esp 8) .eax,
      .mov .eax (.mem (at_ .esp 60)), .store (at_ .esp 12) .eax, .mov .eax (.mem (at_ .esp 64)), .store (at_ .esp 16) .eax,
      .mov .eax (.mem (at_ .esp 68)), .store (at_ .esp 20) .eax, .mov .eax (.mem (at_ .esp 72)), .store (at_ .esp 24) .eax,
      .mov .eax (.mem (at_ .esp 76)), .store (at_ .esp 28) .eax, .mov .eax (.mem (at_ .esp 80)), .store (at_ .esp 32) .eax,
      .mov .eax (.mem (at_ .esp 92)), .store (at_ .esp 36) .eax, .mov .eax (.mem (at_ .esp 96)), .store (at_ .esp 40) .eax,
      .mov .eax (.mem (at_ .esp 100)), .store (at_ .esp 44) .eax] := rfl

/-- The memory after the frame's entry, at the frame `P`: `dst` (at `P + 84`)
at `P`, and our arguments but `dst` and `dst_len` (at `P + 52` … `P + 80`,
`P + 92` … `P + 100`) at `P + 4` … `P + 44`. -/
def fMem (m : Mem) (P : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (w64 (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
  w (w (w (w (w (w (w (w (w (w (w (m.writeW (w64 P) (r 84)) 4 (r 52)) 8 (r 56)) 12 (r 60)) 16 (r 64))
    20 (r 68)) 24 (r 72)) 28 (r 76)) 32 (r 80)) 36 (r 92)) 40 (r 96)) 44 (r 100)

theorem frameArgs_ok (a : State) (hP : (a.gpr .esp).toNat + 104 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 48 → InRegions a.wr (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 104 → InRegions (a.rd ++ a.wr) (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4) :
    ∃ e, runBlock isa frameArgs a = some e ∧ e.mem = fMem a.mem (a.gpr .esp) ∧
      (∀ r, r ≠ .eax → e.gpr r = a.gpr r) ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  have hw0 : InRegions a.wr (w64 (a.gpr .esp)) 4 := by simpa only [add_zero32] using hw 0 (by decide)
  refine ⟨_, by
    xrun [frameArgs_eq, hw0, hw 4 (by decide), hw 8 (by decide), hw 12 (by decide), hw 16 (by decide),
      hw 20 (by decide), hw 24 (by decide), hw 28 (by decide), hw 32 (by decide), hw 36 (by decide),
      hw 40 (by decide), hw 44 (by decide), hr 52 (by decide) (by decide), hr 56 (by decide) (by decide),
      hr 60 (by decide) (by decide), hr 64 (by decide) (by decide), hr 68 (by decide) (by decide),
      hr 72 (by decide) (by decide), hr 76 (by decide) (by decide), hr 80 (by decide) (by decide),
      hr 84 (by decide) (by decide), hr 92 (by decide) (by decide), hr 96 (by decide) (by decide),
      hr 100 (by decide) (by decide), add_zero32, rdw hP, rdw0 hP, rd0w hP], ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rfl
  · simp [gpr_setMem, gpr_setReg, gpr_arithFlags, h]
  · simp only [rd_setMem, rd_setReg, rd_arithFlags]
  · simp only [wr_setMem, wr_setReg, wr_arithFlags]

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 104 ≤ 2 ^ 32)
include hP

/-- The entry writes only the frame. -/
theorem fMem_frame : Frame [⟨w64 P, 48⟩] m (fMem m P) := by
  have c (d : Nat) (hd : d + 4 ≤ 48) : (⟨w64 P, 48⟩ : Region).Contains (w64 (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega_arith)]; exact Offset.contains_base _ hd (by omega_arith)
  have c0 : (⟨w64 P, 48⟩ : Region).Contains (w64 P) 4 := by simp [Region.Contains]
  have hm := List.mem_singleton_self (⟨w64 P, 48⟩ : Region)
  unfold fMem; dsimp only
  refine Frame.writeW ?_ hm _ (c 44 (by decide)); refine Frame.writeW ?_ hm _ (c 40 (by decide))
  refine Frame.writeW ?_ hm _ (c 36 (by decide)); refine Frame.writeW ?_ hm _ (c 32 (by decide))
  refine Frame.writeW ?_ hm _ (c 28 (by decide)); refine Frame.writeW ?_ hm _ (c 24 (by decide))
  refine Frame.writeW ?_ hm _ (c 20 (by decide)); refine Frame.writeW ?_ hm _ (c 16 (by decide))
  refine Frame.writeW ?_ hm _ (c 12 (by decide)); refine Frame.writeW ?_ hm _ (c 8 (by decide))
  refine Frame.writeW ?_ hm _ (c 4 (by decide)); refine Frame.writeW ?_ hm _ c0
  exact Frame.refl _ _

/-- The words of the frame after the entry. -/
theorem fMem_words :
    let e := fMem m P
    let r (m : Mem) (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
    e.readW (w64 P) 32 = r m 84 ∧ r e 4 = r m 52 ∧ r e 8 = r m 56 ∧ r e 12 = r m 60 ∧ r e 16 = r m 64 ∧
      r e 20 = r m 68 ∧ r e 24 = r m 72 ∧ r e 28 = r m 76 ∧ r e 32 = r m 80 ∧ r e 36 = r m 92 ∧
      r e 40 = r m 96 ∧ r e 44 = r m 100 := by
  simp (disch := first | decide | omega_arith) only [fMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial⟩

end

/-! ## The precondition, by name -/

section
variable (s : State)

/-- The frame. -/
abbrev Pf : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 48

/-- The public data of the body's run: `open`'s arguments, `W` at 8 and
`tag` at 10, at the frame. -/
def pubTo : BitVec 32 × (Nat → BitVec 32) :=
  (Pf s, fun k => if k < 11 then arg s (if k = 8 then 12 else if k = 9 then 11 else k) else 0)

end

/-- `toPre`, by name, with the stack as `below`. -/
structure TP (s : State) : Prop where
  rd : s.rd = [⟨w64 (arg s 0), 256⟩, ⟨w64 (arg s 2), (arg s 3).toNat⟩, ⟨w64 (arg s 4), (arg s 5).toNat⟩,
    ⟨w64 (arg s 6), (arg s 7).toNat⟩, ⟨w64 (arg s 10), (arg s 11).toNat⟩]
  wr : s.wr = [⟨w64 (arg s 8), (arg s 7).toNat⟩, ⟨w64 (arg s 12), 2560⟩, ⟨argAddr s 0, 52⟩]
  c_t : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  c_w : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  n_t : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  n_w : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  a_t : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  a_w : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  d_t : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  d_w : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  t_g : (⟨w64 (arg s 8), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 10), (arg s 11).toNat⟩
  t_w : (⟨w64 (arg s 8), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  g_w : (⟨w64 (arg s 10), (arg s 11).toNat⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  k_c : (below (s.gpr .esp) 76).Disjoint ⟨w64 (arg s 0), 256⟩
  k_n : (below (s.gpr .esp) 76).Disjoint ⟨w64 (arg s 2), (arg s 3).toNat⟩
  k_a : (below (s.gpr .esp) 76).Disjoint ⟨w64 (arg s 4), (arg s 5).toNat⟩
  k_d : (below (s.gpr .esp) 76).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  k_t : (below (s.gpr .esp) 76).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  k_g : (below (s.gpr .esp) 76).Disjoint ⟨w64 (arg s 10), (arg s 11).toNat⟩
  k_w : (below (s.gpr .esp) 76).Disjoint ⟨w64 (arg s 12), 2560⟩
  r_t : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 8), (arg s 7).toNat⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 12), 2560⟩
  r_a : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fn : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  fa : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  fd : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  ft : (arg s 8).toNat + (arg s 7).toNat ≤ 2 ^ 32
  fg : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  fw : (arg s 12).toNat + 2560 ≤ 2 ^ 32
  sp : 76 ≤ (s.gpr .esp).toNat
  hi : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  rounds : roundsOk s 1

theorem TP.of {s : State} (h : toPre s) : TP s := by
  simp only [toPre] at h
  obtain ⟨hrd, hwr, c_t, c_w, n_t, n_w, a_t, a_w, d_t, d_w, t_g, t_w, -, g_w, -, -, -, -, -, r_t, -, r_w, r_a, k_c,
    k_n, k_a, k_d, k_t, k_g, k_w, -, fc, fn, fa, fd, ft, fg, fw, sp, hi, hR, hl⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_n k_a k_d k_t k_g k_w
  rw [hl] at hwr c_t n_t a_t d_t t_g t_w k_t r_t ft
  exact ⟨hrd, hwr, c_t, c_w, n_t, n_w, a_t, a_w, d_t, d_w, t_g, t_w, g_w, k_c, k_n, k_a, k_d, k_t, k_g, k_w, r_t, r_w,
    r_a, fc, fn, fa, fd, ft, fg, fw, sp, hi, hR⟩

namespace TP
variable {s : State} (h : TP s)
include h

theorem pN : (Pf s).toNat = (s.gpr .esp).toNat - 48 := sub_toNat (by have := h.sp; omega)

theorem hP : (Pf s).toNat + 104 ≤ 2 ^ 32 := by rw [h.pN]; have := h.sp; have := h.hi; omega

/-- Our argument `i`, above the frame. -/
theorem argA (i : Nat) : argAddr s i = w64 (Pf s + BitVec.ofNat 32 (52 + 4 * i)) := by
  have := h.sp
  simp only [argAddr, Pf]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem argOf {j : Nat} {v : BitVec 32}
    (hv : s.mem.readW (w64 (Pf s + BitVec.ofNat 32 (52 + 4 * j))) 32 = v) : arg s j = v := by
  rw [← hv]; show s.mem.readW (argAddr s j) 32 = _; rw [h.argA j]

/-- The frame and the words in it, within the stack below `esp`. -/
theorem frame_sub {d n : Nat} (hd : d + n ≤ 48) :
    Region.Sub ⟨w64 (Pf s) + BitVec.ofNat 64 d, n⟩ (below (s.gpr .esp) 76) :=
  region_sub_trans (Offset.sub_base _ hd) (below_sub (by decide) h.sp)

theorem frame_sub0 {n : Nat} (hn : n ≤ 48) : Region.Sub ⟨w64 (Pf s), n⟩ (below (s.gpr .esp) 76) :=
  region_sub_trans (Region.sub_prefix hn) (below_sub (by decide) h.sp)

/-- The stack the body's calls use, within ours. -/
theorem stk_sub : Region.Sub (below (Pf s) 28) (below (s.gpr .esp) 76) :=
  below_inner (by decide) h.sp

/-- A region apart from the stack below `esp` is apart from the frame. -/
theorem frameDisj {X : Region} (hX : (below (s.gpr .esp) 76).Disjoint X) :
    ∀ r ∈ [(⟨w64 (Pf s), 48⟩ : Region)], X.Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact (hX.sub_left (h.frame_sub0 (Nat.le_refl _))).symm

end TP

/-- What the entry leaves: the frame's words as the body takes them. -/
structure Entered (s e : State) : Prop where
  esp : e.gpr .esp = Pf s
  gpr : ∀ r, r ≠ .eax → r ≠ .esp → e.gpr r = s.gpr r
  rd : e.rd = s.rd
  wr : e.wr = ⟨w64 (Pf s), 48⟩ :: s.wr
  frame : Frame [⟨w64 (Pf s), 48⟩] s.mem e.mem
  args : ∀ i, i < 11 → arg e i = arg s (if i = 8 then 10 else if i = 9 then 11 else if i = 10 then 12 else i)
  dst : e.mem.readW (w64 (Pf s)) 32 = arg s 8

theorem entered {s : State} (h : TP s) :
    WP isa (.block frameArgs) (allocFrame 48 s) (Entered s) := by
  have hP := h.hP
  have esp : (allocFrame 48 s).gpr .esp = Pf s := allocFrame_esp 48 s
  have hw : ∀ d, d + 4 ≤ 48 → InRegions (allocFrame 48 s).wr (w64 ((allocFrame 48 s).gpr .esp + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by
      rw [esp, allocFrame_wr, aP hP (by omega)]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩
  have hr : ∀ d, 52 ≤ d → d + 4 ≤ 104 →
      InRegions ((allocFrame 48 s).rd ++ (allocFrame 48 s).wr) (w64 ((allocFrame 48 s).gpr .esp + BitVec.ofNat 32 d)) 4 :=
    fun d h₁ h₂ => by
      refine in_left ⟨⟨argAddr s 0, 52⟩, ?_, ?_⟩
      · rw [allocFrame_wr, h.wr]; simp
      · rw [esp, h.argA 0, aP hP (by omega), aP hP (by omega)]
        exact Offset.contains _ (by omega) (by omega) (by omega)
  obtain ⟨e, run, hm, hg, hrd, hwr⟩ := frameArgs_ok (allocFrame 48 s) (by rw [esp]; exact hP) hw hr
  refine WP.of_runBlock ⟨e, run, ?_⟩
  rw [esp] at hm
  have hw' := fMem_words (m := s.mem) hP
  simp only [allocFrame_mem] at hm
  have esp' : e.gpr .esp = Pf s := by rw [hg .esp (by decide), esp]
  have eA : ∀ i, arg e i = (fMem s.mem (Pf s)).readW (w64 (Pf s + BitVec.ofNat 32 (4 + 4 * i))) 32 := fun i => by
    simp only [arg, argAddr, esp', hm]
  refine ⟨esp', fun r h₁ h₂ => by rw [hg r h₁, allocFrame_gpr _ _ h₂], by rw [hrd, allocFrame_rd],
    by rw [hwr, allocFrame_wr], by rw [hm]; exact fMem_frame hP, fun i hi => ?_,
    (by rw [hm]; exact hw'.1.trans (h.argOf (j := 8) rfl).symm)⟩
  rw [eA]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw'.2.1.trans (h.argOf (j := 0) rfl).symm
  · exact hw'.2.2.1.trans (h.argOf (j := 1) rfl).symm
  · exact hw'.2.2.2.1.trans (h.argOf (j := 2) rfl).symm
  · exact hw'.2.2.2.2.1.trans (h.argOf (j := 3) rfl).symm
  · exact hw'.2.2.2.2.2.1.trans (h.argOf (j := 4) rfl).symm
  · exact hw'.2.2.2.2.2.2.1.trans (h.argOf (j := 5) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.1.trans (h.argOf (j := 6) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.1.trans (h.argOf (j := 7) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.2.1.trans (h.argOf (j := 10) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.2.2.1.trans (h.argOf (j := 11) rfl).symm
  · exact hw'.2.2.2.2.2.2.2.2.2.2.2.trans (h.argOf (j := 12) rfl).symm

namespace Entered
variable {s e : State} (h : TP s) (he : Entered s e)
include h he

omit h in
theorem a (i : Nat) (hi : i < 8) : arg e i = arg s i := by
  have := he.args i (by omega)
  simpa only [show ¬(i = 8) by omega, show ¬(i = 9) by omega, show ¬(i = 10) by omega, ↓reduceIte] using this

omit h in
theorem pub_eq : pubSw 11 8 e = pubTo s := by
  refine Prod.ext he.esp (funext fun k => ?_)
  simp only [pubSw, pubTo]
  by_cases hk : k < 11
  · simp only [hk, ↓reduceIte]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact he.args _ (by decide)
  · simp only [hk, ↓reduceIte]

omit h in
theorem dst_eq : dstOf e = arg s 8 := by
  show e.mem.readW (w64 (e.gpr .esp)) 32 = _; rw [he.esp]; exact he.dst

omit h in
/-- The frame, readable and writable. -/
theorem frameIn : (⟨w64 (Pf s), 48⟩ : Region) ∈ e.rd ++ e.wr := by
  rw [he.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)

theorem bodyTo : BodyTo e := by
  have hP := h.hP
  have pn := h.pN
  have hsp := h.sp
  have hhi := h.hi
  have a8 := he.args 8 (by decide)
  have a9 := he.args 9 (by decide)
  have a10 := he.args 10 (by decide)
  simp only [↓reduceIte, show (9 : Nat) ≠ 8 by decide, show (10 : Nat) ≠ 8 by decide,
    show (10 : Nat) ≠ 9 by decide] at a8 a9 a10
  have a0 := he.a 0 (by decide); have a1 := he.a 1 (by decide); have a2 := he.a 2 (by decide)
  have a3 := he.a 3 (by decide); have a4 := he.a 4 (by decide); have a5 := he.a 5 (by decide)
  have a6 := he.a 6 (by decide); have a7 := he.a 7 (by decide)
  have esp := he.esp
  have rdwr : ∀ r ∈ s.rd, r ∈ e.rd ++ e.wr := fun r hr => by rw [he.rd]; exact List.mem_append_left _ hr
  have wrwr : ∀ r ∈ s.wr, r ∈ e.wr := fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ hr
  have eA0 : argAddr e 0 = w64 (Pf s) + BitVec.ofNat 64 4 := by
    show w64 (e.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)) = _; rw [esp]; exact aP hP (by decide)
  have fr : ∀ {d n : Nat}, d + n ≤ 48 → Covers [⟨w64 (Pf s) + BitVec.ofNat 64 d, n⟩] (e.rd ++ e.wr) :=
    fun hd => covers_off (covers_of_mem he.frameIn) hd (by decide)
  have kS : ∀ {X : Region}, (below (s.gpr .esp) 76).Disjoint X → (below (e.gpr .esp) 28).Disjoint X :=
    fun hX => by rw [esp]; exact hX.sub_left h.stk_sub
  have rS : ∀ {X : Region}, (below (s.gpr .esp) 76).Disjoint X → (⟨w64 (e.gpr .esp), 4⟩ : Region).Disjoint X :=
    fun hX => by rw [esp]; exact hX.sub_left (h.frame_sub0 (by decide))
  have aS : ∀ {X : Region}, (below (s.gpr .esp) 76).Disjoint X → X.Disjoint ⟨argAddr e 0, 4 * 11⟩ :=
    fun hX => by rw [eA0]; exact (hX.sub_left (h.frame_sub (d := 4) (n := 44) (by decide))).symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, aS (by rw [a6, a7]; exact h.k_d), aS (by rw [a10]; exact h.k_w),
    rS (by rw [a6, a7]; exact h.k_d), rS (by rw [a10]; exact h.k_w), kS (by rw [a0]; exact h.k_c),
    kS (by rw [a2, a3]; exact h.k_n), kS (by rw [a4, a5]; exact h.k_a), kS (by rw [a6, a7]; exact h.k_d),
    kS (by rw [a10]; exact h.k_w), by rw [a0]; exact h.fc, by rw [a2, a3]; exact h.fn, by rw [a4, a5]; exact h.fa,
    by rw [a6, a7]; exact h.fd, by rw [a10]; exact h.fw, by rw [esp, pn]; omega, by rw [esp, pn]; omega,
    by show roundsOk e 1; simp only [roundsOk, a1]; exact h.rounds⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [a0]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a2, a3]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a4, a5]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a6, a7]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a10]; exact covers_of_mem (wrwr _ (by rw [h.wr]; simp))
  · rw [eA0]; exact fr (by decide)
  · rw [a0, a10]; exact h.c_w
  · rw [a2, a3, a10]; exact h.n_w
  · rw [a4, a5, a10]; exact h.a_w
  · rw [a6, a7, a10]; exact h.d_w
  · rw [a8, a9]; exact covers_of_mem (rdwr _ (by rw [h.rd]; simp))
  · rw [a8, a9]; exact h.fg
  · rw [a8, a9, a10]; exact h.g_w
  · rw [a8, a9]; exact kS h.k_g
  · rw [he.pub_eq, he.dst_eq]
    exact ⟨h.ft, h.c_t, h.n_t, h.a_t, h.d_t, h.t_g.symm, h.t_w.symm,
      h.k_t.sub_left (h.frame_sub0 (by decide)), h.k_t.sub_left h.stk_sub⟩
  · rw [he.dst_eq, a7]; exact covers_of_mem (wrwr _ (by rw [h.wr]; simp))
  · rw [esp]; exact covers_pre (covers_of_mem he.frameIn) (by decide) (by decide)

/-- What `open`'s body computes from the frame is what `open_to` computes. -/
theorem res : openRes e = toRes s := by
  have hf := he.frame
  have hR := h.rounds
  have a0 := he.a 0 (by decide); have a1 := he.a 1 (by decide); have a2 := he.a 2 (by decide)
  have a3 := he.a 3 (by decide); have a4 := he.a 4 (by decide); have a5 := he.a 5 (by decide)
  have a6 := he.a 6 (by decide); have a7 := he.a 7 (by decide)
  have a8 := he.args 8 (by decide)
  have a9 := he.args 9 (by decide)
  simp only [↓reduceIte, show (9 : Nat) ≠ 8 by decide] at a8 a9
  have hc : ciphOf e.mem (arg s 0) (arg s 1).toNat = ciphOf s.mem (arg s 0) (arg s 1).toNat :=
    ciph_frame hf (h.frameDisj h.k_c) hR
  simp only [openRes, toRes, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  rw [show ctxCiph e.mem (w64 (arg s 0)) (arg s 1).toNat = ctxCiph s.mem (w64 (arg s 0)) (arg s 1).toNat from hc,
    show ctxH e.mem (w64 (arg s 0)) = ctxH s.mem (w64 (arg s 0)) from by
      rw [ctxH_eq, ctxH_eq, blockAt_frame hf (h.frameDisj (h.k_c.sub_right (Lay.ctxSub (by decide))))],
    bytesAt_frame hf (h.frameDisj h.k_n) (by have := h.fn; omega),
    bytesAt_frame hf (h.frameDisj h.k_d) (by have := h.fd; omega),
    bytesAt_frame hf (h.frameDisj h.k_a) (by have := h.fa; omega),
    bytesAt_frame hf (h.frameDisj h.k_g) (by have := h.fg; omega)]

end Entered

/-! ## The frame -/

theorem noEsp_of {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

/-- A piece, with what its code may write: within the regions writable where
it starts and the stack below `esp` it uses (`Exec.frameSp`). -/
theorem Pc.frameSp {α : Sort _} {P Q : α → State → Prop} {c : Prog isa} (h : Pc P c Q) (hsp : NoSp c)
    (hd : ∀ a s, P a s → stackUse c ≤ (s.gpr .esp).toNat) :
    Pc P c fun a s' => Q a s' ∧ ∃ s, P a s ∧ Frame (s.wr ++ [below (s.gpr .esp) (stackUse c)]) s.mem s'.mem := by
  refine ⟨fun a s hs => ?_, h.ct⟩
  obtain ⟨t, s', he, hq⟩ := h.wp a s hs
  exact ⟨t, s', he, hq, s, hs, Exec.frameSp he hsp (hd a s hs)⟩

/-- A frame of `bytes` bytes, around a piece run from the state after the
allocation. -/
theorem Pc.frameAlloc {α : Sort _} {P Q : α → State → Prop} {bytes : Nat} {body : Prog isa}
    (h0 : 0 < bytes) (h1 : bytes < 4096) (h4 : bytes % 4 = 0) (hn : ∀ a s, P a s → bytes ≤ (s.gpr .esp).toNat)
    (hsp : NoSp body)
    (hb : Pc (fun a s₁ => ∃ s, P a s ∧ s₁ = allocFrame bytes s) body fun a s₂ => Q a (freed bytes s₂)) :
    Pc P (.frame (.alloc bytes) body (.free bytes)) Q := by
  refine ⟨fun a s hs => WP.frameAlloc h0 h1 h4 (hn a s hs) hsp (hb.wp a _ ⟨s, hs, rfl⟩), ?_⟩
  exact RelCT.frameAlloc (RelCT.mono hb.ct (fun _ _ ⟨s₁, s₂, ⟨⟨a, h₁⟩, ⟨b, h₂⟩⟩, e₁, e₂⟩ =>
    ⟨⟨a, s₁, h₁, e₁⟩, ⟨b, s₂, h₂, e₂⟩⟩) fun _ _ _ => trivial)

section
variable (vg : GcmImpl)

/-- `vg_aes_ctr32_to`, of the implementations `vg`. -/
abbrev toFn : Fn := ⟨vg.ctr.calleeTo.name, vg.ctr.calleeTo.code⟩

theorem body_noEsp :
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).allInstrs (fun i => !Taint.clobbers i .esp) =
      true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush,
    ghCall, ghash1, j0, j0hash, lens, oneAad, oneEntry, oneTag, recv, tag, tagLenOk, openBody, decTo, wholeTo,
    ctrToCall, wipe, wipeLoop, Code.allInstrs, GcmImpl.callees, noEsp_of vg.ctr.nosp, noEsp_of vg.ctr.nospTo,
    noEsp_of vg.ctr.expandNosp, noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem body_stackUse : stackUse (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))) ≤ 28 := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush,
    ghCall, ghash1, j0, j0hash, lens, oneAad, oneEntry, oneTag, recv, tag, tagLenOk, openBody, decTo, wholeTo,
    ctrToCall, wipe, wipeLoop, stackUse, GcmImpl.callees, vg.ctr.stack, vg.ctr.toStack, vg.ctr.expandStack,
    vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons, List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

end

/-! ## Correct and constant time -/

/-- The public data of a run: the body's, and whether the tag is right. -/
abbrev idx (s : State) : OQ := ((pubTo s, arg s 8), (toRes s).isSome)

section
variable (vg : GcmImpl)

theorem openTo_eq : Open.openTo vg.callees (toFn vg) = .frame (.alloc 48)
    (.seq (.block frameArgs) (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec)) (.free 48) :=
  rfl

theorem frameBody_noSp : NoSp (.seq (.block frameArgs)
    (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec) : Prog isa) := by
  refine NoSp.of_all ?_
  show ((Code.block frameArgs : Prog isa).allInstrs _ && _) = true
  rw [show (toMode vg).dec = decTo vg.callees (toFn vg) from rfl, show (toMode vg).bad = wipe from rfl,
    show (toMode vg).fail = wipe from rfl, body_noEsp vg, Bool.and_true]
  decide

theorem openTo_pc (q : OQ) :
    Pc (fun (a : State) s => toPre s ∧ idx s = q ∧ s = a) (Open.openTo vg.callees (toFn vg))
      (fun a s' => abiPreserved a s' ∧ toX86.post a s') := by
  rw [openTo_eq]
  refine Pc.frameAlloc (by decide) (by decide) (by decide) (fun a s ⟨hs, _, _⟩ => by
    have := (TP.of hs).sp; omega) (frameBody_noSp vg) ?_
  refine Pc.seq (Q := fun a e => toPre a ∧ idx a = q ∧ Entered a e) ?_ ?_
  · refine Pc.taint [.esp] (fun a s₁ ⟨s, ⟨hs, hq, hsa⟩, e₁⟩ => ?_) (fun a b s₁ s₂ ⟨x, ⟨_, hqx, _⟩, e₁⟩
        ⟨y, ⟨_, hqy, _⟩, e₂⟩ r hr => ?_) (by taint_decide)
    · subst e₁ hsa
      exact WP.mono (entered (TP.of hs)) fun e he => ⟨hs, hq, he⟩
    · simp only [List.mem_singleton] at hr; subst hr e₁ e₂
      rw [allocFrame_esp, allocFrame_esp]
      exact congrArg (fun (q : OQ) => q.1.1.1) (hqx.trans hqy.symm)
  have hsp : NoSp (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec) :=
    NoSp.of_all (body_noEsp vg)
  refine Pc.mono (Pc.lift (Pc.frameSp (openBody_pc (toMode vg) q) hsp fun s₀ s ⟨hb, _, hs⟩ => by
      have := hb.op.sp
      have : stackUse (openBody vg.callees (toMode vg).bad (toMode vg).fail (toMode vg).dec) ≤ 28 :=
        body_stackUse vg
      rw [hs]; omega)
      (fun _ e => e) fun a e ⟨ha, hq, he⟩ => ⟨he.bodyTo (TP.of ha), ?_, rfl⟩) (fun _ _ h => h)
    fun a s₂ ⟨e, ⟨ha, hq, he⟩, ⟨⟨abi, hx, hpost⟩, x, ⟨_, _, hxe⟩, hfr⟩, _, _⟩ => ?_
  swap
  · rw [← hq, he.pub_eq, show (toMode vg).x e = dstOf e from rfl, he.dst_eq, he.res (TP.of ha)]
  subst hq
  rw [hxe] at hfr
  have T := TP.of ha
  have hP := T.hP
  have eE : w64 (a.gpr .esp) = w64 (Pf a) + BitVec.ofNat 64 48 := by
    rw [← aP hP (by decide)]; congr 1; exact (BitVec.sub_add_cancel _ _).symm
  have rF : (⟨w64 (a.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (Pf a), 48⟩ := by
    rw [eE]; exact (split_disj (by omega)).symm
  have ret₁ : e.mem.readW (w64 (a.gpr .esp)) 32 = a.mem.readW (w64 (a.gpr .esp)) 32 :=
    he.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact rF) (by decide)
  have ret₂ : s₂.mem.readW (w64 (a.gpr .esp)) 32 = e.mem.readW (w64 (a.gpr .esp)) 32 := by
    refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [he.wr, T.wr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rF
    · exact T.r_t
    · exact T.r_w
    · exact T.r_a
    · rw [he.esp]
      exact (ret_below (k := 76) T.sp).sub_right (region_sub_trans
        (below_sub (body_stackUse vg) (by rw [T.pN]; have := T.sp; omega)) T.stk_sub)
  refine ⟨⟨fun r hr => ?_, by rw [freed_mem, ret₂, ret₁]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_gpr _ _ (by decide), abi.1 _ (by decide), he.gpr _ (by decide) (by decide)]
    · rw [freed_esp, abi.1 _ (by decide), he.esp]; exact BitVec.sub_add_cancel _ _
  · have hres : oRes (idx a).1.1 e = toRes a := by rw [← openRes_eq hx.pub, he.res T]
    unfold PostO at hpost
    rw [hres] at hpost
    simp only [toX86, ret32_eq, freed_mem, freed_gpr _ _ (show Reg.eax ≠ .esp by decide)]
    split
    · next pt hpt => rw [hpt] at hpost; exact hpost
    · next hpt => rw [hpt] at hpost; exact hpost

theorem openTo_correct (s : State) (hs : toX86.pre s) :
    ∃ t s', Exec isa (Open.openTo vg.callees (toFn vg)) s t s' ∧ abiPreserved s s' ∧ toX86.post s s' :=
  (openTo_pc vg (idx s)).wp s s ⟨hs, rfl, rfl⟩

theorem openTo_ct : ConstantTime isa toX86.pre toX86.pub (Open.openTo vg.callees (toFn vg)) := by
  refine Pc.constantTime idx (fun s₁ s₂ _ _ ⟨⟨hesp, ha⟩, hs⟩ => ?_) (openTo_pc vg) fun _ hs => ⟨hs, rfl, rfl⟩
  simp only [idx, pubTo, Pf, hesp, hs, ha 8 (by decide)]
  congr 3
  funext k
  split
  · rw [ha _ (by split <;> (try split) <;> omega)]
  · rfl

end

/-! ## The contracts -/

/-- A state satisfying the precondition with the working space: no nonce,
additional data, text or tag; its thirteen argument slots at `0x8004`. -/
def toSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30 else if a = 0x8025 then 0x31
    else if a = 0x802d then 0x50 else if a = 0x8035 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3100, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 52⟩]

section
variable (vg : GcmImpl)

/-- `open_to`'s public data include its leak, from which `pub` has whether
it succeeds (`rounds` being valid). -/
theorem openTo_verified : Verified X86.target (Open.openTo vg.callees (toFn vg)) toScratchK :=
  Verified.of_correct (openTo_correct vg) (openTo_ct vg)
    { pre := to_pre
      post := by sig_implies_post [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
        pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ h₁ h₂ h
        have hR₁ := (TP.of (to_pre s₁ h₁)).rounds
        have hR₂ := (TP.of (to_pre s₂ h₂)).rounds
        sig_pub [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right,
          Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | (apply leak_bool hR₁ hR₂; with_reducible assumption)
      sat := by
        have a0 : arg toSat 0 = 0x1000 := by decide
        have a1 : arg toSat 1 = 10 := by decide
        have a2 : arg toSat 2 = 0x2000 := by decide
        have a3 : arg toSat 3 = 0 := by decide
        have a4 : arg toSat 4 = 0x2100 := by decide
        have a5 : arg toSat 5 = 0 := by decide
        have a6 : arg toSat 6 = 0x3000 := by decide
        have a7 : arg toSat 7 = 0 := by decide
        have a8 : arg toSat 8 = 0x3100 := by decide
        have a9 : arg toSat 9 = 0 := by decide
        have a10 : arg toSat 10 = 0x5000 := by decide
        have a11 : arg toSat 11 = 0 := by decide
        have a12 : arg toSat 12 = 0x4000 := by decide
        have e : argAddr toSat 0 = 0x8004 := by decide
        have esp : toSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [toScratchK, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Gcm.openToSig, Spec.Gcm.openToPre, Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, toX86, toPre,
          pubN, roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp] using toSat }

end

/-! ## In its frame

The frame of `withStackScratch` copies the arguments passed on the stack,
which needs the pre- and postconditions and the leak of `Spec.Gcm.openToSig`
to read the memory on entry only within the function's buffers: the key
context, the nonce, the additional data, `src` and the tag
(`openToPre_local`, `openToRoundsPost_local`, `openToLeak_local`, as
`Proof/AesGcm/ScratchOpenTo.lean` has them for `open_to_prepared`). -/

section
variable (pb : Nat)

theorem openToPre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- What `open_to` computes on the memory `m₂` is what it computes on `m₁`
where they agree on the buffers it reads. -/
theorem openToResult_local {m₁ m₂ : Mem} {ctx rd nonce nl aad al src len tag tl : BitVec 64}
    (hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14)
    (hc : ∀ i < 256, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hn : ∀ i < nl.toNat, m₂ (nonce + BitVec.ofNat 64 i) = m₁ (nonce + BitVec.ofNat 64 i))
    (ha : ∀ i < al.toNat, m₂ (aad + BitVec.ofNat 64 i) = m₁ (aad + BitVec.ofNat 64 i))
    (hs : ∀ i < len.toNat, m₂ (src + BitVec.ofNat 64 i) = m₁ (src + BitVec.ofNat 64 i))
    (ht : ∀ i < tl.toNat, m₂ (tag + BitVec.ofNat 64 i) = m₁ (tag + BitVec.ofNat 64 i)) :
    openResult (ctxCiph m₂ ctx (rd.setWidth pb).toNat) (ctxH m₂ ctx) (tl.setWidth pb).toNat
        (bytesAt m₂ nonce (nl.setWidth pb).toNat) (bytesAt m₂ src (len.setWidth pb).toNat)
        (bytesAt m₂ aad (al.setWidth pb).toNat) (bytesAt m₂ tag (tl.setWidth pb).toNat) =
      openResult (ctxCiph m₁ ctx (rd.setWidth pb).toNat) (ctxH m₁ ctx) (tl.setWidth pb).toNat
        (bytesAt m₁ nonce (nl.setWidth pb).toNat) (bytesAt m₁ src (len.setWidth pb).toNat)
        (bytesAt m₁ aad (al.setWidth pb).toNat) (bytesAt m₁ tag (tl.setWidth pb).toNat) := by
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  have := Nat.mod_le tl.toNat (2 ^ pb)
  rw [ctxCiph_congr (le15 hr) hc, ctxH_congr hc,
    bytesAt_congr (p := nonce) (n := (nl.setWidth pb).toNat) fun i hi => hn i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := aad) (n := (al.setWidth pb).toNat) fun i hi => ha i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := src) (n := (len.setWidth pb).toNat) fun i hi => hs i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := tag) (n := (tl.setWidth pb).toNat) fun i hi => ht i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]

theorem openToRoundsPost_local : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₁ m' r →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, Proof.AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [openToResult_local pb hr (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1) (agree_of hb.2.2.2.1)
    (agree_of hb.2.2.2.2.2)]
  exact h hr

theorem openToLeak_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₁ =
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (Spec.Gcm.openToLeak pb) _ m₂
  dsimp only [Curry.apply, Spec.Gcm.openToLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openToResult_local pb hr (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
      (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end

/-- A state satisfying `vg_aes_gcm_open_to`'s precondition, without the
working space: its twelve argument slots at `0x8004`. -/
def toFrameSat : State := { toSat with wr := [⟨0x3100, 0⟩, ⟨0x8004, 48⟩] }

theorem toFrameSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract X86.abi 2692).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [toFrameSat, toSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using toFrameSat

section
variable (vg : GcmImpl)

theorem openTo_noEsp : (Open.openTo vg.callees (toFn vg)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  show (!Taint.clobbers (.alloc 48) .esp && ((Code.block frameArgs : Prog isa).allInstrs _ &&
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).allInstrs _) && !Taint.clobbers (.free 48) .esp) = true
  rw [body_noEsp vg]
  decide

theorem openTo_stackUse : stackUse (Open.openTo vg.callees (toFn vg)) ≤ 76 := by
  have := body_stackUse vg
  show max 0 (stackUse (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg)))) + 48 ≤ 76
  omega

/-- `open_to` in its frame of 2616 bytes, holding its working space. -/
theorem openTo_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2616 12 (Open.openTo vg.callees (toFn vg)))
      (Proof.AesGcm.openToRoundsContract X86.abi 2692) :=
  X86.Verified.stackScratch (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openToPre X86.abi.ptrBits) (post := Proof.AesGcm.openToRoundsPost X86.abi.ptrBits)
    (wa := true) (stack := 76) (leak := some (Spec.Gcm.openToLeak X86.abi.ptrBits)) (bytes := 2616)
    (openTo_verified vg) (by decide) (openTo_noEsp vg) (openTo_stackUse vg) (openToPre_local _)
    (openToRoundsPost_local _) toFrameSat_pre (hleak := openToLeak_local _)

theorem body_spSafe :
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, absorbTail, cmp, cmpTail, copyLoop, crypt,
    cryptEntry, cryptHead, cryptTail, cryptWhole, ctrCall, finTag, firstFlush, flush,
    ghCall, ghash1, j0, j0hash, lens, oneAad, oneEntry, oneTag, recv, tag, tagLenOk, openBody, decTo, wholeTo,
    ctrToCall, wipe, wipeLoop, Code.all, GcmImpl.callees, vg.ctr.spSafe, vg.ctr.spSafeTo, vg.ctr.expandSpSafe,
    vg.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

/-- No instruction writes `esp` but the frames' push and pop. -/
theorem openTo_spSafe :
    (Impl.StackScratch.X86.withStackScratch 2616 12 (Open.openTo vg.callees (toFn vg))).all
      (fun i => !X86.isa.writesSp i) = true := by
  refine withStackScratch_spSafe ?_
  show (!X86.isa.writesSp (.alloc 48) && ((Code.block frameArgs : Prog isa).all _ &&
    (openBody vg.callees wipe wipe (decTo vg.callees (toFn vg))).all _) && !X86.isa.writesSp (.free 48)) = true
  rw [body_spSafe vg]
  decide

end

end VG.Proof.AesGcm.X86.OpenTo
