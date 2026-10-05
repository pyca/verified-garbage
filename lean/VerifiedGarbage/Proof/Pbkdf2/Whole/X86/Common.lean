import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Calls
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha224
import VerifiedGarbage.Proof.Hmac.Generic.Common

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Contract`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the contract

`pbkG` is the contract the proof of `pbkdf2` is written against:
`VG.Spec.Pbkdf2.pbkdf2ScratchContract` with 76 bytes of stack, with its facts spelt
out, which it implies for any streaming hash function and scratch space
(`pbkImp`). Every argument is on the stack (cdecl): `password`,
`password_len`, `salt`, `salt_len`, `c`, `out`, `out_len`, `scratch`.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

variable (S : StreamingHash) (W : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`,
with `8 W` bytes of scratch space and 76 bytes of stack below the return
address. -/
def pbkG : Contract isa where
  pre s :=
    let pw : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
    let salt : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let out : Region := ⟨(VG.X86.arg s 5).setWidth 64, (VG.X86.arg s 6).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 7).setWidth 64, W * 8⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩
    76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
    s.rd = [pw, salt] ∧ s.wr = [out, scratch, args] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ pw.Disjoint args ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    salt.Disjoint args ∧ out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint pw ∧ ret.Disjoint salt ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 5).toNat + (VG.X86.arg s 6).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 7).toNat + W * 8 ≤ 2 ^ 32 ∧
    0 < (VG.X86.arg s 4).toNat ∧ (VG.X86.arg s 6).toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac S (bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
      (bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat) (VG.X86.arg s 4).toNat (VG.X86.arg s 6).toNat =
      some (bytesAt s'.mem ((VG.X86.arg s 5).setWidth 64) (VG.X86.arg s 6).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 8, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `pbkG` with the arguments readable rather than writable, as the taint
analysis needs them apart from the writable regions: the contract the proof
is written against, which `VG.X86.Verified.narrowTo` moves to `pbkG` (the
code only reads its arguments). -/
def pbkN : Contract isa where
  pre s :=
    let pw : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
    let salt : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let out : Region := ⟨(VG.X86.arg s 5).setWidth 64, (VG.X86.arg s 6).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 7).setWidth 64, W * 8⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩
    76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
    s.rd = [pw, salt, args] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ pw.Disjoint args ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    salt.Disjoint args ∧ out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint pw ∧ ret.Disjoint salt ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 5).toNat + (VG.X86.arg s 6).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 7).toNat + W * 8 ≤ 2 ^ 32 ∧
    0 < (VG.X86.arg s 4).toNat ∧ (VG.X86.arg s 6).toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post := (VG.Proof.Pbkdf2.Whole.X86.pbkG S W).post
  pub := (VG.Proof.Pbkdf2.Whole.X86.pbkG S W).pub

theorem setWidth_inj32 {a b : BitVec 32} (h : (a.setWidth 64).setWidth 32 = (b.setWidth 64).setWidth 32) :
    a = b := by rwa [setWidth32_64, setWidth32_64] at h

/-- `pbkG` implies the shared contract for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem pbkImp (h : ∃ s, (Spec.Pbkdf2.pbkdf2ScratchContract S W X86.abi 76).pre s) :
    (VG.Proof.Pbkdf2.Whole.X86.pbkG S W).Implies (Spec.Pbkdf2.pbkdf2ScratchContract S W X86.abi 76) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, X86.abi] at h
        simp only [argVal32, setWidth32_64, toNat_setWidth64,
          show argBytes [32, 32, 32, 32, 32, 32, 32, 32] = 32 from rfl] at h
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27, h28⟩
      post := by
        rintro s s' - h
        sig_post [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, X86.abi]
        simp only [argVal32, setWidth32_64]
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, X86.abi] at h
        simp only [argVal32] at h
        obtain ⟨e, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
        refine ⟨e, fun i hi => ?_⟩
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a0
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a1
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a2
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a3
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a4
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a5
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a6
        · exact VG.Proof.Pbkdf2.Whole.X86.setWidth_inj32 a7
      sat := h }

/-- The regions the proof gives `pbkdf2`: the arguments readable. -/
def narrowRd (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩, ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩, ⟨argAddr s 0, 32⟩]
def narrowWr (W : Nat) (s : State) : List Region :=
  [⟨(VG.X86.arg s 5).setWidth 64, (VG.X86.arg s 6).toNat⟩, ⟨(VG.X86.arg s 7).setWidth 64, W * 8⟩]

/-- A state for `pbkG`, given the regions `pbkN` gives. -/
theorem pbkN_pre {s : State} (h : (VG.Proof.Pbkdf2.Whole.X86.pbkG S W).pre s) : (VG.Proof.Pbkdf2.Whole.X86.pbkN S W).pre (s.withRegions (VG.Proof.Pbkdf2.Whole.X86.narrowRd s) (VG.Proof.Pbkdf2.Whole.X86.narrowWr W s)) := by
  obtain ⟨h0, h1, _, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
  simp only [VG.Proof.Pbkdf2.Whole.X86.pbkN, VG.Proof.Pbkdf2.Whole.X86.narrowRd, VG.Proof.Pbkdf2.Whole.X86.narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨h0, h1, trivial, trivial, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩

/-- Verified against `pbkN`, so against `pbkG`. -/
theorem verified_pbkG {c : Prog isa} (h : Verified X86.target c (VG.Proof.Pbkdf2.Whole.X86.pbkN S W)) (hsat : ∃ s, (VG.Proof.Pbkdf2.Whole.X86.pbkG S W).pre s) :
    Verified X86.target c (VG.Proof.Pbkdf2.Whole.X86.pbkG S W) := by
  refine Verified.narrowTo h VG.Proof.Pbkdf2.Whole.X86.narrowRd (VG.Proof.Pbkdf2.Whole.X86.narrowWr W) (fun s h => VG.Proof.Pbkdf2.Whole.X86.pbkN_pre S W h) (fun s h => ?_) (fun s h => ?_)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, _, h2, h3, _⟩ := h
    rw [h2, h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [VG.Proof.Pbkdf2.Whole.X86.narrowRd, VG.Proof.Pbkdf2.Whole.X86.narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨_, _, _, h3, _⟩ := h
    rw [h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [VG.Proof.Pbkdf2.Whole.X86.narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

end VG.Proof.Pbkdf2.Whole.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common`. -/
section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the functions it calls, and its parts

`FnsOK F` is what the proof knows of the functions `pbkdf2` calls: the hash
function's streaming functions (`VG.Proof.Pbkdf2.Stream.X86.HashOK`), and
HMAC's `init` and `finalize` and PBKDF2's `iterate`, sound for their shared
contracts with 48 bytes of stack (`Sound`), with some working space each, at
most the `8 W` bytes they get. Then the precondition of `pbkdf2` (`Pre`), the
parts of its `scratch`, and what every piece of it keeps (`KR`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK SavedRegs saveR)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open Spec.Sha256 (bytesAt)

/-- The functions `pbkdf2` calls, verified. -/
structure FnsOK (F : Fns) where
  hH : HashOK F.H
  Wi : Nat
  Wf : Nat
  Wt : Nat
  hi : Sound F.hiC (Spec.Hmac.initScratchContract hH.SH Wi X86.abi 48)
  hf : Sound F.hfC (Spec.Hmac.finalizeScratchContract hH.SH Wf X86.abi 48)
  it : Sound F.itC (Spec.Pbkdf2.iterateContract hH.SH Wt X86.abi 48)
  hiSp : NoSp F.hiC
  hfSp : NoSp F.hfC
  itSp : NoSp F.itC
  hiSU : stackUse F.hiC ≤ 48
  hfSU : stackUse F.hfC ≤ 48
  itSU : stackUse F.itC ≤ 48
  hWi : Wi ≤ F.W
  hWf : Wf ≤ F.W
  hWt : Wt ≤ F.W
  hWH : F.H.W ≤ F.W
  hW : F.W ≤ 512
  /-- The digest is no longer than a block (so that the digest of a long
  password is a key `init` takes). -/
  hDB : F.H.D ≤ F.H.B
  /-- The streaming state holds a block. -/
  hBS : F.H.B ≤ F.H.S
  /-- Our buffers fit in the `8 S` bytes after the working space. -/
  fits : 20 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S

variable {F : Fns}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev pw : BitVec 32 := VG.X86.arg s₀ 0
abbrev pwl : Nat := (VG.X86.arg s₀ 1).toNat
abbrev salt : BitVec 32 := VG.X86.arg s₀ 2
abbrev sl : Nat := (VG.X86.arg s₀ 3).toNat
/-- The iteration count. -/
abbrev cc : Nat := (VG.X86.arg s₀ 4).toNat
abbrev out : BitVec 32 := VG.X86.arg s₀ 5
abbrev ol : Nat := (VG.X86.arg s₀ 6).toNat
abbrev scr : BitVec 32 := VG.X86.arg s₀ 7
abbrev pwR : Region := ⟨(VG.Proof.Pbkdf2.Whole.X86.pw s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.pwl s₀⟩
abbrev saltR : Region := ⟨(VG.Proof.Pbkdf2.Whole.X86.salt s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.sl s₀⟩
abbrev outR : Region := ⟨(VG.Proof.Pbkdf2.Whole.X86.out s₀).setWidth 64, VG.Proof.Pbkdf2.Whole.X86.ol s₀⟩
abbrev scR (F : Fns) : Region := ⟨(VG.Proof.Pbkdf2.Whole.X86.scr s₀).setWidth 64, (F.W + F.H.S) * 8⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 32⟩
abbrev retR : Region := ⟨(VG.Proof.Pbkdf2.Whole.X86.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Pbkdf2.Whole.X86.E s₀) 76
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := VG.Proof.Pbkdf2.Whole.X86.scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := (VG.Proof.Pbkdf2.Whole.X86.scr s₀).setWidth 64 + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨VG.Proof.Pbkdf2.Whole.X86.A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨(VG.Proof.Pbkdf2.Whole.X86.scr s₀).setWidth 64, k⟩

end

/-- The size of `scratch`. -/
abbrev _root_.VG.Impl.Pbkdf2.Whole.X86.Fns.L8 (F : Fns) : Nat := (F.W + F.H.S) * 8

/-- The precondition. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  sp76 : 76 ≤ (VG.Proof.Pbkdf2.Whole.X86.E s₀).toNat
  spf : (VG.Proof.Pbkdf2.Whole.X86.E s₀).toNat + 36 ≤ 2 ^ 32
  rd : s₀.rd = [VG.Proof.Pbkdf2.Whole.X86.pwR s₀, VG.Proof.Pbkdf2.Whole.X86.saltR s₀, VG.Proof.Pbkdf2.Whole.X86.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Whole.X86.outR s₀, VG.Proof.Pbkdf2.Whole.X86.scR s₀ F]
  pw_o : (VG.Proof.Pbkdf2.Whole.X86.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.outR s₀)
  pw_s : (VG.Proof.Pbkdf2.Whole.X86.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F)
  pw_a : (VG.Proof.Pbkdf2.Whole.X86.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.argR s₀)
  sa_o : (VG.Proof.Pbkdf2.Whole.X86.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.outR s₀)
  sa_s : (VG.Proof.Pbkdf2.Whole.X86.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F)
  sa_a : (VG.Proof.Pbkdf2.Whole.X86.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.argR s₀)
  o_s : (VG.Proof.Pbkdf2.Whole.X86.outR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F)
  o_a : (VG.Proof.Pbkdf2.Whole.X86.outR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.argR s₀)
  s_a : (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F).Disjoint (VG.Proof.Pbkdf2.Whole.X86.argR s₀)
  r_pw : (VG.Proof.Pbkdf2.Whole.X86.retR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.pwR s₀)
  r_sa : (VG.Proof.Pbkdf2.Whole.X86.retR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.saltR s₀)
  r_o : (VG.Proof.Pbkdf2.Whole.X86.retR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.outR s₀)
  r_s : (VG.Proof.Pbkdf2.Whole.X86.retR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F)
  r_a : (VG.Proof.Pbkdf2.Whole.X86.retR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.argR s₀)
  b_pw : (VG.Proof.Pbkdf2.Whole.X86.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.pwR s₀)
  b_sa : (VG.Proof.Pbkdf2.Whole.X86.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.saltR s₀)
  b_o : (VG.Proof.Pbkdf2.Whole.X86.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.outR s₀)
  b_s : (VG.Proof.Pbkdf2.Whole.X86.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F)
  b_a : (VG.Proof.Pbkdf2.Whole.X86.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.argR s₀)
  npw : (VG.Proof.Pbkdf2.Whole.X86.pw s₀).toNat + VG.Proof.Pbkdf2.Whole.X86.pwl s₀ ≤ 2 ^ 32
  nsa : (VG.Proof.Pbkdf2.Whole.X86.salt s₀).toNat + VG.Proof.Pbkdf2.Whole.X86.sl s₀ ≤ 2 ^ 32
  no : (VG.Proof.Pbkdf2.Whole.X86.out s₀).toNat + VG.Proof.Pbkdf2.Whole.X86.ol s₀ ≤ 2 ^ 32
  nsc : (VG.Proof.Pbkdf2.Whole.X86.scr s₀).toNat + F.L8 ≤ 2 ^ 32
  c0 : 0 < VG.Proof.Pbkdf2.Whole.X86.cc s₀
  olD : VG.Proof.Pbkdf2.Whole.X86.ol s₀ ≤ (2 ^ 32 - 1) * F.H.D

theorem pre_of (hF : VG.Proof.Pbkdf2.Whole.X86.FnsOK F) {s₀ : State} (h : (VG.Proof.Pbkdf2.Whole.X86.pbkN hF.hH.SH (F.W + F.H.S)).pre s₀) : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hD := hF.hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩ : Region) = VG.Proof.Pbkdf2.Whole.X86.stkR s₀ := by
    rw [VG.Proof.Pbkdf2.Whole.X86.stkR, below_eq h0]
  rw [hD] at h28
  rw [e] at h18 h19 h20 h21 h22
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩

/-! ## The layout of `scratch` -/

/-- The sizes, as facts about natural numbers. -/
structure Sizes (F : Fns) : Prop where
  B : 0 < F.H.B ∧ F.H.B ≤ 128
  S : 0 < F.H.S ∧ F.H.S ≤ 256
  D : 0 < F.H.D ∧ F.H.D ≤ F.H.F ∧ F.H.F ≤ 64
  W : F.H.W ≤ F.W ∧ F.W ≤ 512
  DB : F.H.D ≤ F.H.B
  BS : F.H.B ≤ F.H.S
  fits : 20 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S

theorem FnsOK.sizes (hF : VG.Proof.Pbkdf2.Whole.X86.FnsOK F) : VG.Proof.Pbkdf2.Whole.X86.Sizes F :=
  ⟨⟨hF.hH.hB0, hF.hH.hBB⟩, ⟨hF.hH.hS0, hF.hH.hSB⟩, ⟨hF.hH.hD0, hF.hH.hDF, hF.hH.hF⟩, ⟨hF.hWH, hF.hW⟩, hF.hDB, hF.hBS, hF.fits⟩

/-- Where the parts of `scratch` are. -/
theorem layout : F.L.buf = 8 * F.W + 16 ∧ F.st0O = 8 * F.W + 16 ∧ F.st1O = 8 * F.W + 16 + F.H.S ∧
    F.stSO = 8 * F.W + 16 + 2 * F.H.S ∧ F.stWO = 8 * F.W + 16 + 3 * F.H.S ∧
    F.uO = 8 * F.W + 16 + 4 * F.H.S ∧ F.tO = 8 * F.W + 16 + 4 * F.H.S + F.H.D ∧
    F.hkO = 8 * F.W + 16 + 4 * F.H.S + 2 * F.H.D ∧ F.intO = 8 * F.W + 16 + 4 * F.H.S + 2 * F.H.D + F.H.F := by
  dsimp only [Fns.st0O, Fns.st1O, Fns.stSO, Fns.stWO, Fns.uO, Fns.tO, Fns.hkO, Fns.intO, Fns.L, Hash.buf]
  omega

theorem end_le (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F) : F.intO + 4 ≤ F.L8 := by
  have := VG.Proof.Pbkdf2.Whole.X86.layout (F := F); have := hz.fits; simp only [Fns.L8]; omega

theorem L8_le (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F) : F.L8 ≤ 8 * 512 + 8 * 256 := by
  have := hz.W; have := hz.S; simp only [Fns.L8]; omega

/-- The save area of our caller's registers. -/
abbrev svR (F : Fns) (s₀ : State) : Region := saveR F.L (VG.Proof.Pbkdf2.Whole.X86.scr s₀)

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < F.L8) : (VG.Proof.Pbkdf2.Whole.X86.dO s₀ o).setWidth 64 = VG.Proof.Pbkdf2.Whole.X86.A s₀ o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.setWidth_add (by omega)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (VG.Proof.Pbkdf2.Whole.X86.dO s₀ o).toNat = (VG.Proof.Pbkdf2.Whole.X86.scr s₀).toNat + o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.toNat_add_ofNat (by omega)

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (VG.Proof.Pbkdf2.Whole.X86.sR s₀ o n) (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (VG.Proof.Pbkdf2.Whole.X86.sR s₀ a m) (VG.Proof.Pbkdf2.Whole.X86.sR s₀ b n) := by
  have := VG.Proof.Pbkdf2.Whole.X86.L8_le hz; exact Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (VG.Proof.Pbkdf2.Whole.X86.lowR s₀ k) (VG.Proof.Pbkdf2.Whole.X86.sR s₀ b n) := by
  have := VG.Proof.Pbkdf2.Whole.X86.L8_le hz; exact Offset.base_disjoint _ hk (by omega)

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (VG.Proof.Pbkdf2.Whole.X86.lowR s₀ k) (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (VG.Proof.Pbkdf2.Whole.X86.svR F s₀) (VG.Proof.Pbkdf2.Whole.X86.scR s₀ F) := by
  have := VG.Proof.Pbkdf2.Whole.X86.end_le hz; have := VG.Proof.Pbkdf2.Whole.X86.layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 16 ≤ F.L8; omega)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8) : (VG.Proof.Pbkdf2.Whole.X86.svR F s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.sR s₀ o n) := by
  have := VG.Proof.Pbkdf2.Whole.X86.L8_le hz; exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega)) (by simp only [Fns.L]; omega) (by omega)

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (VG.Proof.Pbkdf2.Whole.X86.svR F s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.lowR s₀ k) := by
  have := VG.Proof.Pbkdf2.Whole.X86.L8_le hz; have := VG.Proof.Pbkdf2.Whole.X86.end_le hz; have := VG.Proof.Pbkdf2.Whole.X86.layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 16) (by simp only [Fns.L]; omega)
    (by simp only [Fns.L]; omega)).symm

omit hz in
theorem sc_mem : VG.Proof.Pbkdf2.Whole.X86.scR s₀ F ∈ s₀.wr := by rw [hp.wr]; simp

theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.L8) :
    InRegions s.wr (VG.Proof.Pbkdf2.Whole.X86.A s₀ o) n := by
  have := VG.Proof.Pbkdf2.Whole.X86.L8_le hz
  exact ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, by rw [hwr]; exact VG.Proof.Pbkdf2.Whole.X86.sc_mem hp, Offset.contains_base _ h (by omega)⟩

end

/-! ## What every piece keeps -/

/-- The regions everything writes: `out`, `scratch` and the stack below `esp`. -/
abbrev wrs (F : Fns) (s₀ : State) : List Region := [VG.Proof.Pbkdf2.Whole.X86.outR s₀, VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, VG.Proof.Pbkdf2.Whole.X86.stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Pbkdf2.Whole.X86.E s₀
  ebp : s.gpr .ebp = VG.Proof.Pbkdf2.Whole.X86.scr s₀
  saved : SavedRegs F.L (VG.Proof.Pbkdf2.Whole.X86.scr s₀) s₀ s.mem
  frame : Frame (VG.Proof.Pbkdf2.Whole.X86.wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp]

theorem kregs_callee : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.kregs, r ∈ calleeSaved := by decide

/-- The 76 bytes below `esp`, while `KR` holds. -/
theorem KR.stkE {s₀ s : State} (h : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) : VG.Proof.Pbkdf2.Whole.X86.stk s = VG.Proof.Pbkdf2.Whole.X86.stkR s₀ := by
  rw [VG.Proof.Pbkdf2.Whole.X86.stk, h.esp]

/-- `KR` survives changes to other registers, and to memory in `out`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Whole.X86.svR F s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.Pbkdf2.Whole.X86.wrs F s₀, Region.Sub r r') :
    VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    h.saved.frame F.L hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Whole.X86.kregs) {v : BitVec 32}
    (u : VG.Proof.Sha256.X86.Stream.Upd s s' d v) : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s' :=
  h.same u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A write to a part of `scratch` after the save area. -/
theorem KR.write {s₀ s s' : State} (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F) (h : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.kregs, s'.gpr r = s.gpr r) {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8)
    (hf : Frame [VG.Proof.Pbkdf2.Whole.X86.sR s₀ o n] s.mem s'.mem) : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s' :=
  h.keep hrd hwr hg hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Whole.X86.sv_disj hz ho hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, VG.Proof.Pbkdf2.Whole.X86.part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after the save area, or
the working space, and the stack below `esp`. -/
theorem KR.call {s₀ s s' : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀) (hz : VG.Proof.Pbkdf2.Whole.X86.Sizes F) (h : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = VG.Proof.Pbkdf2.Whole.X86.lowR s₀ k ∧ k ≤ 8 * F.W) ∨
      ∃ o n, r = VG.Proof.Pbkdf2.Whole.X86.sR s₀ o n ∧ 8 * F.W + 16 ≤ o ∧ o + n ≤ F.L8) : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s' := by
  have hL := VG.Proof.Pbkdf2.Whole.X86.end_le hz; have := VG.Proof.Pbkdf2.Whole.X86.layout (F := F)
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Whole.X86.kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact VG.Proof.Pbkdf2.Whole.X86.sv_low hz hk
      · exact VG.Proof.Pbkdf2.Whole.X86.sv_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.b_s.sub_right (VG.Proof.Pbkdf2.Whole.X86.sv_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact ⟨VG.Proof.Pbkdf2.Whole.X86.scR s₀ F, by simp, VG.Proof.Pbkdf2.Whole.X86.low_sub (F := F) (by omega)⟩
      · exact ⟨_, by simp, VG.Proof.Pbkdf2.Whole.X86.part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

/-! ## The arguments, the return address and the inputs, while `KR` holds -/

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Whole.X86.Pre F s₀)
include hp

omit hp in
theorem argR_eq : VG.Proof.Pbkdf2.Whole.X86.argR s₀ = ⟨addr (VG.Proof.Pbkdf2.Whole.X86.E s₀) 4, 32⟩ := rfl

theorem stk_arg : (VG.Proof.Pbkdf2.Whole.X86.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Whole.X86.argR s₀) := hp.b_a

theorem KR.argEq {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {i : Nat} (hi : i < 8) : VG.X86.arg s i = VG.X86.arg s₀ i := by
  have hd : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.wrs F s₀, Region.Disjoint ⟨addr (VG.Proof.Pbkdf2.Whole.X86.E s₀) 4, 32⟩ r := by
    rw [← VG.Proof.Pbkdf2.Whole.X86.argR_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.b_a.symm
  exact Pbkdf2.Stream.X86.arg_keep rfl hk.esp (n := 32) (by have := hp.spf; omega) hk.frame hd (by omega)

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = VG.Proof.Pbkdf2.Whole.X86.E s₀) (i : Nat) :
    s.ea (VG.Impl.Pbkdf2.Stream.X86.at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [show s.ea (VG.Impl.Pbkdf2.Stream.X86.at_ .esp (4 + 4 * i)) = addr (s.gpr .esp) (4 + 4 * i) from rfl, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 8) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.wr]
  exact ⟨VG.Proof.Pbkdf2.Whole.X86.argR s₀, by simp, by
    rw [VG.Proof.Pbkdf2.Whole.X86.argR_eq]; exact Pbkdf2.Stream.X86.arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

/-- An argument, read from memory while `KR` holds. -/
theorem KR.readArg {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {i : Nat} (hi : i < 8) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by
    rw [Pbkdf2.Stream.X86.argAddr_eq, Pbkdf2.Stream.X86.argAddr_eq, hk.esp]] at this

/-- `mov d, [esp + 4 + 4 i]`: argument `i`, while `KR` holds. -/
theorem wp_arg {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {d : Reg} {i : Nat} (hi : i < 8) {is : List Instr}
    {Q : State → Prop} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (Fns.argM i) :: is)) s Q :=
  VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ i) (VG.Proof.Pbkdf2.Whole.X86.argW hk.esp i) (VG.Proof.Pbkdf2.Whole.X86.argIn hp hk.rd hk.wr hi)
    fun s' u => k s' (by rw [hk.readArg hp hi] at u; exact u)

/-- The return address, while `KR` holds. -/
theorem KR.ret {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    s.mem.readW ((VG.Proof.Pbkdf2.Whole.X86.E s₀).setWidth 64) 32 = s₀.mem.readW ((VG.Proof.Pbkdf2.Whole.X86.E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := VG.Proof.Pbkdf2.Whole.X86.retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_o
    · exact hp.r_s
    · rw [VG.Proof.Pbkdf2.Whole.X86.stkR, below_eq hp.sp76]
      exact (Offset.below_disjoint _ (by omega)).symm) (by decide)

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ VG.Proof.Pbkdf2.Whole.X86.wrs F s₀, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep hk.frame hd hn

theorem KR.pwBytes {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    bytesAt s.mem ((VG.Proof.Pbkdf2.Whole.X86.pw s₀).setWidth 64) (VG.Proof.Pbkdf2.Whole.X86.pwl s₀) = bytesAt s₀.mem ((VG.Proof.Pbkdf2.Whole.X86.pw s₀).setWidth 64) (VG.Proof.Pbkdf2.Whole.X86.pwl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.b_pw.symm) (by have := hp.npw; omega)

theorem KR.saltBytes {s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) :
    bytesAt s.mem ((VG.Proof.Pbkdf2.Whole.X86.salt s₀).setWidth 64) (VG.Proof.Pbkdf2.Whole.X86.sl s₀) = bytesAt s₀.mem ((VG.Proof.Pbkdf2.Whole.X86.salt s₀).setWidth 64) (VG.Proof.Pbkdf2.Whole.X86.sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.b_sa.symm) (by have := hp.nsa; omega)

end

/-- `d ← scratch + o`, while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : VG.Proof.Pbkdf2.Whole.X86.KR F s₀ s) {d : Reg} {o : Nat} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (VG.Proof.Pbkdf2.Whole.X86.dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Stream.X86.scr, List.cons_append, List.nil_append]
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂ u₂ =>
    k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, hk.ebp]

end VG.Proof.Pbkdf2.Whole.X86

end
