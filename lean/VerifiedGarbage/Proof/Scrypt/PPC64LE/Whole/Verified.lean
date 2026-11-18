module

public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha256
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Sha256
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
meta import VerifiedGarbage.Proof.Scrypt.Whole
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Correct
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Correct
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Scrypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Contract
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.BlockMix
import VerifiedGarbage.Proof.Scrypt.PPC64LE.Lit
import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Impl.Scrypt.PPC64LE.Scrypt
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Scrypt.PPC64LE.BlockMix
meta import VerifiedGarbage.Proof.Scrypt.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Scrypt.PPC64LE.Whole.Correct`, which only this module used -/

section

/-! ### `Scrypt.PPC64LE.Whole.Layout`, which only this module used -/

section

/-! ### `Scrypt.PPC64LE.Whole.Contract`, which only this module used -/

section

/-!
# scrypt on PPC64LE: the contract

Untrusted: the contract the proof of `vg_scrypt` is written against
(`scryptPPC`), as on AArch64 (`Proof/Scrypt/AArch64/Whole/Verified.lean`), with
1120 bytes of stack below the stack pointer (`stackBytes`: our 112-byte frame
and the 1008 bytes PBKDF2 uses below it). It implies the shared contract of
`Spec/` (`scrypt_implies`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev stackBytes : Nat := 1120

/-- `vg_scrypt(password = r3, password_len = r4, salt = r5, salt_len = r6,
r = r7, b = r8, blen = r9, v = r10, vlen, scratch, slen, out, out_len)`, the
last five in the caller's Parameter Save Area. -/
def scryptPPC : Contract isa where
  pre s :=
    let vlen := stackArg s 0
    let sc := stackArg s 1
    let slen := stackArg s 2
    let out := stackArg s 3
    let ol := stackArg s 4
    let r := (s.gpr .r7).toNat
    let pwR : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let saltR : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let bR : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 128⟩
    let vR : Region := ⟨s.gpr .r10, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    stackBytes ≤ s.sp.toNat ∧ s.sp.toNat + 136 ≤ 2 ^ 64 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r10).toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .r9).toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r ((s.gpr .r9).toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .r7).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) ((stackArg s 0).toNat / r) r
      ((s.gpr .r9).toNat / r) (stackArg s 4).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 3) (stackArg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat) (s₁.gpr .r7).toNat
        ((s₁.gpr .r9).toNat / (s₁.gpr .r7).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .r7).toNat ((stackArg s₁ 0).toNat / (s₁.gpr .r7).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat) (s₂.gpr .r7).toNat
        ((s₂.gpr .r9).toNat / (s₂.gpr .r7).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .r7).toNat ((stackArg s₂ 0).toNat / (s₂.gpr .r7).toNat))

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
doublewords at `0x90060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r5 => 0x20000 | .r7 => 1 | .r8 => 0x30000 | .r9 => 1 | .r10 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem a := bif Nat.beq a.toNat 0x90060 then 2 else bif Nat.beq a.toNat 0x9006A then 5 else bif Nat.beq a.toNat 0x90070 then 17
    else bif Nat.beq a.toNat 0x9007A then 6 else bif Nat.beq a.toNat 0x90080 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90060, 40⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies : scryptPPC.Implies (Spec.Scrypt.scryptContract PPC64LE.abi stackBytes) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptPPC,
          PPC64LE.abi, PPC64LE.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 h4 h5 h6 h7 a0 a1 a2 a3
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, PPC64LE.abi, PPC64LE.argRegs,
          _root_.List.range, _root_.List.range.loop, List.append_eq, satState] [satState] using satState }

end VG.Proof.Scrypt.PPC64LE.Whole

end

end

/-!
# scrypt on PPC64LE: where everything is

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Verified.lean`): the function's
buffers and the 1120 bytes of stack below the stack pointer, from `B` up
(`Lay`): the 1008 bytes the calls use, then the frame (from `B + 1008`: its
32-byte header, then from `B + 1040` our return address, our caller's `r30`,
the password, its length, `r`, `b`, `blen`, `v` and the next block). Our
stack arguments are at `B + 1216`. `Ctx` is what holds in the frame's body,
and `call_ok` runs a call of verified code in such a state.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE

/-- The arguments, and the lowest byte of the stack used (`sp - 1120` on
entry). -/
structure Lay where
  pw : Addr
  pwl : BitVec 64
  salt : Addr
  sl : BitVec 64
  r : BitVec 64
  b : Addr
  blen : BitVec 64
  v : Addr
  vlen : BitVec 64
  scr : Addr
  slen : BitVec 64
  out : Addr
  ol : BitVec 64
  B : Addr

namespace Lay

variable (L : Lay)

abbrev PW : Region := ⟨L.pw, L.pwl.toNat⟩
abbrev SALT : Region := ⟨L.salt, L.sl.toNat⟩
abbrev BB : Region := ⟨L.b, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨L.v, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨L.scr, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨L.out, L.ol.toNat⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 1216, 40⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 1120⟩
/-- The frame's local variable space. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 1040, 80⟩
/-- The frame's stack pointer. -/
abbrev E : Addr := L.B + BitVec.ofNat 64 1008

/-- `p` and `N`. -/
abbrev pp : Nat := L.blen.toNat / L.r.toNat
abbrev NN : Nat := L.vlen.toNat / L.r.toNat

/-- What the contract says of where the buffers and the stack are, and of
the parameters. -/
structure Ok : Prop where
  pb : L.PW.Disjoint L.BB
  pv : L.PW.Disjoint L.VV
  pc : L.PW.Disjoint L.SC
  po : L.PW.Disjoint L.OUT
  sb : L.SALT.Disjoint L.BB
  sv : L.SALT.Disjoint L.VV
  sc : L.SALT.Disjoint L.SC
  so : L.SALT.Disjoint L.OUT
  bv : L.BB.Disjoint L.VV
  bc : L.BB.Disjoint L.SC
  bo : L.BB.Disjoint L.OUT
  ba : L.BB.Disjoint L.ARGS
  vc : L.VV.Disjoint L.SC
  vo : L.VV.Disjoint L.OUT
  va : L.VV.Disjoint L.ARGS
  co : L.SC.Disjoint L.OUT
  ca : L.SC.Disjoint L.ARGS
  oa : L.OUT.Disjoint L.ARGS
  kp : L.STK.Disjoint L.PW
  ks : L.STK.Disjoint L.SALT
  kb : L.STK.Disjoint L.BB
  kv : L.STK.Disjoint L.VV
  kc : L.STK.Disjoint L.SC
  ko : L.STK.Disjoint L.OUT
  np : L.pw.toNat + L.pwl.toNat ≤ 2 ^ 64
  ns : L.salt.toNat + L.sl.toNat ≤ 2 ^ 64
  nb : L.b.toNat + L.blen.toNat * 128 ≤ 2 ^ 64
  nv : L.v.toNat + L.vlen.toNat * 128 ≤ 2 ^ 64
  nc : L.scr.toNat + L.slen.toNat * 128 ≤ 2 ^ 64
  no : L.out.toNat + L.ol.toNat ≤ 2 ^ 64
  nB : L.B.toNat + 1256 ≤ 2 ^ 64
  rpos : 0 < L.r.toNat
  bmod : L.blen.toNat % L.r.toNat = 0
  vmod : L.vlen.toNat % L.r.toNat = 0
  valid : Spec.Scrypt.valid L.NN L.r.toNat L.pp L.ol.toNat
  olb : L.ol.toNat ≤ (2 ^ 32 - 1) * 32
  slen : L.slen.toNat = L.r.toNat + 16

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_buf {d n : Nat} (h₁ : d + n ≤ 1120) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hr
  · exact (h.kv.sub_left hs).sub_right hr
  · exact (h.kc.sub_left hs).sub_right hr
  · exact (h.ko.sub_left hs).sub_right hr

/-- A range in our stack arguments is disjoint from one in a writable buffer. -/
theorem args_buf {d n : Nat} (h₁ : 1216 ≤ d) (h₂ : d + n ≤ 1256) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega_arith)
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hr
  · exact (h.va.symm.sub_left hs).sub_right hr
  · exact (h.ca.symm.sub_left hs).sub_right hr
  · exact (h.oa.symm.sub_left hs).sub_right hr

end Lay.Ok

/-! ## What the calls cannot change -/

/-- The doublewords of the frame and our stack arguments that stay as they
are in the frame's body: our return address `lr` and our caller's `r30`. -/
structure Kept (L : Lay) (lr r30 : BitVec 64) (m : Mem) : Prop where
  lr : m.readW (L.B + BitVec.ofNat 64 1040) 64 = lr
  r30 : m.readW (L.B + BitVec.ofNat 64 1048) 64 = r30
  pw : m.readW (L.B + BitVec.ofNat 64 1056) 64 = L.pw
  pwl : m.readW (L.B + BitVec.ofNat 64 1064) 64 = L.pwl
  r : m.readW (L.B + BitVec.ofNat 64 1072) 64 = L.r
  b : m.readW (L.B + BitVec.ofNat 64 1080) 64 = L.b
  blen : m.readW (L.B + BitVec.ofNat 64 1088) 64 = L.blen
  v : m.readW (L.B + BitVec.ofNat 64 1096) 64 = L.v
  vlen : m.readW (L.B + BitVec.ofNat 64 1216) 64 = L.vlen
  scr : m.readW (L.B + BitVec.ofNat 64 1224) 64 = L.scr
  out : m.readW (L.B + BitVec.ofNat 64 1240) 64 = L.out
  ol : m.readW (L.B + BitVec.ofNat 64 1248) 64 = L.ol

/-- Where the kept doublewords are. -/
abbrev KeptAt (d : Nat) : Prop := (1040 ≤ d ∧ d + 8 ≤ 1104) ∨ (1216 ≤ d ∧ d + 8 ≤ 1256)

/-- The kept doublewords survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {lr r30 : BitVec 64} {m m' : Mem} {rs : List Region} (hk : Kept L lr r30 m)
    (hf : Frame rs m m')
    (hd : ∀ d, KeptAt d → ∀ R ∈ rs, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R) : Kept L lr r30 m' := by
  have k : ∀ d, KeptAt d →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 1040 (by decide)).trans hk.lr, (k 1048 (by decide)).trans hk.r30, (k 1056 (by decide)).trans hk.pw,
    (k 1064 (by decide)).trans hk.pwl, (k 1072 (by decide)).trans hk.r, (k 1080 (by decide)).trans hk.b,
    (k 1088 (by decide)).trans hk.blen, (k 1096 (by decide)).trans hk.v, (k 1216 (by decide)).trans hk.vlen,
    (k 1224 (by decide)).trans hk.scr, (k 1240 (by decide)).trans hk.out, (k 1248 (by decide)).trans hk.ol⟩

/-! ## In the frame's body -/

/-- The state in the frame's body: `g` are the registers on entry, `lr` the
return address, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (lr : BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.E
  r30 : t.gpr .r30 = L.E
  cs : ∀ r ∈ preserved, r ≠ .r30 → t.gpr r = g r
  kept : Kept L lr (g .r30) t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.ARGS, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-- A writable region is within one of the writable buffers. -/
def InBuf (L : Lay) (r : Region) : Prop :=
  Within r L.BB ∨ Within r L.VV ∨ Within r L.SC ∨ Within r L.OUT

theorem InBuf.sub {L : Lay} {r : Region} (h : InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

theorem covers {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem} {t : State}
    (hc : Ctx L g lr m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- The stack a call from `sp = B + 1008` uses, if it uses at most 1008 bytes. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 1008) :
    Region.Sub (below (B + BitVec.ofNat 64 1008) m) ⟨B, 1008⟩ := by
  have : B + BitVec.ofNat 64 1008 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (1008 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 1008) (a := m) (b := 1008) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 1008 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega_arith)

/-- A call of verified code (see `WP.callAny`), which uses at most 1008 bytes
of stack and is given regions within ours to read, and within the writable
buffers to write: afterwards `Ctx` holds again, memory changed only within
what it writes and the 1008 bytes below `sp`, and the callee's postcondition
holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : sdepth c ≤ 1008) {t : State} (hc : Ctx L g lr m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g lr m₀ s' → Frame (wr ++ [⟨L.B, 1008⟩]) t.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = t.gpr r) →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.callAny hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs hpost => ?_) (by omega_arith)
  have hf' : Frame (wr ++ [⟨L.B, 1008⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.sp]
      exact below_call_sub _ hd
  have hnB := hL.nB
  -- The regions the call may change miss the kept doublewords.
  have hdisj : ∀ d, KeptAt d → ∀ R ∈ wr ++ [⟨L.B, 1008⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R := by
    intro d hdd R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨R', hR', hs⟩ := (hwsub R hR).sub
      rcases hdd with hdd | hdd
      · exact hL.stk_buf (by omega_arith) hR' hs
      · exact hL.args_buf (by omega_arith) (by omega_arith) hR' hs
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hcs _ (by decide)).trans hc.r30,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'), hc.kept.frame hf' hdisj,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hcs hpost
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨R', hR', hs⟩ := (hwsub r hr).sub
    rcases hR' with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Region.sub_prefix (by decide)⟩

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, s.gpr .r6, s.gpr .r7, s.gpr .r8, s.gpr .r9, s.gpr .r10,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    s.sp - BitVec.ofNat 64 1120⟩

theorem lay_top (s : State) : (lay s).B + BitVec.ofNat 64 1120 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (lay s).B + BitVec.ofNat 64 1216 = stackArgAddr s 0 := by
  simp only [lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : scryptPPC.pre s) : (lay s).Ok := by
  obtain ⟨hst, h136, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea : (lay s).ARGS = ⟨stackArgAddr s 0, 40⟩ := by simp only [Lay.ARGS, lay_args]
  have nB : (lay s).B.toNat + 1256 ≤ 2 ^ 64 := by
    simp only [lay]
    simp only [stackBytes] at hst
    rw [Offset.toNat_sub_ofNat s.sp 1120]
    omega_arith
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, nB, rpos, bmod, vmod, hval, olb, slen⟩

end VG.Proof.Scrypt.PPC64LE.Whole

end

end

/-! ### `Scrypt.PPC64LE.Whole.Steps`, which only this module used -/

section

/-!
# scrypt on PPC64LE: the blocks between the calls

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Verified.lean`): the facts about
the parameters the proof uses; reading and writing the frame in `Ctx`; and
each block between the calls (`setup` from the frame's push, the moves of
the calls' arguments, the next block, `restore`), keeping `Ctx` and giving
the calls' arguments (`PbkArgs`, `RomixArgs`) or the next block.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE.Whole

/-! ## Arithmetic -/

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega_using [hR]
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hS]

theorem lsl7 (x : BitVec 64) : x <<< 7 = BitVec.ofNat 64 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

/-- `b` is not the whole address space, since the stack is not in it. -/
theorem blen_lt : L.blen.toNat * 128 < 2 ^ 64 :=
  toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 1120; omega_using [])

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 64 := by have := h.blen_lt; have := h.r_le; omega_arith

/-- `128 r p`, the length of `b`. -/
theorem len_b : 128 * L.r.toNat * L.pp = L.blen.toNat * 128 := by
  rw [h.blen_eq, Nat.mul_comm 128, Nat.mul_assoc, Nat.mul_comm 128, Nat.mul_assoc]

/-- The derived key of step 1 is not too long for PBKDF2. -/
theorem ol1 : L.blen.toNat * 128 ≤ (2 ^ 32 - 1) * 32 := by
  have h₁ := h.valid.2.2.2.2.1
  have h₂ := Nat.div_mul_le_self ((2 ^ 32 - 1) * 32) (128 * L.r.toNat)
  have h₃ : L.pp * (128 * L.r.toNat) ≤ (2 ^ 32 - 1) * 32 / (128 * L.r.toNat) * (128 * L.r.toNat) :=
    Nat.mul_le_mul_right _ h₁
  rw [← h.len_b, Nat.mul_comm (128 * L.r.toNat)]
  omega_using [h₂, h₃]

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega_arith

end Lay.Ok

/-! ## In the frame -/

/-- A register other than the callee-saved ones keeps them. -/
theorem gpr_write_pres {s : State} {r d : Reg} {v : BitVec 64} (hr : r ∈ preserved) (hd : d ∉ preserved) :
    (s.write d v).gpr r = s.gpr r :=
  RegUpd.gpr_write_of_ne _ _ fun e => hd (e ▸ hr)

/-- Reading a doubleword past a write of another. -/
theorem readW_writeW_off (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 64) (h : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x + 8 ≤ 2 ^ 64) (hy : y + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hx hy) (by decide)

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- The address of a doubleword of the frame (`r30 = B + 1008`). -/
theorem fr_addr (B : Addr) (d : Nat) :
    B + BitVec.ofNat 64 1008 + BitVec.ofNat 64 d = B + BitVec.ofNat 64 (1008 + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The frame's cur slot. -/
abbrev curR (L : Lay) : Region := ⟨L.B + BitVec.ofNat 64 1104, 8⟩

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g lr m₀ t)
include hc

theorem r30' : t.gpr .r30 = L.B + BitVec.ofNat 64 1008 := hc.r30

theorem inFr {d : Nat} (h₁ : 1040 ≤ d) (h₂ : d + 8 ≤ 1120) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inFrW {d : Nat} (h₁ : 1040 ≤ d) (h₂ : d + 8 ≤ 1120) : InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inArgs {d : Nat} (h₁ : 1216 ≤ d) (h₂ : d + 8 ≤ 1256) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

/-- Code that writes only registers other than the callee-saved ones. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) : Ctx L g lr m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.r30,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hm]; exact hc.kept, by rw [hm]; exact hc.frame⟩

/-- Code that also writes the frame's cur slot. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hf : Frame [curR L] t.mem t'.mem) : Ctx L g lr m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.r30,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun d hd R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega_using [])
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega_using [])⟩

end Ctx

/-- The callee-saved registers through the writes of a block that writes
none of them. -/
macro "pres_tac" : tactic => `(tactic| (
  intro r hr
  simp (disch := decide) only [gpr_write_pres hr]))

/-- The simp set running a block in the frame. -/
macro "frame_run" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, fld, argOff, locals, lrOff, r30Off, pwOff, pwlOff,
    rOff, bOff, blenOff, vOff, curOff, vlenArg, scratchArg, outArg, outLenArg,
    exec_ld, exec_std, exec_li, exec_lsl, exec_add, exec_sub, exec_addi', exec_mtlr,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, RegUpd.lr_write, fr_addr, ne_eq, reduceCtorEq, not_false_eq_true,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reducePow, and_self,
    Option.some.injEq, exists_eq_left', $ls,*]))

/-! ## The blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, `c = 1` and `scratch`. -/
structure PbkArgs (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  r3 : t.gpr .r3 = L.pw
  r4 : t.gpr .r4 = L.pwl
  r5 : t.gpr .r5 = salt
  r6 : t.gpr .r6 = sl
  r7 : t.gpr .r7 = 1
  r8 : t.gpr .r8 = out
  r9 : t.gpr .r9 = ol
  r10 : t.gpr .r10 = L.scr

/-- The registers on entry to the frame's body, once our arguments are saved. -/
structure Entry (L : Lay) (t : State) : Prop where
  r3 : t.gpr .r3 = L.pw
  r4 : t.gpr .r4 = L.pwl
  r5 : t.gpr .r5 = L.salt
  r6 : t.gpr .r6 = L.sl
  r8 : t.gpr .r8 = L.b
  r9 : t.gpr .r9 = L.blen

theorem pbk1Args_ok {t : State} (hc : Ctx L g lr m₀ t) (he : Entry L t) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' := by
  have l1224 := hc.inArgs (d := 1224) (by omega_using []) (by omega_using [])
  frame_run [pbk1Args, hc.r30', l1224, hc.kept.scr]
  refine ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, ?_⟩
  exact ⟨he.r3, he.r4, he.r5, he.r6, rfl, he.r8, by rw [he.r9, lsl7]; rfl, rfl⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block cur0) t fun t' => Ctx L g lr m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = L.b ∧ Frame [curR L] t.mem t'.mem := by
  have l1080 := hc.inFr (d := 1080) (by omega_using []) (by omega_using [])
  have w1104 := hc.inFrW (d := 1104) (by omega_using []) (by omega_using [])
  frame_run [cur0, hc.r30', l1080, w1104, hc.kept.b]
  have f : Frame [curR L] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 1104) L.b) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.store hL rfl rfl rfl (by pres_tac) f, Mem.readW_writeW_self64 _ _ _, f⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : Addr) (t : State) : Prop where
  r3 : t.gpr .r3 = cur
  r4 : t.gpr .r4 = L.r
  r5 : t.gpr .r5 = L.v
  r6 : t.gpr .r6 = L.vlen
  r7 : t.gpr .r7 = L.scr
  r8 : t.gpr .r8 = L.r + BitVec.ofNat 64 2

theorem romixArgs_ok {t : State} (hc : Ctx L g lr m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ RomixArgs L cur t' := by
  have l1104 := hc.inFr (d := 1104) (by omega_using []) (by omega_using [])
  have l1072 := hc.inFr (d := 1072) (by omega_using []) (by omega_using [])
  have l1096 := hc.inFr (d := 1096) (by omega_using []) (by omega_using [])
  have l1216 := hc.inArgs (d := 1216) (by omega_using []) (by omega_using [])
  have l1224 := hc.inArgs (d := 1224) (by omega_using []) (by omega_using [])
  frame_run [romixArgs, hc.r30', l1104, l1072, l1096, l1216, l1224, hcur, hc.kept.r, hc.kept.v,
    hc.kept.vlen, hc.kept.scr]
  exact ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => Ctx L g lr m₀ t' ∧ Frame [curR L] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.gpr .r5 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
  have l1104 := hc.inFr (d := 1104) (by omega_using []) (by omega_using [])
  have w1104 := hc.inFrW (d := 1104) (by omega_using []) (by omega_using [])
  have l1072 := hc.inFr (d := 1072) (by omega_using []) (by omega_using [])
  have l1080 := hc.inFr (d := 1080) (by omega_using []) (by omega_using [])
  have l1088 := hc.inFr (d := 1088) (by omega_using []) (by omega_using [])
  frame_run [nextBlock, hc.r30', l1104, w1104, l1072, l1080, l1088, hcur, hc.kept.r, hc.kept.b,
    hc.kept.blen, lsl7]
  have f : Frame [curR L] t.mem
      (t.mem.writeW (L.B + BitVec.ofNat 64 1104) (cur + BitVec.ofNat 64 (L.r.toNat * 128))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.store hL rfl rfl rfl (by pres_tac) f, f, Mem.readW_writeW_self64 _ _ _, ?_⟩
  show _ - _ = _
  rw [readW_writeW_off (x := 1080) (y := 1104) _ _ _ (by decide) (by decide) (by decide),
    readW_writeW_off (x := 1088) (y := 1104) _ _ _ (by decide) (by decide) (by decide), hc.kept.b, hc.kept.blen]

theorem pbk2Args_ok {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' := by
  have l1056 := hc.inFr (d := 1056) (by omega_using []) (by omega_using [])
  have l1064 := hc.inFr (d := 1064) (by omega_using []) (by omega_using [])
  have l1080 := hc.inFr (d := 1080) (by omega_using []) (by omega_using [])
  have l1088 := hc.inFr (d := 1088) (by omega_using []) (by omega_using [])
  have l1224 := hc.inArgs (d := 1224) (by omega_using []) (by omega_using [])
  have l1240 := hc.inArgs (d := 1240) (by omega_using []) (by omega_using [])
  have l1248 := hc.inArgs (d := 1248) (by omega_using []) (by omega_using [])
  frame_run [pbk2Args, hc.r30', l1056, l1064, l1080, l1088, l1224, l1240, l1248, hc.kept.pw, hc.kept.pwl,
    hc.kept.b, hc.kept.blen, hc.kept.scr, hc.kept.out, hc.kept.ol, lsl7]
  exact ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The return address back in the link register and our caller's `r30` back. -/
theorem restore_ok {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block restore) t fun t' => t'.lr = lr ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ ∀ r ∈ preserved, t'.gpr r = g r := by
  have l1040 := hc.inFr (d := 1040) (by omega_using []) (by omega_using [])
  have l1048 := hc.inFr (d := 1048) (by omega_using []) (by omega_using [])
  frame_run [restore, hc.r30', l1040, l1048, hc.kept.lr, hc.kept.r30]
  refine ⟨by trivial, by trivial, by trivial, by trivial, by trivial, fun r hr => ?_⟩
  by_cases e : r = .r30
  · subst e; exact RegUpd.gpr_write_self _ _ _
  · rw [RegUpd.gpr_write_of_ne _ _ e]
    exact (gpr_write_pres hr (by decide)).trans (hc.cs r hr e)

/-! ## Entering the frame -/

theorem alloc_sp (s : State) : (allocated 112 s).sp = (lay s).B + BitVec.ofNat 64 1008 := by
  show s.sp - BitVec.ofNat 64 112 = s.sp - BitVec.ofNat 64 1120 + BitVec.ofNat 64 1008
  bv_omega

theorem alloc_wr (s : State) : (allocated 112 s).wr = (lay s).FR :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 112 + 32, 112 - 32⟩ : Region) :: s.wr = _
  rw [show s.sp - BitVec.ofNat 64 112 + 32 = (lay s).B + BitVec.ofNat 64 1040 by
    show _ = s.sp - BitVec.ofNat 64 1120 + _; bv_omega]

theorem alloc_mem (s : State) : (allocated 112 s).mem = s.mem.writeW ((lay s).B + BitVec.ofNat 64 1008) s.sp := by
  show s.mem.write (s.sp - BitVec.ofNat 64 112) 8 s.sp = _
  rw [show s.sp - BitVec.ofNat 64 112 = (lay s).B + BitVec.ofNat 64 1008 from alloc_sp s, write8]

theorem alloc_gpr (s : State) : (allocated 112 s).gpr = s.gpr := rfl
theorem alloc_lr (s : State) : (allocated 112 s).lr = s.lr := rfl
theorem arg_slot (s : State) (i : Nat) (hi : i < 5) :
    stackArgAddr s i = (lay s).B + BitVec.ofNat 64 (1216 + 8 * i) := by
  simp only [stackArgAddr, lay]
  have : 8 * i < 2 ^ 64 := by omega_using [hi]
  bv_omega

theorem exec_addSp0 {s : State} {d : Reg} : exec (.addSp d 0) s = some (s.write d s.sp) := by
  simp [exec]

theorem add_ofNat_zero (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

theorem entry_ok {s : State} (h : scryptPPC.pre s) :
    WP isa (.block setup) (allocated locals s) fun t => Ctx (lay s) s.gpr s.lr s.mem t ∧ Entry (lay s) t := by
  have hL := lay_ok h
  have hnB := hL.nB
  have hw : ∀ d, 1040 ≤ d → d + 8 ≤ 1120 →
      InRegions (allocated 112 s).wr ((lay s).B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨(lay s).FR, by rw [alloc_wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩
  have w1040 := hw 1040 (by omega_using []) (by omega_using [])
  have w1048 := hw 1048 (by omega_using []) (by omega_using [])
  have w1056 := hw 1056 (by omega_using []) (by omega_using [])
  have w1064 := hw 1064 (by omega_using []) (by omega_using [])
  have w1072 := hw 1072 (by omega_using []) (by omega_using [])
  have w1080 := hw 1080 (by omega_using []) (by omega_using [])
  have w1088 := hw 1088 (by omega_using []) (by omega_using [])
  have w1096 := hw 1096 (by omega_using []) (by omega_using [])
  frame_run [setup, exec_addSp0, exec_mflr, alloc_sp, alloc_gpr, alloc_lr, add_ofNat_zero, w1040, w1048,
    w1056, w1064, w1072, w1080, w1088, w1096]
  have ka : ∀ i, i < 5 → s.mem.readW ((lay s).B + BitVec.ofNat 64 (1216 + 8 * i)) 64 = stackArg s i :=
    fun i hi => by rw [stackArg, arg_slot s i hi]
  have k0 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1216) 64 = (lay s).vlen := ka 0 (by decide)
  have k1 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1224) 64 = (lay s).scr := ka 1 (by decide)
  have k3 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1240) 64 = (lay s).out := ka 3 (by decide)
  have k4 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1248) 64 = (lay s).ol := ka 4 (by decide)
  refine ⟨⟨?_, ?_, rfl, RegUpd.gpr_write_self _ _ _, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show s.rd = _
    rw [h.2.2.1, ← lay_args]; rfl
  · show (allocated 112 s).wr = _
    rw [alloc_wr, h.2.2.2.1]; rfl
  · intro r hr hr'
    rw [RegUpd.gpr_write_of_ne _ _ hr']
    dsimp only
    rw [gpr_write_pres hr (by decide), gpr_write_pres hr (by decide)]; rfl
  · constructor <;>
      simp (disch := decide) only [RegUpd.mem_write, alloc_mem, readW_writeW_off, Mem.readW_writeW_self64,
        k0, k1, k3, k4] <;> rfl
  · rw [RegUpd.mem_write]
    dsimp only
    rw [alloc_mem]
    refine Frame.sub (rs := [(lay s).STK]) ?_ fun r hr => ?_
    · repeat refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega_using []))
      exact Frame.refl _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Scrypt.PPC64LE.Whole

end

end


/-!
# scrypt on PPC64LE: correctness

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Verified.lean`).
`vg_pbkdf2_hmac_sha256_scratch` (any implementation of it using at most
1008 bytes of stack) is verified against the shared contract
`(Proof.Pbkdf2.Instance.pbkdf2ScratchContract VG.Spec.Hmac.sha256I)`; we call it under that contract
spelt out (`pbkK`, the contract its proof is written against): `pbk_call`.
`romix_call` calls `vg_scrypt_romix`. Step 1 leaves the blocks `X k` of
`PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`); step 3
derives the key from them (`step3_ok`). `scrypt_ok` puts the frame around it.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE.Whole
open VG.Proof.Pbkdf2.Whole.PPC64LE (pbkG)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

/-! ## PBKDF2-HMAC-SHA256 as a callee -/

/-- `pbkdf2`'s contract, spelt out. -/
abbrev pbkK : Contract isa := pbkG Spec.Hmac.sha256S 1600 1008

theorem pbk_pre {s : State} (h : pbkK.pre s) :
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008).pre s := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre,
    Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, PPC64LE.abi, PPC64LE.argRegs]
  simp only [pbkK, pbkG, Spec.Hmac.sha256S] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega_arith

theorem pbk_post {s s' : State} (h : (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008).post s s') :
    pbkK.post s s' := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre,
    Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, PPC64LE.abi, PPC64LE.argRegs] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkK.pub s₁ s₂) :
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008).pub s₁ s₂ := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre,
    Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, PPC64LE.abi, PPC64LE.argRegs]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h9, h1, h2, h3, h4, h5, h6, h7, h8⟩

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
include hv

theorem pbk_correct (s : State) (h : pbkK.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (pbk_pre h)
  exact ⟨t, s', he, ha, pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (pbk_pre h₁) (pbk_pre h₂) (pbk_pub hp) e₁ e₂

end

/-! ## The calls -/

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}

theorem Ctx.ce_sp {t : State} (hc : Ctx L g lr m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).sp = L.B + BitVec.ofNat 64 1008 := by
  rw [State.withRegions_sp, State.callEntry_sp, hc.sp]

theorem sub1008 (B : Addr) : B + BitVec.ofNat 64 1008 - BitVec.ofNat 64 1008 = B := BitVec.add_sub_cancel _ _

theorem sub48 (B : Addr) : B + BitVec.ofNat 64 1008 - 48 = B + BitVec.ofNat 64 960 := by
  rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, Offset.sub_ofNat_eq _ (by decide : 48 ≤ 1008), BitVec.add_sub_cancel]

namespace Lay.Ok

variable (hL : L.Ok)
include hL

/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs]

theorem stk_in {d n : Nat} (h₁ : d + n ≤ 1120) {r : Region} (h : InBuf L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  exact hL.stk_buf h₁ hR hs

/-- The 1008 bytes the calls use miss every writable buffer. -/
theorem low_in {r : Region} (h : InBuf L r) : Region.Disjoint ⟨L.B, 1008⟩ r := by
  have := hL.stk_in (d := 0) (n := 1008) (by omega_arith) h
  simpa using this

theorem scr_in : InBuf L ⟨L.scr, 1600⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega_arith))))

end Lay.Ok

/-! ### PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt : Addr) (sl : BitVec 64) : List Region := [L.PW, ⟨salt, sl.toNat⟩]
abbrev pbkWr (L : Lay) (out : Addr) (ol : BitVec 64) : List Region := [⟨out, ol.toNat⟩, ⟨L.scr, 1600⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨salt, sl.toNat⟩ R
  ow : InBuf L ⟨out, ol.toNat⟩
  so : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨out, ol.toNat⟩
  sc : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨L.scr, 1600⟩
  oc : Region.Disjoint ⟨out, ol.toNat⟩ ⟨L.scr, 1600⟩
  ks : L.STK.Disjoint ⟨salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 64
  no : out.toNat + ol.toNat ≤ 2 ^ 64
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hnB := hL.nB
  have t1008 : (L.B + BitVec.ofNat 64 1008).toNat = L.B.toNat + 1008 := toNat_add_ofNat _ (by omega_arith)
  have sw : InBuf L ⟨L.scr, 1600⟩ := hL.scr_in
  have lo : Region.Sub ⟨L.B, 1008⟩ L.STK := by simpa using Offset.sub_base L.B (d := 0) (n := 1008) (k := 1120) (by omega_arith)
  simp only [pbkK, pbkG, below, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr,
    hc.ce_sp, sub1008, t1008, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r9 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r10 ∉ linkRegs), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, ha.r9, ha.r10]
  exact ⟨trivial, trivial, hL.pw_buf hr.ow, hL.pw_buf sw, hr.so, hr.sc, hr.oc, by omega_arith,
    hL.kp.sub_left lo, hr.ks.sub_left lo, hL.low_in hr.ow, hL.low_in sw, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega_arith, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr L out ol, ∃ R ∈ L.regions, Within r R := by
  have hs := hr.sw
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (Nat.le_refl _)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen17; omega_arith)⟩

theorem pbk_wsub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) : ∀ r ∈ pbkWr L out ol, InBuf L r := by
  simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hr.ow
  · exact hL.scr_in

theorem pbk_call (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
    (hd : sdepth pbk ≤ 1008) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g lr m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g lr m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.scr, 1600⟩, ⟨L.B, 1008⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  refine call_ok hL (pbk_correct hv) hd hc (pbk_pre' hL hc ha hr) (pbk_sub hL hr) (pbk_wsub hL hr)
    fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [pbkK, pbkG, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r9 ∉ linkRegs), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8,
    ha.r9] at h
  exact h

end

/-! ### ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, (L.r.toNat + 2) * 128⟩]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkAt L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

theorem r2 (hL : L.Ok) : (L.r + BitVec.ofNat 64 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  exact toNat_add_ofNat _ (by omega_arith)

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    Proof.Scrypt.roMixPPC64LE.pre (t.callEntry.withRegions [] (romixWr L i)) := by
  have hnB := hL.nB
  have hb := blk_in hL hi
  have hv : InBuf L ⟨L.v, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith))))
  have tb : (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    have := blk_le hL hi; have := hL.nb; have := hL.rpos
    exact toNat_add_ofNat _ (by omega_arith)
  have t1008 : (L.B + BitVec.ofNat 64 1008).toNat = L.B.toNat + 1008 := toNat_add_ofNat _ (by omega_arith)
  simp only [Proof.Scrypt.roMixPPC64LE, State.withRegions_rd, State.withRegions_wr, hc.ce_sp, sub48, t1008,
    gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
    ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, r2 hL]
  have kb := Within.sub (within_off L.b (blk_le hL hi))
  have ks := Within.sub (within_base L.scr (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega_arith))
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    by omega_arith, hL.stk_in (by omega_arith) hb, hL.stk_in (by omega_arith) hv, hL.stk_in (by omega_arith) hs,
    by rw [tb]; have := blk_le hL hi; have := hL.nb; omega_arith, hL.nv,
    by have := hL.nc; have := hL.slen; omega_arith, hL.rpos, hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ ([] : List Region) ++ romixWr L i, ∃ R ∈ L.regions, Within r R := by
  simp only [romixWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.BB, by simp, within_off _ (blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen; omega_arith)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith))))

theorem roMix_sdepth : sdepth Impl.Scrypt.PPC64LE.roMix ≤ 1008 := by lit_decide

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.PPC64LE.roMix) t fun t' => Ctx L g lr m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.B, 1008⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkAt L i) (128 * L.r.toNat)) := by
  refine call_ok hL RoMix.roMix_correct roMix_sdepth hc (romix_pre hL hc hi ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [Proof.Scrypt.roMixPPC64LE, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs), ha.r3, ha.r4, ha.r6] at h
  exact h

end

/-! ## The password, the salt and the blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : Ctx L g lr m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem L.pw L.pwl.toNat = bytesAt m₀ L.pw L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega_arith)

theorem salt_bytes : bytesAt t.mem L.salt L.sl.toNat = bytesAt m₀ L.salt L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega_arith)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
    (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m L.b (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkAt L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
      (L.pp * 128 * L.r.toNat) = some (bytesAt m L.b (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ ⟨blkAt L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.nb
  have hr := hL.rpos
  refine Offset.disjoint _ ?_ (by omega_arith) (by omega_arith)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega_arith
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega_arith

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega_arith)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr, 1600⟩ L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega_arith))

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
  (hd : sdepth pbk ≤ 1008) (name : String)
include hv hd

omit hv hd in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [toNat_ofNat_lt hb]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_ofNat_lt hb]; exact hL.sb
  · exact hL.sc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]
    exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.nb
  · rw [toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (ha : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => Ctx L g lr m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hd name hL hc ha (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (he : Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g lr m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k :=
  WP.seq (WP.mono (pbk1Args_ok hc he) fun _ ⟨hc₁, _, ha₁⟩ => pbk1_call_ok hv hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 64) (lr : BitVec 64) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g lr m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-- A block of `b` misses the frame's cur slot. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ (curR L) :=
  (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Offset.sub_base _ (by omega_arith))

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :
    WP isa (.block cur0) t (Inv L g lr m₀ 0) :=
  WP.mono (cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', hb.trans (blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
      (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)⟩

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 64 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

/-- The bytes of `b` left after block `i`, as the loop's condition reads them. -/
theorem left_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - blkAt L (i + 1) != 0) = decide (i + 1 ≠ L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 64 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega_arith
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [bne, Offset.ofNat_sub_ofNat_beq e₂ e₁, decide_not]
  refine congrArg (!·) (decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact (Nat.eq_of_mul_eq_mul_left (by omega_arith) h).symm

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g lr m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.PPC64LE.roMix) t fun t' =>
      Ctx L g lr m₀ t' ∧ Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega_arith) (blk_in hL hi)
    · exact hL.stk_in (by omega_arith) (.inr (.inl (within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega_arith) (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith)))))
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (blkAt L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact blk_disj hL hk hi hki
          · exact hL.bv.sub_left (blk_sub hL hk)
          · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
              (Within.sub (within_base _ (by have := hL.slen; omega_arith)))
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Region.sub_prefix (by omega_arith)))
          (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega_arith
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega_arith
        simp only [hlt, this, ite_false]

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g lr m₀ t)
    (hm : Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g lr m₀ t' ∧ InvB L m₀ (i + 1) t' ∧
      (t'.gpr .r5 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.mono (nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hx₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
        (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)⟩,
      by rw [hx₃, next_eq, left_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g lr m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.PPC64LE.roMix)
      (.block nextBlock))) t fun t' =>
        Inv L g lr m₀ (i + 1) t' ∧ (t'.gpr .r5 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.seq (WP.mono (romixArgs_ok h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (call_step hL hi hc₁ ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => WP.mono (next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g lr m₀ 0 t) :
    WP isa romixLoop t (Inv L g lr m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g lr m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
  (hd : sdepth pbk ≤ 1008) (name : String)
include hv hd

omit hv hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g lr m₀ L.pp t) :
    bytesAt t.mem L.b (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hd in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_ofNat_lt hb]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_ofNat_lt hb]; exact hL.bo
  · rw [toNat_ofNat_lt hb]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.kb
  · rw [toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g lr m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g lr m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (pbk2Args_ok h.1) fun t₁ ⟨hc₁, hm₁, ha₁⟩ => ?_)
  refine WP.mono (pbk_call hv hd name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [toNat_ofNat_lt hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

/-- The frame's body after `setup` and before `restore`. -/
theorem rest_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (he : Entry L t) {Q : State → Prop}
    (hQ : ∀ t', Ctx L g lr m₀ t' →
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) → WP isa (.block restore) t' Q) :
    WP isa (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop
      (.seq (pbkCall name pbk pbk2Args) (.block restore))))) t Q := by
  refine WP.seq (WP.mono (step1_ok hv hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (step3_ok hv hd name hL h₃) fun t₄ ⟨hc₄, hp⟩ => hQ t₄ hc₄ ?_)
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem L.b (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

end

end

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
  (hd : sdepth pbk ≤ 1008) (name : String)
include hv hd

/-- `vg_scrypt` meets `scryptPPC` and the calling convention. -/
theorem scrypt_ok {s : State} (h : scryptPPC.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ scryptPPC.post s s' := by
  have hL := lay_ok h
  have h1120 : 1120 ≤ s.sp.toNat := h.1
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by simp only [locals]; omega_arith) ?_
  refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, he⟩ => ?_)
  refine rest_ok hv hd name hL hc he fun u hu ho => WP.mono (restore_ok hu) fun v ⟨vlr, vm, vsp, _, _, vg⟩ mL _ fl => ?_
  refine ⟨⟨fun r hr => vg r hr, ?_, vlr⟩, ?_⟩
  · show v.sp + BitVec.ofNat 64 112 = s.sp
    rw [vsp, hu.sp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact lay_top s
  · -- The `free` loses the frame's bytes, which lie apart from the output.
    refine Eq.trans ?_ (congrArg some (List.map_congr_left fun i hi =>
      (lost_byte fl (R := (lay s).OUT)
        (hL.ko.symm.sub_right (Offset.sub_below _ (by simp only [locals]; decide)
          (by simp only [locals]; decide))) (List.mem_range.mp hi)).symm))
    show _ = some (bytesAt v.mem _ _)
    rw [vm]
    exact ho

end

end VG.Proof.Scrypt.PPC64LE.Whole

end

end

/-!
# scrypt on PPC64LE: constant time, up to the indices `j`, and the shared contract

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Verified.lean`): two runs whose
public data agree have the same layout, so in the frame's body they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs), whatever their secrets, and the indices of all the scryptROMix
calls agree (`LeakEq`). The blocks address only the frame, from `r30`, which
`Ctx` fixes (the taint analysis); each call is of constant-time code whose
public data agree (`RelCT.call`); the loop's branch agrees since both runs
count the same blocks. The frame leaks only the stack pointer
(`RelCT.alloc`).

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified
against its shared contract with at most 1008 bytes of stack, is verified
against `Spec.Scrypt.scryptContract` for the 1120 bytes of stack its frame
and calls use (`scrypt_verified_of`); and so is the one calling PBKDF2 made
with SHA-256 (`scrypt_verified`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE.Whole
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  lr₁ : BitVec 64
  lr₂ : BitVec 64
  m₁ : Mem
  m₂ : Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ LeakEq e.L e.m₁ e.m₂ ∧ Ctx e.L e.g₁ e.lr₁ e.m₁ a ∧ Ctx e.L e.g₂ e.lr₂ e.m₂ b ∧
    Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g lr m₀ (t : State), L.Ok → Ctx L g lr m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g lr m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- Two states in the frame's body agree on the stack pointer and `r30`. -/
theorem agree_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {lr₁ lr₂ : BitVec 64}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ lr₁ m₁ t₁) (c₂ : Ctx L g₂ lr₂ m₂ t₂) :
    VG.PPC64LE.Taint.Agree (Taint.ofRegs [.r30]) t₁ t₂ :=
  ⟨c₁.sp.trans c₂.sp.symm, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr
    exact c₁.r30.trans c₂.r30.symm⟩

/-- A block whose addresses depend only on `r30`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.PPC64LE.Taint.T}
    (h : (taint.check (Taint.ofRegs [.r30]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g lr m₀ (t : State), L.Ok → Ctx L g lr m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g lr m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (RelCT.taint (A := taint) (Taint.ofRegs [.r30])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_two c₁ c₂) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g lr m₀ (t : State), L.Ok → Ctx L g lr m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ lr₁ lr₂ m₁ m₂, L.Ok → LeakEq L m₁ m₂ → Ctx L g₁ lr₁ m₁ t₁ →
      Ctx L g₂ lr₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, InBuf L r)
    (hw : ∀ (L : Lay) g lr m₀ (t : State), L.Ok → Ctx L g lr m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g lr m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
    have w₁ := covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)
    have w₂ := covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)
    exact RelCT.call (n := n) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
          hpub _ _ _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, w₁.1, w₁.2, w₂.1, w₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-! ## The calls -/

theorem pbk_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64} {lr₁ lr₂ : BitVec 64} {m₁ m₂ : Mem}
    {t₁ t₂ : State} (c₁ : Ctx L g₁ lr₁ m₁ t₁) (c₂ : Ctx L g₂ lr₂ m₂ t₂) {salt : Addr} {sl : BitVec 64}
    {out : Addr} {ol : BitVec 64} (a₁ : PbkArgs L salt sl out ol t₁) (a₂ : PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      (t₂.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  simp only [pbkK, Proof.Pbkdf2.Whole.PPC64LE.pbkG, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r9 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r10 ∉ linkRegs), a₁.r3, a₁.r4, a₁.r5, a₁.r6, a₁.r7, a₁.r8, a₁.r9,
    a₁.r10, a₂.r3, a₂.r4, a₂.r5, a₂.r6, a₂.r7, a₂.r8, a₂.r9, a₂.r10, c₁.ce_sp, c₂.ce_sp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} {m₀ : Mem} {t : State} {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t)
    (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (blkAt L i) (128 * L.r.toNat) = X L m₀ i := by
  rw [State.withRegions_mem, State.callEntry_mem, hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64} {lr₁ lr₂ : BitVec 64}
    {m₁ m₂ : Mem} {t₁ t₂ : State} (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ lr₁ m₁ t₁)
    (c₂ : Ctx L g₂ lr₂ m₂ t₂) {i : Nat} (hi : i < L.pp) (b₁ : InvB L m₁ i t₁) (b₂ : InvB L m₂ i t₂)
    (a₁ : RomixArgs L (blkAt L i) t₁) (a₂ : RomixArgs L (blkAt L i) t₂) :
    Proof.Scrypt.roMixPPC64LE.pub (t₁.callEntry.withRegions [] (romixWr L i))
      (t₂.callEntry.withRegions [] (romixWr L i)) := by
  simp only [Proof.Scrypt.roMixPPC64LE, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs), a₁.r3, a₁.r4, a₁.r5, a₁.r6, a₁.r7, a₁.r8, a₂.r3,
    a₂.r4, a₂.r5, a₂.r6, a₂.r7, a₂.r8, c₁.ce_sp, c₂.ce_sp, true_and,
    romix_bytes hi b₁, romix_bytes hi b₂]
  exact leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.PPC64LE.roMix) (.block nextBlock)))
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .r5 != 0) = decide (L.pp - n + 1 ≠ L.pp)) := by
  have a : RelCT isa (Two (LoopAt n)) (.block romixArgs) (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc ⟨h0, hn, hb⟩ =>
      WP.mono (romixArgs_ok hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t) (.call "vg_scrypt_romix" Impl.Scrypt.PPC64LE.roMix)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) :=
    two_call RoMix.roMix_correct RoMix.roMix_ct (fun _ => []) (fun L => romixWr L (L.pp - n))
      (fun _ _ _ _ _ hL hc ⟨h0, hn, _, ha⟩ => romix_pre hL hc (by omega_using [h0, hn]) ha)
      (fun _ _ _ _ _ _ _ _ _ _ hk c₁ c₂ ⟨h0, hn, b₁, a₁⟩ ⟨_, _, b₂, a₂⟩ =>
        romix_pub_two hk c₁ c₂ (by omega_using [h0, hn]) b₁ b₂ a₁ a₂)
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_sub hL (by omega_using [h0, hn]))
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_wsub hL (by omega_using [h0, hn]))
      (fun _ _ _ _ _ hL hc ⟨h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega_using [h0, hn]) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) (.block nextBlock)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .r5 != 0) = decide (L.pp - n + 1 ≠ L.pp)) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      WP.mono (next_step hL (by omega_using [h0, hn]) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', h0, hn, hb, hz⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) romixLoop (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval (.nonzero .d .r5) x = some (x.gpr .r5 != 0) := fun x =>
    eval_nonzero x .r5
  have h := fun n => RelCT.loop (M := isa) (c := .nonzero .d .r5)
    (Q := Two fun L m₀ t => InvB L m₀ L.pp t)
    (fun n => Two (LoopAt n)) (fun n => (body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨h0, hn, b₁, z₁⟩, ⟨-, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show InvB e.L _ e.L.pp a from hl ▸ b₁,
          show InvB e.L _ e.L.pp b from hl ▸ b₂⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega_using [h0, hn]
        exact ⟨n - 1, by omega_using [h0], e, hL, hk, c₁, c₂, ⟨by omega_using [h0, hn, hl], by omega_using [hn], e₁ ▸ b₁⟩,
          ⟨by omega_using [h0, hn, hl], by omega_using [hn], e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, b₁, b₂⟩ => ⟨e.L.pp, e, hL, hk, c₁, c₂,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

/-- Two calls whose public data agree, in the frame. -/
def Entered (a b : State) : Prop :=
  ∃ s₁ s₂, scryptPPC.pre s₁ ∧ scryptPPC.pre s₂ ∧ scryptPPC.pub s₁ s₂ ∧
    a = allocated locals s₁ ∧ b = allocated locals s₂

theorem save_ct : RelCT isa Entered (.block setup) (Two fun L _ t => Entry L t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp, hlk⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show s₁.sp - _ = s₂.sp - _; rw [hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay s₂ = lay s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp]
  refine ⟨ht, ⟨lay s₁, s₁.gpr, s₂.gpr, s₁.lr, s₂.lr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, y₁.1, e ▸ y₂.1, y₁.2,
    e ▸ y₂.2⟩
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h6, ← a0] at hlk
  exact hlk

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
  (hd : sdepth pbk ≤ 1008) (name : String)
include hv hd

theorem rest_ct : RelCT isa (Two fun L _ t => Entry L t)
    (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop
      (.seq (pbkCall name pbk pbk2Args) (.block restore)))))
    fun _ _ => True := by
  have p1a : RelCT isa (Two fun L _ t => Entry L t) (.block pbk1Args)
      (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc he =>
      WP.mono (pbk1Args_ok hc he) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
      (fun L => pbkWr L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk1_regions hL))
      (fun _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk1_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk1_regions hL))
      (fun _ _ _ _ _ hL hc ha =>
        WP.mono (pbk1_call_ok hv hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k)
      (.block cur0) (Two fun L m₀ t => InvB L m₀ 0 t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hL hc hx => start_ok hL hc hx
  have p2a : RelCT isa (Two fun L m₀ t => InvB L m₀ L.pp t) (.block pbk2Args)
      (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (pbk2Args_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (Two fun _ _ _ => True) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => pbkWr L L.out L.ol)
      (fun _ _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk2_regions hL))
      (fun _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk2_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk2_regions hL))
      (fun _ _ _ _ _ hL hc ha =>
        WP.mono (pbk_call hv hd name hL hc ha (pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  have rs : RelCT isa (Two fun _ _ _ => True) (.block restore) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r30]) (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_two c₁ c₂)
      (by taint_decide)
  exact (p1a.seq p1c).seq (c0.seq (loop_ct.seq ((p2a.seq p2c).seq rs)))

theorem scrypt_ct : ConstantTime isa scryptPPC.pre scryptPPC.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.alloc (R := fun _ _ => True) (fun _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_)
  refine (save_ct.seq (rest_ct hv hd name)).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified PPC64LE.target (scrypt name pbk) (Spec.Scrypt.scryptContract PPC64LE.abi stackBytes) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := scrypt_ok hv hd name h
    exact ⟨t, s', he, hp⟩) (scrypt_ct hv hd name) scrypt_implies

end

/-! ## With PBKDF2 made with SHA-256 -/

/-- PBKDF2-HMAC-SHA256's implementation. -/
abbrev pbkCode : Prog isa := Proof.Pbkdf2.Whole.PPC64LE.Sha256.F.pbkdf2

/-- Its name. -/
abbrev pbkName : String := "vg_pbkdf2_hmac_sha256_scratch"

theorem pbk_verified :
    Verified PPC64LE.target pbkCode (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008) :=
  Proof.Pbkdf2.Whole.PPC64LE.Sha256.scratch

theorem pbk_sdepth : sdepth pbkCode ≤ 1008 := by
  have h := Proof.Pbkdf2.Whole.PPC64LE.sdepth_main Proof.Pbkdf2.Whole.PPC64LE.Sha256.okF
  have hX : Proof.Pbkdf2.Whole.PPC64LE.Sha256.okF.X + 144 = 1008 := by decide
  simp only [pbkCode, Impl.Pbkdf2.Whole.PPC64LE.Fns.pbkdf2, sdepth, Instr.frameBytes, Nat.max_le] at h ⊢
  omega_using [h, hX]

/-- `vg_scrypt` calling `vg_pbkdf2_hmac_sha256_scratch`. -/
theorem scrypt_verified :
    Verified PPC64LE.target (scrypt pbkName pbkCode) (Spec.Scrypt.scryptContract PPC64LE.abi stackBytes) :=
  scrypt_verified_of pbk_verified pbk_sdepth pbkName

end VG.Proof.Scrypt.PPC64LE.Whole
