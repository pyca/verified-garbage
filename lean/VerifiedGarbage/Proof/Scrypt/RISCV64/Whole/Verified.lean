module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
meta import VerifiedGarbage.Proof.Scrypt.Whole
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract
public import VerifiedGarbage.Proof.Scrypt.RISCV64.BlockMix
import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Scrypt.RISCV64.Scrypt
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.Scrypt
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.BlockMix
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-! ### `Scrypt.RISCV64.Whole.Correct`, which only this module used -/

section

/-! ### `Scrypt.RISCV64.Whole.Steps`, which only this module used -/

section

/-! ### `Scrypt.RISCV64.Whole.Layout`, which only this module used -/

section

/-! ### `Scrypt.RISCV64.Whole.Contract`, which only this module used -/

section

/-!
# scrypt on RISC-V: the contract

Untrusted: the contract the proof of `vg_scrypt` is written against
(`scryptRV`), as on PPC64LE (`Proof/Scrypt/PPC64LE/Whole/Verified.lean`),
with 1248 bytes of stack below the stack pointer (`stackBytes`: our 256-byte
frame and the 992 bytes PBKDF2 uses below it). It implies the shared contract
of `Spec/` (`scrypt_implies`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev stackBytes : Nat := 1248

/-- `vg_scrypt(password = a0, password_len = a1, salt = a2, salt_len = a3,
r = a4, b = a5, blen = a6, v = a7, vlen, scratch, slen, out, out_len)`, the
last five on the caller's stack. -/
def scryptRV : Contract isa where
  pre s :=
    let vlen := stackArg s 0
    let sc := stackArg s 1
    let slen := stackArg s 2
    let out := stackArg s 3
    let ol := stackArg s 4
    let r := (s.gpr .a4).toNat
    let pwR : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let saltR : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let bR : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat * 128⟩
    let vR : Region := ⟨s.gpr .a7, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    stackBytes ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .a6).toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r ((s.gpr .a6).toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .a4).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) ((stackArg s 0).toNat / r) r
      ((s.gpr .a6).toNat / r) (stackArg s 4).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 3) (stackArg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat) (s₁.gpr .a4).toNat
        ((s₁.gpr .a6).toNat / (s₁.gpr .a4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .a4).toNat ((stackArg s₁ 0).toNat / (s₁.gpr .a4).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat) (s₂.gpr .a4).toNat
        ((s₂.gpr .a6).toNat / (s₂.gpr .a4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .a4).toNat ((stackArg s₂ 0).toNat / (s₂.gpr .a4).toNat))

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
doublewords at `0x90000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x10000 | .a2 => 0x20000 | .a4 => 1 | .a5 => 0x30000 | .a6 => 1 | .a7 => 0x40000
    | _ => 0
  sp := 0x90000
  mem a := bif Nat.beq a.toNat 0x90000 then 2 else bif Nat.beq a.toNat 0x9000A then 5
    else bif Nat.beq a.toNat 0x90010 then 17 else bif Nat.beq a.toNat 0x9001A then 6
    else bif Nat.beq a.toNat 0x90020 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90000, 40⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies : scryptRV.Implies (Spec.Scrypt.scryptContract RISCV64.abi stackBytes) := by
  sig_implies [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, scryptRV, below, RISCV64.abi,
    RISCV64.argRegs, List.getD, List.range, List.range.loop]
    [satState, RISCV64.stackArg, RISCV64.stackArgAddr, Mem.readW, Mem.read]
    using satState

end VG.Proof.Scrypt.RISCV64.Whole

end

end

/-!
# scrypt on RISC-V: where everything is

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/Scrypt/PPC64LE/Whole/Verified.lean`): the function's buffers and the
1248 bytes of stack below the stack pointer, from `B` up (`Lay`): the 992
bytes PBKDF2 uses, then our frame (from `E = B + 992`: our return address,
our caller's `s3`, the password, its length, `r`, `b`, `blen`, `v` and the
next block, then from `B + 1072` the 168 bytes where scryptROMix and its
callees save registers). Our stack arguments are at `B + 1248`. `Ctx` is
what holds in the frame's body, and `call_ok` runs a call of verified code in
such a state.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64

/-- The arguments, and the bottom of the stack used. -/
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
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 1248, 40⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 1248⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 992, 256⟩
/-- Where scryptROMix and its callees save registers. -/
abbrev SV : Region := ⟨L.B + BitVec.ofNat 64 1072, 168⟩
/-- The frame's stack pointer. -/
abbrev E : Addr := L.B + BitVec.ofNat 64 992

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
  nB : L.B.toNat + 1288 ≤ 2 ^ 64
  aB : L.B.toNat % 16 = 0
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

/-- `SV` is within the frame. -/
theorem sv_within (L : Lay) : Within L.SV L.FR :=
  ⟨80, by
    show L.B + BitVec.ofNat 64 1072 = L.B + BitVec.ofNat 64 992 + BitVec.ofNat 64 80
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat], by show 80 + 168 ≤ 256; decide⟩

/-- The writable buffers, and where the calls save registers. -/
abbrev IsBuf (L : Lay) (R : Region) : Prop :=
  R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT ∨ R = L.SV

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

/-- A doubleword of the frame we keep is disjoint from a part of a writable
buffer. -/
theorem kept_buf {d : Nat} (h₁ : 992 ≤ d) (h₂ : d + 8 ≤ 1064) {R : Region} (hR : IsBuf L R) {r : Region}
    (hr : Region.Sub r R) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ r := by
  have hnB := h.nB
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.STK := Offset.sub_base _ (by omega)
  rcases hR with rfl | rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hr
  · exact (h.kv.sub_left hs).sub_right hr
  · exact (h.kc.sub_left hs).sub_right hr
  · exact (h.ko.sub_left hs).sub_right hr
  · exact (Offset.disjoint _ (by omega_using [h₂]) (by omega_using [h₂]) (by omega_using [])).sub_right hr

/-- A range in our stack arguments is disjoint from a part of a writable buffer. -/
theorem args_buf {d n : Nat} (h₁ : 1248 ≤ d) (h₂ : d + n ≤ 1288) {R : Region} (hR : IsBuf L R)
    {r : Region} (hr : Region.Sub r R) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hnB := h.nB
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega_using [h₂])
  rcases hR with rfl | rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hr
  · exact (h.va.symm.sub_left hs).sub_right hr
  · exact (h.ca.symm.sub_left hs).sub_right hr
  · exact (h.oa.symm.sub_left hs).sub_right hr
  · exact (Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])).sub_right hr

end Lay.Ok

/-! ## What the calls cannot change -/

/-- The doublewords of the frame and our stack arguments that stay as they
are in the frame's body: our return address `ra` and our caller's `s3`. -/
structure Kept (L : Lay) (ra s3 : BitVec 64) (m : Mem) : Prop where
  ra : m.readW (L.B + BitVec.ofNat 64 992) 64 = ra
  s3 : m.readW (L.B + BitVec.ofNat 64 1000) 64 = s3
  pw : m.readW (L.B + BitVec.ofNat 64 1008) 64 = L.pw
  pwl : m.readW (L.B + BitVec.ofNat 64 1016) 64 = L.pwl
  r : m.readW (L.B + BitVec.ofNat 64 1024) 64 = L.r
  b : m.readW (L.B + BitVec.ofNat 64 1032) 64 = L.b
  blen : m.readW (L.B + BitVec.ofNat 64 1040) 64 = L.blen
  v : m.readW (L.B + BitVec.ofNat 64 1048) 64 = L.v
  vlen : m.readW (L.B + BitVec.ofNat 64 1248) 64 = L.vlen
  scr : m.readW (L.B + BitVec.ofNat 64 1256) 64 = L.scr
  out : m.readW (L.B + BitVec.ofNat 64 1272) 64 = L.out
  ol : m.readW (L.B + BitVec.ofNat 64 1280) 64 = L.ol

/-- Where the kept doublewords are. -/
abbrev KeptAt (d : Nat) : Prop := (992 ≤ d ∧ d + 8 ≤ 1056) ∨ (1248 ≤ d ∧ d + 8 ≤ 1288)

/-- The kept doublewords survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {ra s3 : BitVec 64} {m m' : Mem} {rs : List Region} (hk : Kept L ra s3 m)
    (hf : Frame rs m m')
    (hd : ∀ d, KeptAt d → ∀ R ∈ rs, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R) :
    Kept L ra s3 m' := by
  have k : ∀ d, KeptAt d →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 992 (by decide)).trans hk.ra, (k 1000 (by decide)).trans hk.s3,
    (k 1008 (by decide)).trans hk.pw, (k 1016 (by decide)).trans hk.pwl, (k 1024 (by decide)).trans hk.r,
    (k 1032 (by decide)).trans hk.b, (k 1040 (by decide)).trans hk.blen,
    (k 1048 (by decide)).trans hk.v, (k 1248 (by decide)).trans hk.vlen,
    (k 1256 (by decide)).trans hk.scr, (k 1272 (by decide)).trans hk.out,
    (k 1280 (by decide)).trans hk.ol⟩

/-! ## In the frame's body -/

/-- The state in the frame's body: `g` are the registers on entry, `m₀` the
memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.E
  s3 : t.gpr .s3 = L.E
  cs : ∀ r ∈ preserved, r ≠ .s3 → t.gpr r = g r
  kept : Kept L (g .ra) (g .s3) t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.ARGS, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-- A writable region is within one of the writable buffers, or where the
calls save registers. -/
def InBuf (L : Lay) (r : Region) : Prop :=
  Within r L.BB ∨ Within r L.VV ∨ Within r L.SC ∨ Within r L.OUT ∨ Within r L.SV

theorem InBuf.sub {L : Lay} {r : Region} (h : InBuf L r) : ∃ R, IsBuf L R ∧ Region.Sub r R := by
  rcases h with h | h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr (.inl rfl))), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr (.inr rfl))), h.sub⟩

theorem Within.trans {r R S : Region} (h : Within r R) (h' : Within R S) : Within r S := by
  obtain ⟨o, hb, hl⟩ := h
  obtain ⟨o', hb', hl'⟩ := h'
  refine ⟨o' + o, ?_, by omega_using [hl, hl']⟩
  rw [hb, hb', BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem covers {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h.trans (sv_within L)⟩

/-- The stack a call from `sp = B + 992` uses, if it uses at most 992 bytes. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 992) :
    Region.Sub (below (B + BitVec.ofNat 64 992) m) ⟨B, 992⟩ := by
  have : B + BitVec.ofNat 64 992 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (992 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 992) (a := m) (b := 992) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 992 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega_using [hm])

/-- A call of verified code (see `WP.callAny`), which uses at most 992 bytes
of stack and is given regions within ours to read, and within the writable
buffers to write: afterwards `Ctx` holds again, memory changed only within
what it writes and the 992 bytes below `sp`, and the callee's postcondition
holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : sdepth c ≤ 992) {t : State} (hc : Ctx L g m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g m₀ s' → Frame (wr ++ [⟨L.B, 992⟩]) t.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = t.gpr r) →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.callAny hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs hpost => ?_) (by omega_using [hd])
  have hf' : Frame (wr ++ [⟨L.B, 992⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.sp]
      exact below_call_sub _ hd
  have hnB := hL.nB
  -- The regions the call may change miss the kept doublewords.
  have hdisj : ∀ d, KeptAt d → ∀ R ∈ wr ++ [⟨L.B, 992⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R := by
    intro d hdd R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨R', hR', hs⟩ := (hwsub R hR).sub
      rcases hdd with hdd | hdd
      · exact hL.kept_buf (by omega_using [hdd]) (by omega_using [hdd]) hR' hs
      · exact hL.args_buf (by omega_using [hdd]) (by omega_using [hdd]) hR' hs
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hcs _ (by decide)).trans hc.s3,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'), hc.kept.frame hf' hdisj,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hcs hpost
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨R', hR', hs⟩ := (hwsub r hr).sub
    rcases hR' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨L.STK, by simp, fun x hx => (Offset.sub_base L.B (d := 1072) (n := 168) (k := 1248)
        (by omega_using [])) x (hs x hx)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Region.sub_prefix (by decide)⟩

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .a0, s.gpr .a1, s.gpr .a2, s.gpr .a3, s.gpr .a4, s.gpr .a5, s.gpr .a6, s.gpr .a7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    s.sp - BitVec.ofNat 64 1248⟩

theorem lay_top (s : State) : (lay s).B + BitVec.ofNat 64 1248 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (lay s).B + BitVec.ofNat 64 1248 = stackArgAddr s 0 := by
  rw [lay_top]; exact (BitVec.add_zero _).symm

theorem lay_ok {s : State} (h : scryptRV.pre s) : (lay s).Ok := by
  obtain ⟨hst, h40, hal, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea : (lay s).ARGS = ⟨stackArgAddr s 0, 40⟩ := by simp only [Lay.ARGS, lay_args]
  have tB : (lay s).B.toNat = s.sp.toNat - 1248 := by
    simp only [lay]
    simp only [stackBytes] at hst
    rw [Offset.toNat_sub_ofNat s.sp 1248]
    omega_using [hst]
  have nB : (lay s).B.toNat + 1288 ≤ 2 ^ 64 := by
    simp only [stackBytes] at hst; rw [tB]; omega_using [h40]
  have aB : (lay s).B.toNat % 16 = 0 := by
    simp only [stackBytes] at hst; rw [tB]; omega_using [hal]
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, nB, aB, rpos, bmod, vmod, hval, olb, slen⟩

end VG.Proof.Scrypt.RISCV64.Whole

end

end

/-!
# scrypt on RISC-V: the blocks between the calls

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/Scrypt/PPC64LE/Whole/Steps.lean`): the facts about the parameters the
proof uses; reading and writing the frame in `Ctx` (`fld_wp`, `fsd_wp`,
through `s3`); and each block between the calls (`setup` from the frame's
`alloc`, the moves of the calls' arguments, the next block, `restore`),
keeping `Ctx` and giving the calls' arguments (`PbkArgs`, `RomixArgs`) or
the next block.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64.Whole
open VG.Impl.Scrypt.RISCV64 (mov)

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
  toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 1248; omega_using [])

/-- `128 r p`, the length of `b`. -/
theorem len_b : 128 * L.r.toNat * L.pp = L.blen.toNat * 128 := by
  rw [h.blen_eq, Nat.mul_comm 128, Nat.mul_assoc, Nat.mul_comm 128, Nat.mul_assoc]

/-- The derived key of step 1 is not too long for PBKDF2. -/
theorem ol1 : L.blen.toNat * 128 ≤ (2 ^ 32 - 1) * 32 := by
  have h₁ := h.valid.2.2.2.2.1
  obtain h₂ := Nat.div_mul_le_self ((2 ^ 32 - 1) * 32) (128 * L.r.toNat)
  obtain h₃ : L.pp * (128 * L.r.toNat) ≤ (2 ^ 32 - 1) * 32 / (128 * L.r.toNat) * (128 * L.r.toNat) :=
    Nat.mul_le_mul_right _ h₁
  rw [← h.len_b, Nat.mul_comm (128 * L.r.toNat)]
  omega_using [h₂, h₃]

end Lay.Ok

/-! ## In the frame -/

/-- The address of a doubleword of the frame (`s3 = B + 992`). -/
theorem fr_addr (B : Addr) (d : Nat) :
    B + BitVec.ofNat 64 992 + BitVec.ofNat 64 d = B + BitVec.ofNat 64 (992 + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- Reading a doubleword past a write of another. -/
theorem readW_writeW_off (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 64) (h : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x + 8 ≤ 2 ^ 64) (hy : y + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hx hy) (by decide)

/-- The frame's cur slot. -/
abbrev curR (L : Lay) : Region := ⟨L.B + BitVec.ofNat 64 1056, 8⟩

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g m₀ t)
include hc

theorem s3' : t.gpr .s3 = L.B + BitVec.ofNat 64 992 := hc.s3

/-- Code that writes only registers other than the callee-saved ones. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.s3,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hm]; exact hc.kept, by rw [hm]; exact hc.frame⟩

/-- A write of a register other than the callee-saved ones. -/
theorem upd {d : Reg} {v : BitVec 64} (u : Upd t t' d v) (hd : d ∉ preserved) : Ctx L g m₀ t' :=
  hc.regs u.rd u.wr u.sp u.mem fun r hr => u.other r fun e => hd (e ▸ hr)

/-- Code that also writes the frame's cur slot. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hf : Frame [curR L] t.mem t'.mem) : Ctx L g m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.s3,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun d hd R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega_using [])
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega_using [])⟩

end Ctx

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-- A doubleword of the frame or of our stack arguments is aligned. -/
theorem fr_al (hL : L.Ok) {d : Nat} (hd : d % 8 = 0) :
    (L.B + BitVec.ofNat 64 (992 + d)).toNat % 8 = 0 :=
  Spill.al8 (by have := hL.aB; omega_using [this]) (by omega_using [hd])

/-- `ld r, d(s3)`, of the frame or of our stack arguments. -/
theorem fld_wp (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {r : Reg} {d : Nat} (o : Nat)
    (hd : d + 8 ≤ 296) (h8 : d % 8 = 0) (ho : 992 + d = o) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd t s' r (t.mem.readW (L.B + BitVec.ofNat 64 o) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (fld r d :: is)) t Q := by
  subst ho
  have hnB := hL.nB
  refine wp_ld (by omega_using [hd]) (by rw [hc.s3', fr_addr]) (fr_al hL h8) ?_ k
  rw [hc.rd, hc.wr]
  by_cases h256 : d + 8 ≤ 256
  · exact ⟨L.FR, by simp, Offset.contains _ (by omega_using []) (by omega_using [h256]) (by omega_using [])⟩
  · exact ⟨L.ARGS, by simp, Offset.contains _ (by omega_using [h8, h256]) (by omega_using [hd]) (by omega_using [])⟩

/-- `sd r, d(s3)`, of the frame. -/
theorem fsd_wp (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {r : Reg} {d : Nat} (o : Nat)
    (hd : d + 8 ≤ 256) (h8 : d % 8 = 0) (ho : 992 + d = o) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd t s' (t.mem.writeW (L.B + BitVec.ofNat 64 o) (t.gpr r)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .d r .s3 d :: is)) t Q := by
  subst ho
  have hnB := hL.nB
  refine wp_sd (by omega_using [hd]) (by rw [hc.s3', fr_addr]) (fr_al hL h8) ?_ k
  rw [hc.wr]
  exact ⟨L.FR, by simp, Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])⟩

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password and `c = 1`. -/
structure PbkArgs (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  a0 : t.gpr .a0 = L.pw
  a1 : t.gpr .a1 = L.pwl
  a2 : t.gpr .a2 = salt
  a3 : t.gpr .a3 = sl
  a4 : t.gpr .a4 = 1
  a5 : t.gpr .a5 = out
  a6 : t.gpr .a6 = ol

/-- The registers on entry to the frame's body, once our arguments are saved. -/
structure Entry (L : Lay) (t : State) : Prop where
  a0 : t.gpr .a0 = L.pw
  a1 : t.gpr .a1 = L.pwl
  a2 : t.gpr .a2 = L.salt
  a3 : t.gpr .a3 = L.sl
  a5 : t.gpr .a5 = L.b
  a6 : t.gpr .a6 = L.blen

theorem pbk1Args_ok {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' := by
  unfold pbk1Args
  refine wp_li (imm := 1) (by decide) fun a ua => wp_sll (by decide) fun b ub => WP.block_nil ?_
  refine ⟨(hc.upd ua (by decide)).upd ub (by decide), by rw [ub.mem, ua.mem], ?_⟩
  exact ⟨by rw [ub.other _ (by decide), ua.other _ (by decide), he.a0],
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a1],
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a2],
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a3],
    by rw [ub.other _ (by decide), ua.gpr]; rfl,
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a5],
    by rw [ub.gpr, ua.other _ (by decide), he.a6, lsl7]⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block cur0) t fun t' => Ctx L g m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = L.b ∧ Frame [curR L] t.mem t'.mem := by
  have hnB := hL.nB
  unfold cur0
  refine fld_wp hL hc (d := bOff) 1032 (by decide) (by decide) (by decide) fun a ua => ?_
  obtain ha := hc.upd ua (by decide)
  refine fsd_wp hL ha (d := curOff) 1056 (by decide) (by decide) (by decide) fun b ub => WP.block_nil ?_
  obtain e : a.gpr .a0 = L.b := by rw [ua.gpr]; exact hc.kept.b
  obtain f : Frame [curR L] t.mem b.mem := by
    rw [ub.mem, ua.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.store hL (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) (by rw [ub.sp, ua.sp])
    (fun r hr => by rw [ub.gpr, ua.other _ fun e => by subst e; revert hr; decide]) f, ?_, f⟩
  rw [ub.mem, e]
  exact Mem.readW_writeW_self64 _ _ _

/-- The low three bits of the pointers ROMix accesses by doublewords. -/
abbrev alBits (L : Lay) : BitVec 64 := (L.b ||| L.v ||| L.scr) &&& BitVec.ofInt 64 7

theorem alignBits_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block alignBits) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .t0 = alBits L := by
  unfold alignBits
  refine fld_wp hL hc (d := bOff) 1032 (by decide) (by decide) (by decide) fun a ua => ?_
  obtain ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := vOff) 1048 (by decide) (by decide) (by decide) fun b ub => ?_
  obtain hb := ha.upd ub (by decide)
  refine wp_or fun c uc => ?_
  obtain hc' := hb.upd uc (by decide)
  refine fld_wp hL hc' (d := argOff scratchArg) 1256 (by decide) (by decide) (by decide) fun d ud => ?_
  obtain hd := hc'.upd ud (by decide)
  refine wp_or fun e ue => ?_
  obtain he := hd.upd ue (by decide)
  refine wp_andi (by decide) fun f uf => WP.block_nil ?_
  refine ⟨he.upd uf (by decide), by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem], ?_⟩
  obtain e0 : a.gpr .t0 = L.b := by rw [ua.gpr]; exact hc.kept.b
  obtain e1 : b.gpr .t1 = L.v := by rw [ub.gpr, ua.mem]; exact hc.kept.v
  obtain e2 : b.gpr .t0 = L.b := by rw [ub.other _ (by decide), e0]
  obtain e3 : c.gpr .t0 = L.b ||| L.v := by rw [uc.gpr, e2, e1]
  obtain e4 : d.gpr .t1 = L.scr := by rw [ud.gpr, uc.mem, ub.mem, ua.mem]; exact hc.kept.scr
  obtain e5 : d.gpr .t0 = L.b ||| L.v := by rw [ud.other _ (by decide), e3]
  obtain e6 : e.gpr .t0 = L.b ||| L.v ||| L.scr := by rw [ue.gpr, e5, e4]
  rw [uf.gpr, e6]

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : Addr) (t : State) : Prop where
  a0 : t.gpr .a0 = cur
  a1 : t.gpr .a1 = L.r
  a2 : t.gpr .a2 = L.v
  a3 : t.gpr .a3 = L.vlen
  a4 : t.gpr .a4 = L.scr
  a5 : t.gpr .a5 = L.B + BitVec.ofNat 64 1072

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ RomixArgs L cur t' := by
  unfold romixArgs
  refine fld_wp hL hc (d := curOff) 1056 (by decide) (by decide) (by decide) fun a ua => ?_
  obtain ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := rOff) 1024 (by decide) (by decide) (by decide) fun b ub => ?_
  obtain hb := ha.upd ub (by decide)
  refine fld_wp hL hb (d := vOff) 1048 (by decide) (by decide) (by decide) fun c uc => ?_
  obtain hc' := hb.upd uc (by decide)
  refine fld_wp hL hc' (d := argOff vlenArg) 1248 (by decide) (by decide) (by decide) fun d ud => ?_
  obtain hd := hc'.upd ud (by decide)
  refine fld_wp hL hd (d := argOff scratchArg) 1256 (by decide) (by decide) (by decide) fun e ue => ?_
  obtain he := hd.upd ue (by decide)
  refine wp_addi (by decide) fun f uf => WP.block_nil ?_
  obtain me : e.mem = t.mem := by rw [ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨he.upd uf (by decide), by rw [uf.mem, me], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.gpr, hcur]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.gpr, ua.mem]; exact hc.kept.r
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr, ub.mem, ua.mem]
    exact hc.kept.v
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem, ub.mem, ua.mem]
    exact hc.kept.vlen
  · rw [uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem]
    exact hc.kept.scr
  · rw [uf.gpr, he.s3', fr_addr]; rfl

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧ Frame [curR L] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.gpr .t0 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) -
        (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
  have hnB := hL.nB
  unfold nextBlock
  refine fld_wp hL hc (d := curOff) 1056 (by decide) (by decide) (by decide) fun a ua => ?_
  obtain ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := rOff) 1024 (by decide) (by decide) (by decide) fun b ub => ?_
  obtain hb := ha.upd ub (by decide)
  refine wp_sll (by decide) fun c uc => ?_
  obtain hc' := hb.upd uc (by decide)
  refine wp_add fun d ud => ?_
  obtain hd := hc'.upd ud (by decide)
  obtain e0 : d.gpr .a0 = cur + BitVec.ofNat 64 (L.r.toNat * 128) := by
    rw [ud.gpr, uc.other _ (by decide), ub.other _ (by decide), ua.gpr, hcur, uc.gpr, ub.gpr, ua.mem,
      hc.kept.r, lsl7]
  obtain md : d.mem = t.mem := by rw [ud.mem, uc.mem, ub.mem, ua.mem]
  refine fsd_wp hL hd (d := curOff) 1056 (by decide) (by decide) (by decide) fun e ue => ?_
  obtain f : Frame [curR L] t.mem e.mem := by
    rw [ue.mem, md]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain he : Ctx L g m₀ e := hd.store hL ue.rd ue.wr ue.sp (fun r _ => by rw [ue.gpr]) (by rw [md]; exact f)
  refine fld_wp hL he (d := bOff) 1032 (by decide) (by decide) (by decide) fun h uh => ?_
  obtain hh := he.upd uh (by decide)
  refine fld_wp hL hh (d := blenOff) 1040 (by decide) (by decide) (by decide) fun i ui => ?_
  obtain hi := hh.upd ui (by decide)
  refine wp_sll (by decide) fun j uj => ?_
  obtain hj := hi.upd uj (by decide)
  refine wp_add fun k uk => ?_
  obtain hk := hj.upd uk (by decide)
  refine wp_sub fun l ul => WP.block_nil ?_
  obtain me : e.mem = t.mem.writeW (L.B + BitVec.ofNat 64 1056) (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
    rw [ue.mem, md, e0]
  obtain ml : l.mem = e.mem := by rw [ul.mem, uk.mem, uj.mem, ui.mem, uh.mem]
  obtain eb : e.mem.readW (L.B + BitVec.ofNat 64 1032) 64 = L.b := by
    rw [me, readW_writeW_off (x := 1032) (y := 1056) _ _ _ (by decide) (by decide) (by decide)]
    exact hc.kept.b
  obtain ebl : e.mem.readW (L.B + BitVec.ofNat 64 1040) 64 = L.blen := by
    rw [me, readW_writeW_off (x := 1040) (y := 1056) _ _ _ (by decide) (by decide) (by decide)]
    exact hc.kept.blen
  refine ⟨hk.upd ul (by decide), by rw [ml]; exact f, by rw [ml, me]; exact Mem.readW_writeW_self64 _ _ _, ?_⟩
  obtain k0 : k.gpr .a0 = cur + BitVec.ofNat 64 (L.r.toNat * 128) := by
    rw [uk.other _ (by decide), uj.other _ (by decide), ui.other _ (by decide), uh.other _ (by decide),
      ue.gpr, e0]
  obtain i0 : i.gpr .t0 = L.b := by
    rw [ui.other _ (by decide), uh.gpr]; exact eb
  obtain j1 : j.gpr .t1 = BitVec.ofNat 64 (L.blen.toNat * 128) := by
    rw [uj.gpr, ui.gpr, uh.mem, ← lsl7]; exact congrArg (fun x : BitVec 64 => x <<< (7 : Nat)) ebl
  obtain k1 : k.gpr .t0 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) := by
    rw [uk.gpr, uj.other _ (by decide), i0, j1]
  rw [ul.gpr, k1, k0]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' := by
  unfold pbk2Args
  refine fld_wp hL hc (d := pwOff) 1008 (by decide) (by decide) (by decide) fun a ua => ?_
  obtain ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := pwlOff) 1016 (by decide) (by decide) (by decide) fun b ub => ?_
  obtain hb := ha.upd ub (by decide)
  refine fld_wp hL hb (d := bOff) 1032 (by decide) (by decide) (by decide) fun c uc => ?_
  obtain hc' := hb.upd uc (by decide)
  refine fld_wp hL hc' (d := blenOff) 1040 (by decide) (by decide) (by decide) fun d ud => ?_
  obtain hd := hc'.upd ud (by decide)
  refine wp_sll (by decide) fun e ue => ?_
  obtain he := hd.upd ue (by decide)
  refine wp_li (imm := 1) (by decide) fun f uf => ?_
  obtain hf := he.upd uf (by decide)
  refine fld_wp hL hf (d := argOff outArg) 1272 (by decide) (by decide) (by decide) fun h uh => ?_
  obtain hh := hf.upd uh (by decide)
  refine fld_wp hL hh (d := argOff outLenArg) 1280 (by decide) (by decide) (by decide) fun i ui => WP.block_nil ?_
  obtain mh : h.mem = t.mem := by rw [uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hh.upd ui (by decide), by rw [ui.mem, mh], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr]
    exact hc.kept.pw
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.mem]
    exact hc.kept.pwl
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.mem, ua.mem]
    exact hc.kept.b
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.gpr, uc.mem,
      ub.mem, ua.mem, hc.kept.blen, lsl7]
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.gpr]; rfl
  · rw [ui.other _ (by decide), uh.gpr, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
    exact hc.kept.out
  · rw [ui.gpr, uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
    exact hc.kept.ol

/-- The return address and our caller's `s3` back. -/
theorem restore_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block restore) t fun t' => t'.gpr .ra = g .ra ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ ∀ r ∈ preserved, t'.gpr r = g r := by
  unfold restore
  refine fld_wp hL hc (d := raOff) 992 (by decide) (by decide) (by decide) fun a ua => ?_
  obtain ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := s3Off) 1000 (by decide) (by decide) (by decide) fun b ub => WP.block_nil ?_
  refine ⟨by rw [ub.other _ (by decide), ua.gpr]; exact hc.kept.ra, by rw [ub.mem, ua.mem],
    by rw [ub.sp, ua.sp], by rw [ub.rd, ua.rd], by rw [ub.wr, ua.wr], fun r hr => ?_⟩
  by_cases e : r = .s3
  · subst e; rw [ub.gpr, ua.mem]; exact hc.kept.s3
  · rw [ub.other _ e, ua.other _ fun e' => by subst e'; revert hr; decide]
    exact hc.cs r hr e

end

/-! ## Entry -/

/-- `sd r, d(t0)` into the frame, before `s3` is set. -/
theorem esd {L : Lay} (hL : L.Ok) {t : State} {rest : List Region} (h0 : t.gpr .t0 = L.B + BitVec.ofNat 64 992)
    (hw : t.wr = L.FR :: rest) {r : Reg} {d : Nat} (o : Nat) (hd : d + 8 ≤ 256) (h8 : d % 8 = 0)
    (ho : 992 + d = o) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd t s' (t.mem.writeW (L.B + BitVec.ofNat 64 o) (t.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d r .t0 d :: is)) t Q := by
  subst ho
  have hnB := hL.nB
  refine wp_sd (by omega_using [hd]) (by rw [h0, fr_addr]) (fr_al hL h8) ?_ k
  rw [hw]
  exact ⟨L.FR, by simp, Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])⟩

theorem arg_addr (s : State) (i : Nat) :
    (lay s).B + BitVec.ofNat 64 (1248 + 8 * i) = stackArgAddr s i := by
  show _ = s.sp + _
  rw [← lay_top s, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem entry_ok {s : State} (h : scryptRV.pre s) :
    WP isa (.block setup) (allocd 256 s) fun t => Ctx (lay s) s.gpr s.mem t ∧ Entry (lay s) t := by
  obtain hL := lay_ok h
  have hnB := hL.nB
  obtain hsp : (allocd 256 s).sp = (lay s).B + BitVec.ofNat 64 992 :=
    Offset.sub_ofNat_eq s.sp (by decide : 256 ≤ 1248)
  obtain hw : (allocd 256 s).wr = (lay s).FR :: s.wr := by
    rw [show (allocd 256 s).wr = ⟨(allocd 256 s).sp, 256⟩ :: s.wr from rfl, hsp]
  unfold setup
  refine wp_addSp (by decide) fun a ua => ?_
  obtain a0 : a.gpr .t0 = (lay s).B + BitVec.ofNat 64 992 := by
    rw [ua.gpr, hsp]; exact BitVec.add_zero _
  obtain aw : a.wr = (lay s).FR :: s.wr := ua.wr.trans hw
  obtain ga : ∀ r, r ≠ .t0 → a.gpr r = s.gpr r := fun r hr => ua.other r hr
  refine esd hL a0 aw (d := raOff) 992 (by decide) (by decide) (by decide) fun b ub => ?_
  refine esd hL (by rw [ub.gpr]; exact a0) (ub.wr.trans aw) (d := s3Off) 1000 (by decide) (by decide)
    (by decide) fun c uc => ?_
  obtain cg : c.gpr = a.gpr := uc.gpr.trans ub.gpr
  obtain cw : c.wr = (lay s).FR :: s.wr := uc.wr.trans (ub.wr.trans aw)
  refine esd hL (by rw [cg]; exact a0) cw (d := pwOff) 1008 (by decide) (by decide) (by decide) fun d ud => ?_
  refine esd hL (by rw [ud.gpr, cg]; exact a0) (ud.wr.trans cw) (d := pwlOff) 1016 (by decide) (by decide)
    (by decide) fun e ue => ?_
  obtain eg : e.gpr = a.gpr := ue.gpr.trans (ud.gpr.trans cg)
  obtain ew : e.wr = (lay s).FR :: s.wr := ue.wr.trans (ud.wr.trans cw)
  refine esd hL (by rw [eg]; exact a0) ew (d := rOff) 1024 (by decide) (by decide) (by decide) fun f uf => ?_
  refine esd hL (by rw [uf.gpr, eg]; exact a0) (uf.wr.trans ew) (d := bOff) 1032 (by decide) (by decide)
    (by decide) fun i ui => ?_
  obtain ig : i.gpr = a.gpr := ui.gpr.trans (uf.gpr.trans eg)
  obtain iw : i.wr = (lay s).FR :: s.wr := ui.wr.trans (uf.wr.trans ew)
  refine esd hL (by rw [ig]; exact a0) iw (d := blenOff) 1040 (by decide) (by decide) (by decide) fun j uj => ?_
  refine esd hL (by rw [uj.gpr, ig]; exact a0) (uj.wr.trans iw) (d := vOff) 1048 (by decide) (by decide)
    (by decide) fun k uk => ?_
  obtain kg : k.gpr = a.gpr := uk.gpr.trans (uj.gpr.trans ig)
  refine wp_mv fun l ul => WP.block_nil ?_
  obtain hl : ∀ r, r ≠ .s3 → r ≠ .t0 → l.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ul.other r h1, kg, ga r h2]
  obtain hm : l.mem = ((((((((s.mem.writeW ((lay s).B + BitVec.ofNat 64 992) (s.gpr .ra)).writeW
      ((lay s).B + BitVec.ofNat 64 1000) (s.gpr .s3)).writeW ((lay s).B + BitVec.ofNat 64 1008) (s.gpr .a0)).writeW
      ((lay s).B + BitVec.ofNat 64 1016) (s.gpr .a1)).writeW ((lay s).B + BitVec.ofNat 64 1024) (s.gpr .a4)).writeW
      ((lay s).B + BitVec.ofNat 64 1032) (s.gpr .a5)).writeW ((lay s).B + BitVec.ofNat 64 1040) (s.gpr .a6)).writeW
      ((lay s).B + BitVec.ofNat 64 1048) (s.gpr .a7)) := by
    rw [ul.mem, uk.mem, uj.mem, ui.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, uj.gpr, ig, uf.gpr, eg,
      ud.gpr, cg, ub.gpr, ga _ (by decide), ga _ (by decide), ga _ (by decide), ga _ (by decide),
      ga _ (by decide), ga _ (by decide), ga _ (by decide), ga _ (by decide)]
    rfl
  obtain k0 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1248) 64 = (lay s).vlen := by
    rw [arg_addr s 0]; rfl
  obtain k1 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1256) 64 = (lay s).scr := by
    rw [arg_addr s 1]; rfl
  obtain k3 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1272) 64 = (lay s).out := by
    rw [arg_addr s 3]; rfl
  obtain k4 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1280) 64 = (lay s).ol := by
    rw [arg_addr s 4]; rfl
  obtain lsp : l.sp = (lay s).B + BitVec.ofNat 64 992 := by
    rw [ul.sp, uk.sp, uj.sp, ui.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  obtain lwr : l.wr = (lay s).FR :: s.wr := by rw [ul.wr, uk.wr, uj.wr, iw]
  obtain lrd : l.rd = s.rd := by
    rw [ul.rd, uk.rd, uj.rd, ui.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd]; rfl
  refine ⟨⟨?_, ?_, lsp, ?_, fun r hr hr' => hl r hr' fun e => by subst e; revert hr; decide, ?_, ?_⟩,
    hl _ (by decide) (by decide), hl _ (by decide) (by decide), hl _ (by decide) (by decide),
    hl _ (by decide) (by decide), hl _ (by decide) (by decide), hl _ (by decide) (by decide)⟩
  · rw [lrd, h.2.2.2.1, ← arg_addr s 0]; rfl
  · rw [lwr, h.2.2.2.2.1]; rfl
  · rw [ul.gpr, kg, a0]
  · rw [hm]
    constructor <;>
      simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64, k0, k1, k3, k4] <;> rfl
  · rw [hm]
    refine Frame.sub (rs := [(lay s).STK]) ?_ fun r hr => ?_
    · repeat refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega_using []))
      exact Frame.refl _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.Scrypt.RISCV64.Whole

end

end

/-!
# scrypt on RISC-V: correctness

As on PPC64LE (`Proof/Scrypt/PPC64LE/Whole/Verified.lean`). PBKDF2-HMAC-SHA256
(any implementation correct under `pbkR sha256S 992`, using at most 992 bytes
of stack) is called by `pbk_call`; ROMix, by doublewords or by bytes, by
`romix_call`. Step 1 leaves the blocks `X k` of
`PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`), with
the doubleword ROMix if `b`, `v` and `scratch` are all 8-byte aligned
(`all_ok`); step 3 derives the key from them (`step3_ok`). `scrypt_ok` puts
the frame around it.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.Impl.Scrypt.RISCV64.Whole
open VG.Proof.Pbkdf2.Whole.RISCV64 (pbkR)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

/-- What `vg_scrypt` needs of the PBKDF2 it calls. -/
abbrev pbkK : Contract isa := pbkR Spec.Hmac.sha256S 992

/-- Correctness of the PBKDF2 called. -/
abbrev PbkOk (pbk : Prog isa) : Prop :=
  ∀ s, pbkK.pre s → ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s'

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.ce_sp {t : State} (hc : Ctx L g m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).sp = L.B + BitVec.ofNat 64 992 := by
  rw [State.withRegions_sp, State.callEntry_sp, hc.sp]

theorem sub992 (B : Addr) : B + BitVec.ofNat 64 992 - BitVec.ofNat 64 992 = B := BitVec.add_sub_cancel _ _

theorem sv_stk (L : Lay) : Region.Sub L.SV L.STK := Offset.sub_base _ (by decide)

namespace Lay.Ok

variable (hL : L.Ok)
include hL


/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs,
    (hL.kp.symm.sub_right (sv_stk L)).sub_right hs]

/-- The 992 bytes the calls use miss every writable buffer. -/
theorem low_in {r : Region} (h : InBuf L r) : Region.Disjoint ⟨L.B, 992⟩ r := by
  have hnB := hL.nB
  have lo : Region.Sub ⟨L.B, 992⟩ L.STK := fun x hx => by
    simp only [Region.Contains] at hx ⊢; omega_using [hx]
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl | rfl
  · exact (hL.kb.sub_left lo).sub_right hs
  · exact (hL.kv.sub_left lo).sub_right hs
  · exact (hL.kc.sub_left lo).sub_right hs
  · exact (hL.ko.sub_left lo).sub_right hs
  · exact (Region.Disjoint.symm (Offset.disjoint_base _ (by decide) (by omega_using []))).sub_right hs

end Lay.Ok

/-! ### PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt : Addr) (sl : BitVec 64) : List Region := [L.PW, ⟨salt, sl.toNat⟩]
abbrev pbkWr (out : Addr) (ol : BitVec 64) : List Region := [⟨out, ol.toNat⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨salt, sl.toNat⟩ R
  ow : InBuf L ⟨out, ol.toNat⟩
  so : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨out, ol.toNat⟩
  ks : L.STK.Disjoint ⟨salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 64
  no : out.toNat + ol.toNat ≤ 2 ^ 64
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr out ol)) := by
  have hnB := hL.nB
  have haB := hL.aB
  have t992 : (L.B + BitVec.ofNat 64 992).toNat = L.B.toNat + 992 := toNat_add_ofNat _ (by omega_using [hnB])
  have lo : Region.Sub ⟨L.B, 992⟩ L.STK := fun x hx => by
    simp only [Region.Contains] at hx ⊢; omega_using [hx]
  simp only [pbkK, pbkR, below, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr,
    hc.ce_sp, sub992, t992, gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a6 ∉ linkRegs),
    ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6]
  exact ⟨trivial, trivial, hL.pw_buf hr.ow, hr.so, by omega_using [haB], by omega_using [], hL.kp.sub_left lo, hr.ks.sub_left lo,
    hL.low_in hr.ow, hL.np, hr.ns, hr.no, by decide, hr.ol⟩

theorem pbk_sub {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr out ol, ∃ R ∈ L.regions, Within r R := by
  have hs := hr.sw
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (Nat.le_refl _)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · rcases hr.ow with h | h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h.trans (sv_within L)⟩

theorem pbk_wsub {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) : ∀ r ∈ pbkWr out ol, InBuf L r := by
  simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact hr.ow

theorem pbk_call (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.B, 992⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  refine call_ok hL hv hd hc (pbk_pre' hL hc ha hr) (pbk_sub hr) (pbk_wsub hr)
    fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [pbkK, pbkR, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a6 ∉ linkRegs), ha.a0, ha.a1, ha.a2, ha.a3,
    ha.a4, ha.a5, ha.a6] at h
  exact h

end

/-! ### ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, L.r.toNat * 128⟩, L.SV]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkAt L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

theorem scr_in (hL : L.Ok) : InBuf L ⟨L.scr, L.r.toNat * 128⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen; omega_using [this]))))

theorem blk_toNat (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  exact toNat_add_ofNat _ (by omega_arith)

/-- The doubleword ROMix may run if `b`, `v` and `scratch` are aligned. -/
abbrev Aligned (L : Lay) (wide : Bool) : Prop :=
  wide = true → L.b.toNat % 8 = 0 ∧ L.v.toNat % 8 = 0 ∧ L.scr.toNat % 8 = 0

theorem romix_pre (hL : L.Ok) {t : State} {i : Nat} (hi : i < L.pp) {wide : Bool}
    (hal : Aligned L wide) (ha : RomixArgs L (blkAt L i) t) :
    (Proof.Scrypt.roMixRISCV64 wide).pre (t.callEntry.withRegions [] (romixWr L i)) := by
  have hnB := hL.nB
  have haB := hL.aB
  have tb := blk_toNat hL hi
  have t1072 : (L.B + BitVec.ofNat 64 1072).toNat = L.B.toNat + 1072 := toNat_add_ofNat _ (by omega_using [hnB])
  simp only [Proof.Scrypt.roMixRISCV64, State.withRegions_rd, State.withRegions_wr,
    gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs),
    ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, t1072]
  have kb := Within.sub (within_off L.b (blk_le hL hi))
  have ks := Within.sub (within_base L.scr (n := L.r.toNat * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega_using [this]))
  have sv := (sv_stk L)
  refine ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks,
    (hL.kb.symm.sub_left kb).sub_right sv, hL.vc.sub_right ks, hL.kv.symm.sub_right sv,
    (hL.kc.symm.sub_left ks).sub_right sv, by rw [tb]; have := blk_le hL hi; have := hL.nb; omega_arith,
    hL.nv, by have := hL.nc; have := hL.slen; omega_arith, by omega_using [hnB], hL.rpos, hL.vmod,
    Whole.valid_pow hL.valid, by omega_using [haB], fun hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hal hw
  have e : 128 * L.r.toNat * i = 8 * (16 * L.r.toNat * i) := by simp only [Nat.mul_assoc]; omega_using []
  exact ⟨by rw [tb, e]; omega_using [h1], h2, h3⟩

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ ([] : List Region) ++ romixWr L i, ∃ R ∈ L.regions, Within r R := by
  simp only [romixWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.BB, by simp, within_off _ (blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen; omega_using [this])⟩
  · exact ⟨L.FR, by simp, sv_within L⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact scr_in hL
  · exact .inr (.inr (.inr (.inr (within_base _ (Nat.le_refl _)))))

theorem roMix_sdepth (wide : Bool) : sdepth (Impl.Scrypt.RISCV64.roMix wide) ≤ 992 := by
  cases wide <;> lit_decide

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) {wide : Bool}
    (hal : Aligned L wide) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide)) t fun t' => Ctx L g m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.B, 992⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkAt L i) (128 * L.r.toNat)) := by
  refine call_ok hL RoMix.roMix_correct (roMix_sdepth wide) hc (romix_pre hL hi hal ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [Proof.Scrypt.roMixRISCV64, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), ha.a0, ha.a1, ha.a3] at h
  exact h

end

/-! ## The password, the salt and the blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem L.pw L.pwl.toNat = bytesAt m₀ L.pw L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega_using [])

theorem salt_bytes : bytesAt t.mem L.salt L.sl.toNat = bytesAt m₀ L.salt L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega_using [])

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
  refine Offset.disjoint _ ?_ (by omega_using [h₁, this]) (by omega_using [h₂, this])
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega_using [this]
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega_using [this]

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega_using [this])

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String)
include hv hd

omit hv hd in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [toNat_ofNat_lt hb]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_ofNat_lt hb]; exact hL.sb
  · rw [toNat_ofNat_lt hb]; exact hL.nb
  · rw [toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (ha : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hd name hL hc ha (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k :=
  WP.seq (WP.mono (pbk1Args_ok hc he) fun _ ⟨hc₁, _, ha₁⟩ => pbk1_call_ok hv hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = blkAt L i
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
  (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Offset.sub_base _ (by decide))

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :
    WP isa (.block cur0) t (Inv L g m₀ 0) :=
  WP.mono (cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', ⟨hb.trans (blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
      (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)⟩⟩

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
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega_using [h₁, hb]
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [bne, Offset.ofNat_sub_ofNat_beq e₂ e₁, decide_not]
  refine congrArg (!·) (decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact (Nat.eq_of_mul_eq_mul_left (by omega_using [hr]) h).symm

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t) {wide : Bool}
    (hal : Aligned L wide) (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide)) t fun t' =>
      Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (romix_call hL hc hi hal ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hL.kept_buf (by decide) (by decide) (.inl rfl) (Within.sub (within_off _ (blk_le hL hi)))
    · exact hL.kept_buf (by decide) (by decide) (.inr (.inl rfl)) (Within.sub (within_base _ (Nat.le_refl _)))
    · exact hL.kept_buf (by decide) (by decide) (.inr (.inr (.inl rfl)))
        (Within.sub (within_base _ (by have := hL.slen; omega_using [this])))
    · exact Offset.disjoint _ (by decide) (by omega_using []) (by omega_using [])
    · exact Offset.disjoint_base _ (by decide) (by omega_using [])
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (blkAt L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact blk_disj hL hk hi hki
          · exact hL.bv.sub_left (blk_sub hL hk)
          · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
              (Within.sub (within_base _ (by have := hL.slen; omega_using [this])))
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (sv_stk L)
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (fun x hx => by
              simp only [Region.Contains] at hx ⊢; omega_using [hx]))
          (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega_using [hlt]
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega_using [hki, hlt]
        simp only [hlt, this, ite_false]

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hm : Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧ InvB L m₀ (i + 1) t' ∧
      (t'.gpr .t0 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.mono (nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hx₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
        (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)⟩,
      by rw [hx₃, next_eq, left_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} {wide : Bool} (hal : Aligned L wide)
    (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide))
      (.block nextBlock))) t fun t' =>
        Inv L g m₀ (i + 1) t' ∧ (t'.gpr .t0 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.seq (WP.mono (romixArgs_ok hL h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (call_step hL hi hc₁ hal ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => WP.mono (next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} {wide : Bool} (hal : Aligned L wide) (h : Inv L g m₀ 0 t) :
    WP isa (romixLoop wide) t (Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi hal h) h

/-- Each of three doublewords is aligned if their OR is. -/
theorem al3 (a b c : BitVec 64) :
    ((a ||| b ||| c) &&& BitVec.ofInt 64 7 == 0) =
      decide (a.toNat % 8 = 0 ∧ b.toNat % 8 = 0 ∧ c.toNat % 8 = 0) := by
  have h1 := or_and7 (a ||| b) c
  have h2 := or_and7 (a ||| b) (a ||| b)
  rw [BitVec.or_self, or_and7 a b] at h2
  have e := decide_eq_decide.mp h2
  rw [h1]
  exact decide_eq_decide.mpr ⟨fun ⟨hp, hc⟩ => ⟨(e.mpr ⟨hp, hp⟩).1, (e.mpr ⟨hp, hp⟩).2, hc⟩,
    fun ⟨ha, hb, hc⟩ => ⟨(e.mp ⟨ha, hb⟩).1, hc⟩⟩

/-- ROMix on each block, by doublewords if `b`, `v` and `scratch` allow it. -/
theorem all_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) :
    WP isa romixAll t (Inv L g m₀ L.pp) := by
  refine WP.seq (WP.mono (alignBits_ok hL h.1) fun t₁ ⟨hc₁, hm₁, ht₁⟩ => ?_)
  have h₁ : Inv L g m₀ 0 t₁ := ⟨hc₁, by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩
  by_cases ha : L.b.toNat % 8 = 0 ∧ L.v.toNat % 8 = 0 ∧ L.scr.toNat % 8 = 0
  · refine WP.ite true (by rw [eval_zero, ht₁, al3, decide_eq_true ha]) (fun _ => ?_) fun h => by cases h
    exact loop_ok hL (fun _ => ha) h₁
  · refine WP.ite false (by rw [eval_zero, ht₁, al3, decide_eq_false ha]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hL (fun h => by cases h) h₁

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String)
include hv hd

omit hv hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
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
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (.inl (within_base _ (Nat.le_refl _))))), ?_,
    ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_ofNat_lt hb]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_ofNat_lt hb]; exact hL.bo
  · rw [toNat_ofNat_lt hb]; exact hL.kb
  · rw [toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (pbk2Args_ok hL h.1) fun t₁ ⟨hc₁, hm₁, ha₁⟩ => ?_)
  refine WP.mono (pbk_call hv hd name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [toNat_ofNat_lt hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

/-- The frame's body after `setup` and before `restore`. -/
theorem rest_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) {Q : State → Prop}
    (hQ : ∀ t', Ctx L g m₀ t' →
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) → WP isa (.block Impl.Scrypt.RISCV64.Whole.restore) t' Q) :
    WP isa (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixAll
      (.seq (pbkCall name pbk pbk2Args) (.block Impl.Scrypt.RISCV64.Whole.restore))))) t Q := by
  refine WP.seq (WP.mono (step1_ok hv hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (all_ok hL h₂) fun t₃ h₃ => ?_)
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
variable {pbk : Prog isa} (hv : PbkOk pbk) (hd : sdepth pbk ≤ 992) (name : String)
include hv hd

/-- `vg_scrypt` meets `scryptRV` and the calling convention. -/
theorem scrypt_ok {s : State} (h : scryptRV.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ scryptRV.post s s' := by
  have hL := lay_ok h
  have h1248 : 1248 ≤ s.sp.toNat := h.1
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by simp only [locals]; omega_using [h1248]) ?_
  refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, he⟩ => ?_)
  refine rest_ok hv hd name hL hc he fun u hu ho => WP.mono (restore_ok hL hu) fun v ⟨vra, vm, vsp, _, _, vg⟩ mL _ fl => ?_
  refine ⟨⟨fun r hr => vg r hr, ?_, vra⟩, ?_⟩
  · show v.sp + BitVec.ofNat 64 256 = s.sp
    rw [vsp, hu.sp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact lay_top s
  · -- The `free` loses the frame's bytes, which lie apart from the output.
    refine Eq.trans ?_ (congrArg some (List.map_congr_left fun i hi =>
      (lost_byte fl (R := (lay s).OUT)
        (hL.ko.symm.sub_right (Offset.sub_below _ (by decide) (by decide))) (List.mem_range.mp hi)).symm))
    show _ = some (bytesAt v.mem _ _)
    rw [vm]
    exact ho

end

end VG.Proof.Scrypt.RISCV64.Whole

end

end

/-!
# scrypt on RISC-V: constant time, up to the indices `j`, and the shared contract

As on PPC64LE (`Proof/Scrypt/PPC64LE/Whole/Verified.lean`): two runs whose
public data agree have the same layout, so in the frame's body they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs), whatever their secrets, and the indices of all the scryptROMix
calls agree (`LeakEq`). The blocks address only the frame, from `s3`, which
`Ctx` fixes (the taint analysis); each call is of constant-time code whose
public data agree (`RelCT.call`); the branch on the pointers' alignment and
the loop's branch agree since both runs have the same pointers and count the
same blocks. The frame leaks nothing (`RelCT.allocFrame`).

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 correct and
constant-time under `pbkK` with at most 992 bytes of stack, is verified
against `Spec.Scrypt.scryptContract` for the 1248 bytes of stack its frame
and calls use (`scrypt_verified_of`); and so is the one calling PBKDF2 made
with SHA-256 (`scrypt_verified`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.Impl.Scrypt.RISCV64.Whole
open VG.Proof.Pbkdf2.Whole.RISCV64 (pbkR)
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
  m₁ : Mem
  m₂ : Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ LeakEq e.L e.m₁ e.m₂ ∧ Ctx e.L e.g₁ e.m₁ a ∧ Ctx e.L e.g₂ e.m₂ b ∧
    Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- Two states in the frame's body agree on the stack pointer and `s3`. -/
theorem agree_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.s3]) t₁ t₂ :=
  ⟨c₁.sp.trans c₂.sp.symm, fun r hr => by
    have : r = .s3 := by simpa using hr
    subst this
    exact c₁.s3.trans c₂.s3.symm⟩

/-- A block whose addresses depend only on `s3`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.RISCV64.Taint.T}
    (h : (taint.check (VG.RISCV64.Taint.ofRegs [.s3]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.s3])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_two c₁ c₂) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ m₁ m₂, L.Ok → LeakEq L m₁ m₂ → Ctx L g₁ m₁ t₁ →
      Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, InBuf L r)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
    have w₁ := covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)
    have w₂ := covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)
    exact RelCT.call (n := n) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨hpre _ _ _ _ hL c₁ f₁, hpre _ _ _ _ hL c₂ f₂,
          hpub _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, w₁.1, w₁.2, w₂.1, w₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-! ## The calls -/

theorem pbk_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    {t₁ t₂ : State} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {salt : Addr} {sl : BitVec 64}
    {out : Addr} {ol : BitVec 64} (a₁ : PbkArgs L salt sl out ol t₁) (a₂ : PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (pbkRd L salt sl) (pbkWr out ol))
      (t₂.callEntry.withRegions (pbkRd L salt sl) (pbkWr out ol)) := by
  simp only [pbkK, pbkR, gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a6 ∉ linkRegs),
    a₁.a0, a₁.a1, a₁.a2, a₁.a3, a₁.a4, a₁.a5, a₁.a6, a₂.a0, a₂.a1, a₂.a2, a₂.a3, a₂.a4, a₂.a5, a₂.a6,
    c₁.ce_sp, c₂.ce_sp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} {m₀ : Mem} {t : State} {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t)
    (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (blkAt L i) (128 * L.r.toNat) = X L m₀ i := by
  rw [State.withRegions_mem, State.callEntry_mem, hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} {t₁ t₂ : State} (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ t₁)
    (c₂ : Ctx L g₂ m₂ t₂) {i : Nat} (hi : i < L.pp) (b₁ : InvB L m₁ i t₁) (b₂ : InvB L m₂ i t₂)
    (a₁ : RomixArgs L (blkAt L i) t₁) (a₂ : RomixArgs L (blkAt L i) t₂) (wide : Bool) :
    (Proof.Scrypt.roMixRISCV64 wide).pub (t₁.callEntry.withRegions [] (romixWr L i))
      (t₂.callEntry.withRegions [] (romixWr L i)) := by
  simp only [Proof.Scrypt.roMixRISCV64, gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs), a₁.a0, a₁.a1, a₁.a2, a₁.a3, a₁.a4, a₁.a5, a₂.a0,
    a₂.a1, a₂.a2, a₂.a3, a₂.a4, a₂.a5, c₁.ce_sp, c₂.ce_sp, true_and,
    romix_bytes hi b₁, romix_bytes hi b₂]
  exact leak_X hk hi

/-! ## The loop -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (wide : Bool) (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (wide : Bool) (n : Nat) :
    RelCT isa (Two (LoopAt wide n)) (.seq (.block romixArgs) (.seq (.call (roMixName wide)
      (Impl.Scrypt.RISCV64.roMix wide)) (.block nextBlock)))
      (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .t0 != 0) = decide (L.pp - n + 1 ≠ L.pp)) := by
  have a : RelCT isa (Two (LoopAt wide n)) (.block romixArgs) (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧
      n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨hal, h0, hn, hb⟩ =>
      WP.mono (romixArgs_ok hL hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', hal, h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t) (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide))
      (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) :=
    two_call RoMix.roMix_correct (RoMix.roMix_ct wide) (fun _ => []) (fun L => romixWr L (L.pp - n))
      (fun _ _ _ _ hL _ ⟨hal, h0, hn, _, ha⟩ => romix_pre hL (by omega_using [h0, hn]) hal ha)
      (fun _ _ _ _ _ _ _ _ hk c₁ c₂ ⟨_, h0, hn, b₁, a₁⟩ ⟨_, _, _, b₂, a₂⟩ =>
        romix_pub_two hk c₁ c₂ (by omega_using [h0, hn]) b₁ b₂ a₁ a₂ wide)
      (fun _ _ _ hL ⟨_, h0, hn, _⟩ => romix_sub hL (by omega_using [h0, hn]))
      (fun _ _ _ hL ⟨_, h0, hn, _⟩ => romix_wsub hL (by omega_using [h0, hn]))
      (fun _ _ _ _ hL hc ⟨hal, h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega_using [h0, hn]) hc hal hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', hal, h0, hn, hm⟩)
  have c : RelCT isa (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)
      (.block nextBlock)
      (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .t0 != 0) = decide (L.pp - n + 1 ≠ L.pp)) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨hal, h0, hn, hm⟩ =>
      WP.mono (next_step hL (by omega_using [h0, hn]) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', hal, h0, hn, hb, hz⟩
  exact a.seq (b.seq c)

theorem loop_ct (wide : Bool) :
    RelCT isa (Two fun L m₀ t => Aligned L wide ∧ InvB L m₀ 0 t) (romixLoop wide)
      (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval (.nonzero .t0) x = some (x.gpr .t0 != 0) := fun x =>
    eval_nonzero x .t0
  have h := fun n => RelCT.loop (M := isa) (c := .nonzero .t0)
    (Q := Two fun L m₀ t => InvB L m₀ L.pp t)
    (fun n => Two (LoopAt wide n)) (fun n => (body_ct wide n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨hal, h0, hn, b₁, z₁⟩, ⟨hal₂, -, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show InvB e.L _ e.L.pp a from hl ▸ b₁,
          show InvB e.L _ e.L.pp b from hl ▸ b₂⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega_using [h0, hn]
        exact ⟨n - 1, by omega_using [h0], e, hL, hk, c₁, c₂, ⟨hal, by omega_using [h0, hn, hl], by omega_using [hn], e₁ ▸ b₁⟩,
          ⟨hal₂, by omega_using [h0, hn, hl], by omega_using [hn], e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, ⟨hal₁, b₁⟩, ⟨hal₂, b₂⟩⟩ => ⟨e.L.pp, e, hL, hk,
    c₁, c₂, ⟨hal₁, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hal₂, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

theorem all_ct :
    RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) romixAll (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have a : RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) (.block alignBits)
      (Two fun L m₀ t => InvB L m₀ 0 t ∧ t.gpr .t0 = alBits L) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc hb =>
      WP.mono (alignBits_ok hL hc) fun _ ⟨hc', hm, ht⟩ =>
        ⟨hc', ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ht⟩
  have ev : ∀ (L : Lay) (x : State), x.gpr .t0 = alBits L →
      isa.eval (.zero .t0) x = some (decide (L.b.toNat % 8 = 0 ∧ L.v.toNat % 8 = 0 ∧ L.scr.toNat % 8 = 0)) :=
    fun L x hx => by rw [eval_zero, hx, al3]
  have ht : RelCT isa (fun s₁ s₂ => Two (fun L m₀ t => InvB L m₀ 0 t ∧ t.gpr .t0 = alBits L) s₁ s₂ ∧
      isa.eval (.zero .t0) s₁ = some true) (romixLoop true) (Two fun L m₀ t => InvB L m₀ L.pp t) := by
    refine (loop_ct true).mono (fun _ _ h => ?_) fun _ _ h => h
    obtain ⟨⟨e, hL, hk, c₁, c₂, ⟨b₁, h₁⟩, ⟨b₂, _⟩⟩, hz⟩ := h
    rw [ev _ _ h₁, Option.some.injEq] at hz
    have hal := of_decide_eq_true hz
    exact ⟨e, hL, hk, c₁, c₂, ⟨fun _ => hal, b₁⟩, ⟨fun _ => hal, b₂⟩⟩
  have he : RelCT isa (fun s₁ s₂ => Two (fun L m₀ t => InvB L m₀ 0 t ∧ t.gpr .t0 = alBits L) s₁ s₂ ∧
      isa.eval (.zero .t0) s₁ = some false) (romixLoop false) (Two fun L m₀ t => InvB L m₀ L.pp t) := by
    refine (loop_ct false).mono (fun _ _ h => ?_) fun _ _ h => h
    obtain ⟨⟨e, hL, hk, c₁, c₂, ⟨b₁, _⟩, ⟨b₂, _⟩⟩, _⟩ := h
    exact ⟨e, hL, hk, c₁, c₂, ⟨fun h => Bool.noConfusion h, b₁⟩, ⟨fun h => Bool.noConfusion h, b₂⟩⟩
  refine a.seq (RelCT.ite (fun _ _ h => ?_) ht he)
  obtain ⟨e, _, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ := h
  rw [ev _ _ h₁, ev _ _ h₂]

/-! ## The whole function -/

/-- Two calls whose public data agree, in the frame. -/
def Entered (a b : State) : Prop :=
  ∃ s₁ s₂, scryptRV.pre s₁ ∧ scryptRV.pre s₂ ∧ scryptRV.pub s₁ s₂ ∧
    a = allocd locals s₁ ∧ b = allocd locals s₂

theorem save_ct : RelCT isa Entered (.block setup) (Two fun L _ t => Entry L t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp, hlk⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (VG.RISCV64.Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show s₁.sp - _ = s₂.sp - _; rw [hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay s₂ = lay s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp]
  refine ⟨ht, ⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, y₁.1, e ▸ y₂.1, y₁.2,
    e ▸ y₂.2⟩
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h6, ← a0] at hlk
  exact hlk

/-- The state a frame's body starts in. -/
theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocd n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- Two runs of a frame that reserves stack leak the same trace if the runs of
its body do: reserving it accesses no memory. -/
theorem RelCT.allocFrame {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (hb : RelCT isa (fun x y => ∃ a b, P a b ∧ isa.push (.alloc n) a = some x ∧ isa.push (.alloc n) b = some y)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp [addrs]

section
variable {pbk : Prog isa} (hv : PbkOk pbk) (hct : ConstantTime isa pbkK.pre pbkK.pub pbk)
  (hd : sdepth pbk ≤ 992) (name : String)
include hv hct hd

theorem rest_ct : RelCT isa (Two fun L _ t => Entry L t)
    (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixAll
      (.seq (pbkCall name pbk pbk2Args) (.block Impl.Scrypt.RISCV64.Whole.restore)))))
    fun _ _ => True := by
  have p1a : RelCT isa (Two fun L _ t => Entry L t) (.block pbk1Args)
      (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hc he =>
      WP.mono (pbk1Args_ok hc he) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :=
    two_call hv hct (fun L => pbkRd L L.salt L.sl)
      (fun L => pbkWr L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk1_regions hL))
      (fun _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub (pbk1_regions hL)) (fun _ _ _ hL _ => pbk_wsub (pbk1_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk1_call_ok hv hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k)
      (.block cur0) (Two fun L m₀ t => InvB L m₀ 0 t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc hx => (start_ok hL hc hx).mono fun _ h => h
  have p2a : RelCT isa (Two fun L m₀ t => InvB L m₀ L.pp t) (.block pbk2Args)
      (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc _ =>
      WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (Two fun _ _ _ => True) :=
    two_call hv hct (fun L => pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => pbkWr L.out L.ol)
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk2_regions hL))
      (fun _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub (pbk2_regions hL)) (fun _ _ _ hL _ => pbk_wsub (pbk2_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk_call hv hd name hL hc ha (pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  have rs : RelCT isa (Two fun _ _ _ => True) (.block Impl.Scrypt.RISCV64.Whole.restore) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.s3])
      (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_two c₁ c₂) (by taint_decide)
  exact (p1a.seq p1c).seq (c0.seq (all_ct.seq ((p2a.seq p2c).seq rs)))

theorem scrypt_ct : ConstantTime isa scryptRV.pre scryptRV.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.allocFrame ?_)
  refine (save_ct.seq (rest_ct hv hct hd name)).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, pa, pb⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, alloc_eq pa, alloc_eq pb⟩

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified RISCV64.target (scrypt name pbk) (Spec.Scrypt.scryptContract RISCV64.abi stackBytes) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := scrypt_ok hv hd name h
    exact ⟨t, s', he, hp⟩) (scrypt_ct hv hct hd name) scrypt_implies

end

/-! ## With PBKDF2 made with SHA-256 -/

/-- PBKDF2-HMAC-SHA256's code. -/
abbrev pbkCode : Prog isa := Proof.Pbkdf2.Whole.RISCV64.Sha256.F.pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2Api.name ++ "_core"

theorem pbk_ok : PbkOk pbkCode := fun _ hs =>
  Proof.Pbkdf2.Whole.RISCV64.correct Proof.Pbkdf2.Whole.RISCV64.Sha256.okF hs

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbkCode :=
  Proof.Pbkdf2.Whole.RISCV64.ct Proof.Pbkdf2.Whole.RISCV64.Sha256.okF
    Proof.Pbkdf2.Whole.RISCV64.Sha256.checks

theorem sdepth_noFrames : ∀ c : Prog isa, c.noFrames = true → sdepth c = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [sdepth, sdepth_noFrames a h.1, sdepth_noFrames b h.2, Nat.max_self]
  | .ite _ a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [sdepth, sdepth_noFrames a h.1, sdepth_noFrames b h.2, Nat.max_self]
  | .loop b _, h => sdepth_noFrames b h
  | .call _ b, h => sdepth_noFrames b h
  | .frame .., h => by cases h
  | .icall _ _ b n, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [sdepth, sdepth_noFrames b h.1, sdepth_noFrames n h.2, Nat.max_self]

theorem pbk_sdepth : sdepth pbkCode ≤ 992 := by
  have h1 := Proof.Pbkdf2.Whole.RISCV64.hi_sdepth Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.hH
  have h2 := Proof.Pbkdf2.Whole.RISCV64.hf_sdepth Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.hH
  have h3 := Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.hH.updSd
  have h4 := sdepth_noFrames _ Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.itNf
  have h5 : Proof.Pbkdf2.Whole.RISCV64.Sha256.F.itB + Proof.Pbkdf2.Whole.RISCV64.Sha256.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Sha256.F.X = 992 := by decide
  simp only [Impl.Pbkdf2.Whole.RISCV64.Fns.X] at h5
  simp only [pbkCode, Impl.Pbkdf2.Whole.RISCV64.Fns.pbkdf2, Impl.Pbkdf2.Whole.RISCV64.Fns.main,
    Impl.Pbkdf2.Whole.RISCV64.Fns.callHi, Impl.Pbkdf2.Whole.RISCV64.Fns.callHf,
    Impl.Pbkdf2.Whole.RISCV64.Fns.callIt, Impl.Pbkdf2.Whole.RISCV64.Fns.block,
    Impl.Pbkdf2.Whole.RISCV64.Fns.outLen, Impl.Pbkdf2.Whole.RISCV64.Fns.outLoop,
    Impl.Hmac.Stream.RISCV64.Hash.callUpd, sdepth, Instr.frameBytes, h4]
  omega_using [h1, h2, h3, h5]

/-- `vg_scrypt` calling `vg_pbkdf2_hmac_sha256`. -/
theorem scrypt_verified :
    Verified RISCV64.target (scrypt pbkName pbkCode) (Spec.Scrypt.scryptContract RISCV64.abi stackBytes) :=
  scrypt_verified_of pbk_ok pbk_ct pbk_sdepth pbkName

end VG.Proof.Scrypt.RISCV64.Whole
