import VerifiedGarbage.Proof.Scrypt.X86.RoMixCT
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Impl.Scrypt.X86.Scrypt
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Framework.X86.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86.Whole.Calls`. -/
section

section

/-!
# scrypt on x86 (32-bit): where everything is

As on x86-64 (`Proof/Scrypt/X86_64/Whole/Layout.lean`): the contract the proof
is written against (`scryptX86`), the function's buffers and the 116 bytes of
stack below its return address, from `A` up (`Lay`): the 80 bytes the calls
use, then the frame (36 bytes, from `A + 80`: the callee's arguments, then the
next block). The return address is at `A + 116`, our arguments from `A + 120`.
`Ctx` is what holds between the frame's push and pop: the permissions, `esp`,
the callee-saved registers, our arguments (`Kept`), and that memory changed
only in the writable buffers and the stack.
-/

namespace VG.Proof.Scrypt

open VG.X86 in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. x86 contract for `vg_scrypt(password,
password_len, salt, salt_len, r, b, blen, v, vlen, scratch, slen, out,
out_len)`, every argument on the stack, with 116 bytes of stack below the
return address. -/
def scryptX86 : Contract X86.isa where
  pre s :=
    let r := (VG.X86.arg s 4).toNat
    let pwR : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
    let saltR : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let bR : Region := ⟨(VG.X86.arg s 5).setWidth 64, (VG.X86.arg s 6).toNat * 128⟩
    let vR : Region := ⟨(VG.X86.arg s 7).setWidth 64, (VG.X86.arg s 8).toNat * 128⟩
    let scR : Region := ⟨(VG.X86.arg s 9).setWidth 64, (VG.X86.arg s 10).toNat * 128⟩
    let outR : Region := ⟨(VG.X86.arg s 11).setWidth 64, (VG.X86.arg s 12).toNat⟩
    let args : Region := ⟨argAddr s 0, 52⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116, 116⟩
    116 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 56 ≤ 2 ^ 32 ∧
    s.rd = [pwR, saltR] ∧ s.wr = [bR, vR, scR, outR, args] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧ pwR.Disjoint args ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    saltR.Disjoint args ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    ret.Disjoint pwR ∧ ret.Disjoint saltR ∧ ret.Disjoint bR ∧ ret.Disjoint vR ∧ ret.Disjoint scR ∧
    ret.Disjoint outR ∧ ret.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧ stack.Disjoint args ∧
    (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 5).toNat + (VG.X86.arg s 6).toNat * 128 ≤ 2 ^ 32 ∧ (VG.X86.arg s 7).toNat + (VG.X86.arg s 8).toNat * 128 ≤ 2 ^ 32 ∧
    (VG.X86.arg s 9).toNat + (VG.X86.arg s 10).toNat * 128 ≤ 2 ^ 32 ∧ (VG.X86.arg s 11).toNat + (VG.X86.arg s 12).toNat ≤ 2 ^ 32 ∧
    0 < r ∧ (VG.X86.arg s 6).toNat % r = 0 ∧ (VG.X86.arg s 8).toNat % r = 0 ∧
    Spec.Scrypt.valid ((VG.X86.arg s 8).toNat / r) r ((VG.X86.arg s 6).toNat / r) (VG.X86.arg s 12).toNat ∧
    (VG.X86.arg s 12).toNat ≤ (2 ^ 32 - 1) * 32 ∧ (VG.X86.arg s 10).toNat = r + 16
  post s s' :=
    let r := (VG.X86.arg s 4).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
      (Spec.Scrypt.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat) ((VG.X86.arg s 8).toNat / r) r
      ((VG.X86.arg s 6).toNat / r) (VG.X86.arg s 12).toNat =
      some (Spec.Scrypt.bytesAt s'.mem ((VG.X86.arg s 11).setWidth 64) (VG.X86.arg s 12).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 13, VG.X86.arg s₁ i = VG.X86.arg s₂ i) ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem ((VG.X86.arg s₁ 0).setWidth 64) (VG.X86.arg s₁ 1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem ((VG.X86.arg s₁ 2).setWidth 64) (VG.X86.arg s₁ 3).toNat) (VG.X86.arg s₁ 4).toNat
        ((VG.X86.arg s₁ 6).toNat / (VG.X86.arg s₁ 4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (VG.X86.arg s₁ 4).toNat ((VG.X86.arg s₁ 8).toNat / (VG.X86.arg s₁ 4).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem ((VG.X86.arg s₂ 0).setWidth 64) (VG.X86.arg s₂ 1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem ((VG.X86.arg s₂ 2).setWidth 64) (VG.X86.arg s₂ 3).toNat) (VG.X86.arg s₂ 4).toNat
        ((VG.X86.arg s₂ 6).toNat / (VG.X86.arg s₂ 4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (VG.X86.arg s₂ 4).toNat ((VG.X86.arg s₂ 8).toNat / (VG.X86.arg s₂ 4).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86
open VG.Proof.Pbkdf2.Whole.X86 (toNat_setWidth64)

/-- The arguments and the lowest byte of the stack used (`esp - 116` on entry). -/
structure Lay where
  pw : BitVec 32
  pwl : BitVec 32
  salt : BitVec 32
  sl : BitVec 32
  r : BitVec 32
  b : BitVec 32
  blen : BitVec 32
  v : BitVec 32
  vlen : BitVec 32
  scr : BitVec 32
  slen : BitVec 32
  out : BitVec 32
  ol : BitVec 32
  B : BitVec 32

namespace Lay

variable (L : VG.Proof.Scrypt.X86.Whole.Lay)

/-- The lowest byte of the stack used, as an address. -/
abbrev A : Addr := L.B.setWidth 64

abbrev PW : Region := ⟨L.pw.setWidth 64, L.pwl.toNat⟩
abbrev SALT : Region := ⟨L.salt.setWidth 64, L.sl.toNat⟩
abbrev BB : Region := ⟨L.b.setWidth 64, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨L.scr.setWidth 64, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨L.out.setWidth 64, L.ol.toNat⟩
/-- Our arguments. -/
abbrev ARGS : Region := ⟨L.A + BitVec.ofNat 64 120, 52⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.A, 116⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.A + BitVec.ofNat 64 80, 36⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.A + BitVec.ofNat 64 116, 4⟩

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
  pa : L.PW.Disjoint L.ARGS
  sb : L.SALT.Disjoint L.BB
  sv : L.SALT.Disjoint L.VV
  sc : L.SALT.Disjoint L.SC
  so : L.SALT.Disjoint L.OUT
  sa : L.SALT.Disjoint L.ARGS
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
  rp : L.RET.Disjoint L.PW
  rs : L.RET.Disjoint L.SALT
  rb : L.RET.Disjoint L.BB
  rv : L.RET.Disjoint L.VV
  rc : L.RET.Disjoint L.SC
  ro : L.RET.Disjoint L.OUT
  kp : L.STK.Disjoint L.PW
  ks : L.STK.Disjoint L.SALT
  kb : L.STK.Disjoint L.BB
  kv : L.STK.Disjoint L.VV
  kc : L.STK.Disjoint L.SC
  ko : L.STK.Disjoint L.OUT
  np : L.pw.toNat + L.pwl.toNat ≤ 2 ^ 32
  ns : L.salt.toNat + L.sl.toNat ≤ 2 ^ 32
  nb : L.b.toNat + L.blen.toNat * 128 ≤ 2 ^ 32
  nv : L.v.toNat + L.vlen.toNat * 128 ≤ 2 ^ 32
  nc : L.scr.toNat + L.slen.toNat * 128 ≤ 2 ^ 32
  no : L.out.toNat + L.ol.toNat ≤ 2 ^ 32
  nB : L.B.toNat + 172 ≤ 2 ^ 32
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

theorem Within.sub {r R : Region} (h : VG.Proof.Scrypt.X86.Whole.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    VG.Proof.Scrypt.X86.Whole.Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : VG.Proof.Scrypt.X86.Whole.Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A word `B + k` of the stack, as an address. -/
theorem addr_B {B : BitVec 32} {k : Nat} (h : B.toNat + k < 2 ^ 32) :
    (B + BitVec.ofNat 32 k).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have := B.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := B.toNat + k) h,
    Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := B.toNat) (by omega),
    Nat.mod_eq_of_lt (a := B.toNat + k) (by omega)]

/-- A writable region is within one of the writable buffers. -/
def InBuf (L : VG.Proof.Scrypt.X86.Whole.Lay) (r : Region) : Prop :=
  VG.Proof.Scrypt.X86.Whole.Within r L.BB ∨ VG.Proof.Scrypt.X86.Whole.Within r L.VV ∨ VG.Proof.Scrypt.X86.Whole.Within r L.SC ∨ VG.Proof.Scrypt.X86.Whole.Within r L.OUT

theorem InBuf.sub {L : VG.Proof.Scrypt.X86.Whole.Lay} {r : Region} (h : VG.Proof.Scrypt.X86.Whole.InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.X86.Whole.Lay} (h : L.Ok)
include h

omit h in
theorem toNat_A : L.A.toNat = L.B.toNat := toNat_setWidth64 _

/-- `[esp + d]` in the frame. -/
theorem ea_sp {d : Nat} (hd : d + 4 ≤ 92) :
    (L.B + BitVec.ofNat 32 80 + BitVec.ofNat 32 d).setWidth 64 = L.A + BitVec.ofNat 64 (80 + d) := by
  have := h.nB
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, VG.Proof.Scrypt.X86.Whole.addr_B (by omega)]

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_in {d n : Nat} (h₁ : d + n ≤ 116) {r : Region} (hr : VG.Proof.Scrypt.X86.Whole.InBuf L r) :
    Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.A + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  obtain ⟨R, hR, hsr⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hsr
  · exact (h.kv.sub_left hs).sub_right hsr
  · exact (h.kc.sub_left hs).sub_right hsr
  · exact (h.ko.sub_left hs).sub_right hsr

/-- A range in our arguments is disjoint from one in a writable buffer. -/
theorem args_in {d n : Nat} (h₁ : 120 ≤ d) (h₂ : d + n ≤ 172) {r : Region} (hr : VG.Proof.Scrypt.X86.Whole.InBuf L r) :
    Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.A + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  obtain ⟨R, hR, hsr⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hsr
  · exact (h.va.symm.sub_left hs).sub_right hsr
  · exact (h.ca.symm.sub_left hs).sub_right hsr
  · exact (h.oa.symm.sub_left hs).sub_right hsr

/-- The password misses every writable buffer. -/
theorem pw_in {r : Region} (hr : VG.Proof.Scrypt.X86.Whole.InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.pb.sub_right hs, h.pv.sub_right hs, h.pc.sub_right hs, h.po.sub_right hs]

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

end Lay.Ok

/-! ## What the calls cannot change -/

/-- Our arguments, the words from `A + 120` (`[esp + 40]` in the frame). -/
structure Kept (L : VG.Proof.Scrypt.X86.Whole.Lay) (m : Mem) : Prop where
  pw : m.readW (L.A + BitVec.ofNat 64 120) 32 = L.pw
  pwl : m.readW (L.A + BitVec.ofNat 64 124) 32 = L.pwl
  salt : m.readW (L.A + BitVec.ofNat 64 128) 32 = L.salt
  sl : m.readW (L.A + BitVec.ofNat 64 132) 32 = L.sl
  r : m.readW (L.A + BitVec.ofNat 64 136) 32 = L.r
  b : m.readW (L.A + BitVec.ofNat 64 140) 32 = L.b
  blen : m.readW (L.A + BitVec.ofNat 64 144) 32 = L.blen
  v : m.readW (L.A + BitVec.ofNat 64 148) 32 = L.v
  vlen : m.readW (L.A + BitVec.ofNat 64 152) 32 = L.vlen
  scr : m.readW (L.A + BitVec.ofNat 64 156) 32 = L.scr
  out : m.readW (L.A + BitVec.ofNat 64 164) 32 = L.out
  ol : m.readW (L.A + BitVec.ofNat 64 168) 32 = L.ol

/-- Our arguments survive changes to memory that miss them. -/
theorem Kept.frame {L : VG.Proof.Scrypt.X86.Whole.Lay} {m m' : Mem} {rs : List Region} (hk : VG.Proof.Scrypt.X86.Whole.Kept L m) (hf : Frame rs m m')
    (hd : ∀ R ∈ rs, L.ARGS.Disjoint R) : VG.Proof.Scrypt.X86.Whole.Kept L m' := by
  have k : ∀ d, 120 ≤ d → d + 4 ≤ 172 →
      m'.readW (L.A + BitVec.ofNat 64 d) 32 = m.readW (L.A + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := L.ARGS) (Offset.contains _ h₁ (by omega) (by omega))
      (fun R hR => hd R hR) (by decide)
  exact ⟨(k 120 (by omega) (by omega)).trans hk.pw, (k 124 (by omega) (by omega)).trans hk.pwl,
    (k 128 (by omega) (by omega)).trans hk.salt, (k 132 (by omega) (by omega)).trans hk.sl,
    (k 136 (by omega) (by omega)).trans hk.r, (k 140 (by omega) (by omega)).trans hk.b,
    (k 144 (by omega) (by omega)).trans hk.blen, (k 148 (by omega) (by omega)).trans hk.v,
    (k 152 (by omega) (by omega)).trans hk.vlen, (k 156 (by omega) (by omega)).trans hk.scr,
    (k 164 (by omega) (by omega)).trans hk.out, (k 168 (by omega) (by omega)).trans hk.ol⟩

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx (L : VG.Proof.Scrypt.X86.Whole.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT, L.ARGS]
  esp : t.gpr .esp = L.B + BitVec.ofNat 32 80
  cs : ∀ r ∈ calleeSaved, r ≠ .esp → t.gpr r = g r
  kept : VG.Proof.Scrypt.X86.Whole.Kept L t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : VG.Proof.Scrypt.X86.Whole.Lay) : List Region := [L.PW, L.SALT, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Scrypt.X86.Whole.Lay :=
  ⟨VG.X86.arg s 0, VG.X86.arg s 1, VG.X86.arg s 2, VG.X86.arg s 3, VG.X86.arg s 4, VG.X86.arg s 5, VG.X86.arg s 6, VG.X86.arg s 7, VG.X86.arg s 8, VG.X86.arg s 9, VG.X86.arg s 10,
    VG.X86.arg s 11, VG.X86.arg s 12, s.gpr .esp - BitVec.ofNat 32 116⟩

theorem lay_esp (s : State) :
    (VG.Proof.Scrypt.X86.Whole.lay s).B + BitVec.ofNat 32 116 = s.gpr .esp := BitVec.sub_add_cancel _ _

theorem lay_B {s : State} (h : 116 ≤ (s.gpr .esp).toNat) : (VG.Proof.Scrypt.X86.Whole.lay s).B.toNat = (s.gpr .esp).toNat - 116 :=
  sub_toNat h

theorem lay_args {s : State} (h : 116 ≤ (s.gpr .esp).toNat) (h' : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (VG.Proof.Scrypt.X86.Whole.lay s).A + BitVec.ofNat 64 120 = argAddr s 0 := by
  rw [Lay.A, ← VG.Proof.Scrypt.X86.Whole.addr_B (by rw [VG.Proof.Scrypt.X86.Whole.lay_B h]; omega)]
  simp only [VG.Proof.Scrypt.X86.Whole.lay, argAddr]
  congr 1
  bv_omega

theorem lay_ret {s : State} (h : 116 ≤ (s.gpr .esp).toNat) (h' : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (VG.Proof.Scrypt.X86.Whole.lay s).A + BitVec.ofNat 64 116 = (s.gpr .esp).setWidth 64 := by
  rw [Lay.A, ← VG.Proof.Scrypt.X86.Whole.addr_B (by rw [VG.Proof.Scrypt.X86.Whole.lay_B h]; omega), VG.Proof.Scrypt.X86.Whole.lay_esp s]

theorem lay_stk {s : State} (h : 116 ≤ (s.gpr .esp).toNat) :
    (VG.Proof.Scrypt.X86.Whole.lay s).A = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116 := by
  apply BitVec.eq_of_toNat_eq
  have := (s.gpr .esp).isLt
  rw [Lay.A, toNat_setWidth64, VG.Proof.Scrypt.X86.Whole.lay_B h, Offset.toNat_sub_ofNat, toNat_setWidth64]
  omega

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptX86.pre s) : (VG.Proof.Scrypt.X86.Whole.lay s).Ok := by
  obtain ⟨h116, h56, -, -, pb, pv, pc, po, pa, sb, sv, sc, so, sa, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    rp, rs, rb, rv, rc, ro, -, kp, ks, kb, kv, kc, ko, -, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval,
    olb, slen⟩ := h
  have ea : (VG.Proof.Scrypt.X86.Whole.lay s).ARGS = ⟨argAddr s 0, 52⟩ := by simp only [Lay.ARGS, VG.Proof.Scrypt.X86.Whole.lay_args h116 h56]
  have er : (VG.Proof.Scrypt.X86.Whole.lay s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by simp only [Lay.RET, VG.Proof.Scrypt.X86.Whole.lay_ret h116 h56]
  have ek : (VG.Proof.Scrypt.X86.Whole.lay s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116, 116⟩ := by
    simp only [Lay.STK, VG.Proof.Scrypt.X86.Whole.lay_stk h116]
  exact ⟨pb, pv, pc, po, ea ▸ pa, sb, sv, sc, so, ea ▸ sa, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co,
    ea ▸ ca, ea ▸ oa, er ▸ rp, er ▸ rs, er ▸ rb, er ▸ rv, er ▸ rc, er ▸ ro, ek ▸ kp, ek ▸ ks, ek ▸ kb,
    ek ▸ kv, ek ▸ kc, ek ▸ ko, np, ns, nb, nv, nc, no, by rw [VG.Proof.Scrypt.X86.Whole.lay_B h116]; omega, rpos, bmod, vmod, hval,
    olb, slen⟩

end VG.Proof.Scrypt.X86.Whole

end

section

/-!
# scrypt on x86 (32-bit): the blocks between the calls

The parameters as numbers (`Lay.Ok`), the frame's push (`push_ctx`), and what
each block between the calls does: it keeps `Ctx`, and sets up the next call's
arguments in the frame (`PbkArgs`, `RomixArgs`) or the next block.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Proof.Pbkdf2.Whole.X86 (toNat_setWidth64)

/-! ## Arithmetic -/

theorem ror25 (x : BitVec 32) (h : x.toNat < 2 ^ 25) :
    x.rotateRight 25 = BitVec.ofNat 32 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show 25 % 32 = 25 from rfl, Nat.div_eq_of_lt h, Nat.zero_or]

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.X86.Whole.Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

theorem blen_lt : L.blen.toNat * 128 < 2 ^ 32 := by
  have hnb := h.nb; have hB := h.nB
  refine Nat.lt_of_not_le fun hge => ?_
  have hb0 : L.b.toNat = 0 := by omega
  have e : L.blen.toNat * 128 = 2 ^ 32 := by omega
  have eb : L.b.setWidth 64 = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_setWidth64, hb0]; rfl
  apply h.kb L.A
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · have z : ∀ x : Addr, x - L.b.setWidth 64 = x := fun x => by rw [eb]; exact BitVec.sub_zero x
    simp only [Region.Contains, z, e, Lay.A, toNat_setWidth64]; omega

theorem blen25 : L.blen.toNat < 2 ^ 25 := by have := h.blen_lt; omega

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r25 : L.r.toNat < 2 ^ 25 := by have := h.blen25; have := h.r_le; omega

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
  omega

end Lay.Ok

/-! ## Words at offsets -/

/-- A word read back past a store of another at a different offset. -/
theorem rd_off {P : Addr} {m : Mem} {x y : Nat} {v : BitVec 32} (h : x + 4 ≤ y ∨ y + 4 ≤ x)
    (hx : x + 4 ≤ 2 ^ 32) (hy : y + 4 ≤ 2 ^ 32) :
    (m.writeW (P + BitVec.ofNat 64 y) v).readW (P + BitVec.ofNat 64 x) 32 =
      m.readW (P + BitVec.ofNat 64 x) 32 :=
  Mem.readW_writeW_sep (Offset.sep P h (by omega) (by omega)) (by decide)

/-! ## In the frame -/

theorem ea_esp (t : State) (d : Nat) : t.ea (sp d) = (t.gpr .esp + BitVec.ofNat 32 d).setWidth 64 := rfl

section
variable {L : VG.Proof.Scrypt.X86.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

namespace Ctx

variable {t t' : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t)
include hc

theorem inArgs (hL : L.Ok) (d : Nat) (h₁ : 120 ≤ d) (h₂ : d + 4 ≤ 172) :
    InRegions (t.rd ++ t.wr) (L.A + BitVec.ofNat 64 d) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

theorem inFr (hL : L.Ok) (d : Nat) (h₁ : 80 ≤ d) (h₂ : d + 4 ≤ 116) :
    InRegions (t.rd ++ t.wr) (L.A + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

theorem inFrW (hL : L.Ok) (d : Nat) (h₁ : 80 ≤ d) (h₂ : d + 4 ≤ 116) :
    InRegions t.wr (L.A + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

/-- Code that writes only the frame and registers other than the
callee-saved ones. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) (hf : Frame [L.FR] t.mem t'.mem) : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .esp (by simp [calleeSaved])).trans hc.esp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

/-- A store into the frame is in `FR`. -/
theorem Frame.fr (hL : L.Ok) {m m' : Mem} (hf : Frame [L.FR] m m') {k : Nat} (h₁ : 80 ≤ k)
    (h₂ : k + 4 ≤ 116) (v : BitVec 32) : Frame [L.FR] m (m'.writeW (L.A + BitVec.ofNat 64 k) v) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains _ h₁ (by omega) (by have := hL.nB; omega))

/-- The callee-saved registers, which the blocks leave alone. -/
macro "scrypt_cs_tac" : tactic => `(tactic| (
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes), in the frame. -/
structure PbkArgs (L : VG.Proof.Scrypt.X86.Whole.Lay) (salt sl out ol : BitVec 32) (m : Mem) : Prop where
  a0 : m.readW (L.A + BitVec.ofNat 64 80) 32 = L.pw
  a1 : m.readW (L.A + BitVec.ofNat 64 84) 32 = L.pwl
  a2 : m.readW (L.A + BitVec.ofNat 64 88) 32 = salt
  a3 : m.readW (L.A + BitVec.ofNat 64 92) 32 = sl
  a4 : m.readW (L.A + BitVec.ofNat 64 96) 32 = 1
  a5 : m.readW (L.A + BitVec.ofNat 64 100) 32 = out
  a6 : m.readW (L.A + BitVec.ofNat 64 104) 32 = ol
  a7 : m.readW (L.A + BitVec.ofNat 64 108) 32 = L.scr

/-! ## One instruction at a time

`Same t u`: `u` is `t` with other values in `eax`, `ecx`, `edx` and the
flags. The blocks load a word into `eax`, maybe change it, and store it in
the frame; each of these steps is proved once, for any offsets. -/

/-- `u` differs from `t` only in registers other than the callee-saved ones. -/
structure Same (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ calleeSaved, u.gpr r = t.gpr r
  mem : u.mem = t.mem

theorem Same.refl (t : State) : VG.Proof.Scrypt.X86.Whole.Same t t := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem Same.esp {t u : State} (h : VG.Proof.Scrypt.X86.Whole.Same t u) : u.gpr .esp = t.gpr .esp := h.cs .esp (by simp [calleeSaved])

theorem Same.setReg {t u : State} (h : VG.Proof.Scrypt.X86.Whole.Same t u) {r : Reg} (hr : r ∉ calleeSaved) (v : BitVec 32) :
    VG.Proof.Scrypt.X86.Whole.Same t (u.setReg r v) :=
  ⟨h.rd, h.wr, fun r' hr' => by
    rw [RegUpd.gpr_setReg]; split
    · subst r'; exact absurd hr' hr
    · exact h.cs r' hr', h.mem⟩

theorem Same.setFlags {t u : State} (h : VG.Proof.Scrypt.X86.Whole.Same t u) (a b c d : Option Bool) : VG.Proof.Scrypt.X86.Whole.Same t (u.setFlags a b c d) :=
  ⟨h.rd, h.wr, h.cs, h.mem⟩

theorem Same.arithFlags {t u : State} (h : VG.Proof.Scrypt.X86.Whole.Same t u) (x : BitVec 32) (c o : Bool) :
    VG.Proof.Scrypt.X86.Whole.Same t (VG.X86.arithFlags u x c o) := ⟨h.rd, h.wr, h.cs, h.mem⟩

theorem eax_cs : Reg.eax ∉ calleeSaved := by decide
theorem ecx_cs : Reg.ecx ∉ calleeSaved := by decide
theorem edx_cs : Reg.edx ∉ calleeSaved := by decide

/-- A step of a block, from a state `Same` as `t`. -/
def Step (t : State) (P : State → Prop) (is : List Instr) (Q : State → Prop) : Prop :=
  ∀ u, VG.Proof.Scrypt.X86.Whole.Same t u → P u → WP isa (.block is) u Q

/-- A load of `[esp + a]`, a word of the frame or of our arguments. -/
theorem ld_eq (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) (a : Nat) (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92)
    {u : State} (hu : VG.Proof.Scrypt.X86.Whole.Same t u) :
    readSrc u (.mem (sp a)) = some (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32) := by
  have hin : InRegions (u.rd ++ u.wr) (L.A + BitVec.ofNat 64 (80 + a)) 4 := by
    rw [hu.rd, hu.wr]
    rcases ha with ha | ha
    · exact hc.inFr hL _ (by omega) (by omega)
    · exact hc.inArgs hL _ (by omega) (by omega)
  simp only [readSrc, State.load32, VG.Proof.Scrypt.X86.Whole.ea_esp, hu.esp, hc.esp, hL.ea_sp (d := a) (by omega), hin, ↓reduceIte,
    hu.mem]

/-- `mov e, [esp + a]`. -/
theorem ld_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {e : Reg} (he : e ∉ calleeSaved) (a : Nat)
    (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92) {is : List Instr} {Q : State → Prop} {u : State}
    (hu : VG.Proof.Scrypt.X86.Whole.Same t u)
    (h : ∀ u', VG.Proof.Scrypt.X86.Whole.Same t u' → u'.gpr e = t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32 →
      (∀ r, r ≠ e → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) :
    WP isa (.block (.mov e (.mem (sp a)) :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ (hu.setReg he (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32))
    (RegUpd.gpr_setReg_self _ _ _) fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩
  simp only [exec, VG.Proof.Scrypt.X86.Whole.ld_eq hL hc a ha hu, Option.map_some]

/-- `mov e, imm`. -/
theorem imm_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) (x : BitVec 32) {is : List Instr}
    {Q : State → Prop} {u : State} (hu : VG.Proof.Scrypt.X86.Whole.Same t u)
    (h : ∀ u', VG.Proof.Scrypt.X86.Whole.Same t u' → u'.gpr e = x → (∀ r, r ≠ e → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) :
    WP isa (.block (.mov e (.imm x) :: is)) u Q :=
  WP.block_cons_iff.mpr ⟨_, rfl, h _ (hu.setReg he _) (RegUpd.gpr_setReg_self _ _ _)
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `ror e, 25`: times 128. -/
theorem ror_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) {is : List Instr}
    {Q : State → Prop} {u : State} (hu : VG.Proof.Scrypt.X86.Whole.Same t u)
    (h : ∀ u', VG.Proof.Scrypt.X86.Whole.Same t u' → u'.gpr e = (u.gpr e).rotateRight 25 → (∀ r, r ≠ e → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) :
    WP isa (.block (times128 e :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ ((hu.setFlags (some ((u.gpr e).rotateRight 25).msb) none u.zf u.sf).setReg
    he _) (RegUpd.gpr_setReg_self _ _ _) fun _ hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]⟩
  simp only [exec, execShift]
  rfl

/-- `add e, src`. -/
theorem add_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) {src : Src} {x : BitVec 32}
    {is : List Instr} {Q : State → Prop} {u : State} (hu : VG.Proof.Scrypt.X86.Whole.Same t u) (hx : readSrc u src = some x)
    (h : ∀ u', VG.Proof.Scrypt.X86.Whole.Same t u' → u'.gpr e = u.gpr e + x → (∀ r, r ≠ e → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) :
    WP isa (.block (.alu .add e src :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ ((hu.arithFlags (u.gpr e + x) (2 ^ 32 ≤ (u.gpr e).toNat + x.toNat)
    (addOverflow (u.gpr e) x (u.gpr e + x))).setReg he _) (RegUpd.gpr_setReg_self _ _ _)
    fun _ hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]⟩
  simp only [exec, execAlu, hx, Option.bind_some]

/-- `mov [esp + d], eax`, a word of the frame, ending a step. -/
theorem st_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) (d : Nat) (hd : d + 4 ≤ 36) {u : State}
    (hu : VG.Proof.Scrypt.X86.Whole.Same t u) {is : List Instr} {Q : State → Prop}
    (h : ∀ t', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem = t.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax) →
      (∀ r, t'.gpr r = u.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.store (sp d) .eax :: is)) u Q := by
  have hin : InRegions u.wr (L.A + BitVec.ofNat 64 (80 + d)) 4 := by
    rw [hu.wr]; exact hc.inFrW hL _ (by omega) (by omega)
  have hf : Frame [L.FR] t.mem (t.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax)) :=
    Frame.fr hL (Frame.refl _ _) (by omega) (by omega) _
  have hf' : Frame [L.FR] t.mem (u.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax)) := by
    rw [hu.mem]; exact hf
  refine WP.block_cons_iff.mpr ⟨{ u with mem := u.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax) },
    ?_, h _ (hc.store hL hu.rd hu.wr hu.cs hf') hf' (by rw [hu.mem]) fun _ => rfl⟩
  simp only [exec, State.store32, VG.Proof.Scrypt.X86.Whole.ea_esp, hu.esp, hc.esp, hL.ea_sp (d := d) (by omega), hin, ↓reduceIte]

/-- A word copied from `[esp + a]` to `[esp + d]`. -/
theorem cp_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) (a d : Nat)
    (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92) (hd : d + 4 ≤ 36) {is : List Instr} {Q : State → Prop}
    (h : ∀ t', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem = t.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32) →
      WP isa (.block is) t' Q) :
    WP isa (.block (.mov .eax (.mem (sp a)) :: .store (sp d) .eax :: is)) t Q :=
  VG.Proof.Scrypt.X86.Whole.ld_ok hL hc VG.Proof.Scrypt.X86.Whole.eax_cs a ha (Same.refl t) fun _ hu he _ =>
    VG.Proof.Scrypt.X86.Whole.st_ok hL hc d hd hu fun t' hc' hf hm _ => h t' hc' hf (he ▸ hm)

theorem frame_trans {t₁ t₂ t₃ : State} (h₁ : Frame [L.FR] t₁.mem t₂.mem) (h₂ : Frame [L.FR] t₂.mem t₃.mem) :
    Frame [L.FR] t₁.mem t₃.mem := h₁.trans h₂

theorem pbk1Args_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      VG.Proof.Scrypt.X86.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t'.mem → Q t') :
    WP isa (.block pbk1Args) t Q := by
  unfold pbk1Args
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc 40 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₁ 44 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₂ 48 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₃ 52 12 (by omega) (by omega) fun t₄ hc₄ hf₄ hm₄ => ?_
  refine VG.Proof.Scrypt.X86.Whole.imm_ok VG.Proof.Scrypt.X86.Whole.eax_cs 1 (Same.refl t₄) fun u hu he _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.st_ok hL hc₄ 16 (by omega) hu fun t₅ hc₅ hf₅ hm₅ _ => ?_
  rw [he] at hm₅
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₅ 60 20 (by omega) (by omega) fun t₆ hc₆ hf₆ hm₆ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ld_ok hL hc₆ VG.Proof.Scrypt.X86.Whole.eax_cs 64 (by omega) (Same.refl t₆) fun u hu he _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ror_ok VG.Proof.Scrypt.X86.Whole.eax_cs hu fun u' hu' he' _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.st_ok hL hc₆ 24 (by omega) hu' fun t₇ hc₇ hf₇ hm₇ _ => ?_
  rw [he', he, hc₆.kept.blen, VG.Proof.Scrypt.X86.Whole.ror25 _ hL.blen25] at hm₇
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₇ 76 28 (by omega) (by omega) fun t₈ hc₈ hf₈ hm₈ => ?_
  refine WP.block_nil (h t₈ hc₈ (VG.Proof.Scrypt.X86.Whole.frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    VG.Proof.Scrypt.X86.Whole.frame_trans hf₅ <| frame_trans hf₆ <| frame_trans hf₇ hf₈) ?_)
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  rw [hc.kept.pw] at hm₁; rw [hc₁.kept.pwl] at hm₂; rw [hc₂.kept.salt] at hm₃; rw [hc₃.kept.sl] at hm₄
  rw [hc₅.kept.b] at hm₆; rw [hc₇.kept.scr] at hm₈
  constructor <;> simp (disch := decide) only [hm₈, hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, VG.Proof.Scrypt.X86.Whole.rd_off,
    Mem.readW_writeW_self32]
/-- `cmp e, e'`, ending a block. -/
theorem cmp_ok {e e' : Reg} {u : State} {Q : State → Prop}
    (h : Q (VG.X86.arithFlags u (u.gpr e - u.gpr e') ((u.gpr e).toNat < (u.gpr e').toNat)
      (subOverflow (u.gpr e) (u.gpr e') (u.gpr e - u.gpr e')))) :
    WP isa (.block [.alu .cmp e (.reg e')]) u Q :=
  WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil h⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem → t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = L.b →
      Q t') :
    WP isa (.block cur0) t Q :=
  VG.Proof.Scrypt.X86.Whole.cp_ok hL hc 60 32 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => WP.block_nil (h t₁ hc₁ hf₁ (by
    simp only [Nat.reduceAdd] at hm₁; rw [hm₁, Mem.readW_writeW_self32, hc.kept.b]))

/-- The arguments of a call of ROMix on the block at `cur`, in the frame. -/
structure RomixArgs (L : VG.Proof.Scrypt.X86.Whole.Lay) (cur : BitVec 32) (m : Mem) : Prop where
  a0 : m.readW (L.A + BitVec.ofNat 64 80) 32 = cur
  a1 : m.readW (L.A + BitVec.ofNat 64 84) 32 = L.r
  a2 : m.readW (L.A + BitVec.ofNat 64 88) 32 = L.v
  a3 : m.readW (L.A + BitVec.ofNat 64 92) 32 = L.vlen
  a4 : m.readW (L.A + BitVec.ofNat 64 96) 32 = L.scr
  a5 : m.readW (L.A + BitVec.ofNat 64 100) 32 = L.r + 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {cur : BitVec 32}
    (hcur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur) {Q : State → Prop}
    (h : ∀ t', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem → VG.Proof.Scrypt.X86.Whole.RomixArgs L cur t'.mem →
      t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur → Q t') :
    WP isa (.block romixArgs) t Q := by
  unfold romixArgs
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc 32 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₁ 56 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₂ 68 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₃ 72 12 (by omega) (by omega) fun t₄ hc₄ hf₄ hm₄ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₄ 76 16 (by omega) (by omega) fun t₅ hc₅ hf₅ hm₅ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ld_ok hL hc₅ VG.Proof.Scrypt.X86.Whole.eax_cs 56 (by omega) (Same.refl t₅) fun u hu he _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.add_ok VG.Proof.Scrypt.X86.Whole.eax_cs hu rfl fun u' hu' he' _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.st_ok hL hc₅ 20 (by omega) hu' fun t₆ hc₆ hf₆ hm₆ _ => WP.block_nil ?_
  rw [he', he] at hm₆
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆
  rw [hcur] at hm₁; rw [hc₁.kept.r] at hm₂; rw [hc₂.kept.v] at hm₃; rw [hc₃.kept.vlen] at hm₄
  rw [hc₄.kept.scr] at hm₅; rw [hc₅.kept.r] at hm₆
  refine h t₆ hc₆ (VG.Proof.Scrypt.X86.Whole.frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    VG.Proof.Scrypt.X86.Whole.frame_trans hf₅ hf₆) ?_ ?_
  · constructor <;> simp (disch := decide) only [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, VG.Proof.Scrypt.X86.Whole.rd_off,
      Mem.readW_writeW_self32]
  · simp (disch := decide) only [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, VG.Proof.Scrypt.X86.Whole.rd_off, hcur]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      VG.Proof.Scrypt.X86.Whole.PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t'.mem → Q t') :
    WP isa (.block pbk2Args) t Q := by
  unfold pbk2Args
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc 40 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₁ 44 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₂ 60 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ld_ok hL hc₃ VG.Proof.Scrypt.X86.Whole.eax_cs 64 (by omega) (Same.refl t₃) fun u hu he _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ror_ok VG.Proof.Scrypt.X86.Whole.eax_cs hu fun u' hu' he' _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.st_ok hL hc₃ 12 (by omega) hu' fun t₄ hc₄ hf₄ hm₄ _ => ?_
  rw [he', he, hc₃.kept.blen, VG.Proof.Scrypt.X86.Whole.ror25 _ hL.blen25] at hm₄
  refine VG.Proof.Scrypt.X86.Whole.imm_ok VG.Proof.Scrypt.X86.Whole.eax_cs 1 (Same.refl t₄) fun u hu he _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.st_ok hL hc₄ 16 (by omega) hu fun t₅ hc₅ hf₅ hm₅ _ => ?_
  rw [he] at hm₅
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₅ 84 20 (by omega) (by omega) fun t₆ hc₆ hf₆ hm₆ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₆ 88 24 (by omega) (by omega) fun t₇ hc₇ hf₇ hm₇ => ?_
  refine VG.Proof.Scrypt.X86.Whole.cp_ok hL hc₇ 76 28 (by omega) (by omega) fun t₈ hc₈ hf₈ hm₈ => ?_
  refine WP.block_nil (h t₈ hc₈ (VG.Proof.Scrypt.X86.Whole.frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    VG.Proof.Scrypt.X86.Whole.frame_trans hf₅ <| frame_trans hf₆ <| frame_trans hf₇ hf₈) ?_)
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  rw [hc.kept.pw] at hm₁; rw [hc₁.kept.pwl] at hm₂; rw [hc₂.kept.b] at hm₃; rw [hc₅.kept.out] at hm₆
  rw [hc₆.kept.ol] at hm₇; rw [hc₇.kept.scr] at hm₈
  constructor <;> simp (disch := decide) only [hm₈, hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, VG.Proof.Scrypt.X86.Whole.rd_off,
    Mem.readW_writeW_self32]

theorem Ctx.flags {t : State} (hL : L.Ok) (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) (x : BitVec 32) (c o : Bool) :
    VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ (VG.X86.arithFlags t x c o) :=
  hc.store hL rfl rfl (fun _ _ => rfl) (Frame.refl _ _)

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {cur : BitVec 32}
    (hcur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur) {Q : State → Prop}
    (h : ∀ t', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur + BitVec.ofNat 32 (L.r.toNat * 128) →
      t'.zf = some (cur + BitVec.ofNat 32 (L.r.toNat * 128) -
        (BitVec.ofNat 32 (L.blen.toNat * 128) + L.b) == 0) → Q t') :
    WP isa (.block nextBlock) t Q := by
  unfold nextBlock
  refine VG.Proof.Scrypt.X86.Whole.ld_ok hL hc VG.Proof.Scrypt.X86.Whole.ecx_cs 56 (by omega) (Same.refl t) fun u₁ hu₁ e₁ _ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ror_ok VG.Proof.Scrypt.X86.Whole.ecx_cs hu₁ fun u₂ hu₂ e₂ k₂ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ld_ok hL hc VG.Proof.Scrypt.X86.Whole.eax_cs 32 (by omega) hu₂ fun u₃ hu₃ e₃ k₃ => ?_
  refine VG.Proof.Scrypt.X86.Whole.add_ok VG.Proof.Scrypt.X86.Whole.eax_cs hu₃ rfl fun u₄ hu₄ e₄ k₄ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ld_ok hL hc VG.Proof.Scrypt.X86.Whole.edx_cs 64 (by omega) hu₄ fun u₅ hu₅ e₅ k₅ => ?_
  refine VG.Proof.Scrypt.X86.Whole.ror_ok VG.Proof.Scrypt.X86.Whole.edx_cs hu₅ fun u₆ hu₆ e₆ k₆ => ?_
  refine VG.Proof.Scrypt.X86.Whole.add_ok VG.Proof.Scrypt.X86.Whole.edx_cs hu₆ (VG.Proof.Scrypt.X86.Whole.ld_eq hL hc 60 (by omega) hu₆) fun u₇ hu₇ e₇ k₇ => ?_
  refine VG.Proof.Scrypt.X86.Whole.st_ok hL hc 32 (by omega) hu₇ fun t₁ hc₁ hf₁ hm₁ k₈ => VG.Proof.Scrypt.X86.Whole.cmp_ok ?_
  have ecx : u₃.gpr .ecx = BitVec.ofNat 32 (L.r.toNat * 128) := by
    rw [k₃ _ (by decide), e₂, e₁, hc.kept.r, VG.Proof.Scrypt.X86.Whole.ror25 _ hL.r25]
  have eax : u₇.gpr .eax = cur + BitVec.ofNat 32 (L.r.toNat * 128) := by
    rw [k₇ _ (by decide), k₆ _ (by decide), k₅ _ (by decide), e₄, e₃, ecx]
    simp only [Nat.reduceAdd]; rw [hcur]
  have edx : u₇.gpr .edx = BitVec.ofNat 32 (L.blen.toNat * 128) + L.b := by
    rw [e₇, e₆, e₅, hc.kept.blen, VG.Proof.Scrypt.X86.Whole.ror25 _ hL.blen25]
    simp only [Nat.reduceAdd]; rw [hc.kept.b]
  refine h _ (hc₁.flags hL _ _ _) hf₁ ?_ ?_
  · simp only [RegUpd.mem_arithFlags, hm₁, Nat.reduceAdd, Mem.readW_writeW_self32, eax]
  · simp only [RegUpd.zf_arithFlags, k₈, eax, edx]

end

end VG.Proof.Scrypt.X86.Whole

end

section

/-!
# scrypt on x86 (32-bit): PBKDF2-HMAC-SHA256 as a callee

As on x86-64 (`Proof/Scrypt/X86_64/Whole/Pbkdf2.lean`):
`vg_pbkdf2_hmac_sha256_scratch` (any implementation of it) is verified against the
shared contract `VG.Spec.Hmac.sha256I.pbkdf2ScratchContract`; its caller works with
the same contract spelt out (`pbkG`, the contract its proof is written
against): `pbk_correct` and `pbk_ct` are its correctness and constant time
under `pbkG`, from its `Verified` proof.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG.X86
open VG.Proof.Pbkdf2.Whole.X86 (pbkG argVal32 setWidth32_64 toNat_setWidth64 setWidth_inj32)

/-- `pbkdf2`'s contract, spelt out. -/
abbrev pbkK : Contract isa := pbkG Spec.Hmac.sha256S 200

theorem pbk_pre {s : State} (h : pbkK.pre s) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, X86.abi]
  simp only [argVal32, setWidth32_64, toNat_setWidth64,
    show argBytes [32, 32, 32, 32, 32, 32, 32, 32] = 32 from rfl]
  simp only [VG.Proof.Scrypt.X86.Whole.pbkK, pbkG, Spec.Hmac.sha256S] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

theorem pbk_post {s s' : State} (h : (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76).post s s') :
    pbkK.post s s' := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86.abi] at h
  simp only [argVal32, setWidth32_64] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkK.pub s₁ s₂) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76).pub s₁ s₂ := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, X86.abi]
  simp only [argVal32]
  obtain ⟨e, h⟩ := h
  exact ⟨e, by rw [h 0 (by omega)], by rw [h 1 (by omega)], by rw [h 2 (by omega)],
    by rw [h 3 (by omega)], by rw [h 4 (by omega)], by rw [h 5 (by omega)],
    by rw [h 6 (by omega)], by rw [h 7 (by omega)]⟩

variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76))
include hv

theorem pbk_correct (s : State) (h : pbkK.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (VG.Proof.Scrypt.X86.Whole.pbk_pre h)
  exact ⟨t, s', he, ha, VG.Proof.Scrypt.X86.Whole.pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (VG.Proof.Scrypt.X86.Whole.pbk_pre h₁) (VG.Proof.Scrypt.X86.Whole.pbk_pre h₂) (VG.Proof.Scrypt.X86.Whole.pbk_pub hp) e₁ e₂

end VG.Proof.Scrypt.X86.Whole

end

/-!
# scrypt on x86 (32-bit): the calls

What a call of `vg_pbkdf2_hmac_sha256_scratch` (`pbk_call`) and of `vg_scrypt_romix`
(`romix_call`) from the frame does, from their arguments in the frame
(`PbkArgs`, `RomixArgs`): each keeps `Ctx`, and changes memory only in what it
writes and the 80 bytes below the frame (`call_ok`). `pbk_pre'` and
`romix_pre` are their preconditions, which the proof of constant time uses
too.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Whole.X86 (pbkG toNat_setWidth64)

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

/-- The return address of a call from the frame. -/
theorem e76 (B : BitVec 32) : B + BitVec.ofNat 32 80 - 4 = B + BitVec.ofNat 32 76 := by
  rw [show BitVec.ofNat 32 80 = BitVec.ofNat 32 76 + 4 from rfl, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem toNat_B (L : VG.Proof.Scrypt.X86.Whole.Lay) (hL : L.Ok) {k : Nat} (hk : k < 172) :
    (L.B + BitVec.ofNat 32 k).toNat = L.B.toNat + k := by
  have := hL.nB
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

section
variable {L : VG.Proof.Scrypt.X86.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) (hL : L.Ok)
include hc

theorem ce_esp (rd wr : List Region) : (t.callEntry.withRegions rd wr).gpr .esp = L.B + BitVec.ofNat 32 76 := by
  rw [State.withRegions_gpr, State.callEntry_esp, hc.esp, VG.Proof.Scrypt.X86.Whole.e76]

include hL

theorem ret_at : (t.gpr .esp - 4).setWidth 64 = L.A + BitVec.ofNat 64 76 := by
  rw [hc.esp, VG.Proof.Scrypt.X86.Whole.e76, VG.Proof.Scrypt.X86.Whole.addr_B (by have := hL.nB; omega)]

theorem ce_mem (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).mem = t.mem.writeW (L.A + BitVec.ofNat 64 76) (t.unknowns 0) := by
  rw [State.withRegions_mem, State.callEntry_mem, hc.ret_at hL]

/-- A word above the return address, on entry to the callee. -/
theorem ce_word (rd wr : List Region) {d : Nat} (h₁ : 80 ≤ d) (h₂ : d + 4 ≤ 172) :
    (t.callEntry.withRegions rd wr).mem.readW (L.A + BitVec.ofNat 64 d) 32 =
      t.mem.readW (L.A + BitVec.ofNat 64 d) 32 := by
  rw [hc.ce_mem hL]
  exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem ce_argAddr (rd wr : List Region) (i : Nat) (hi : i < 9) :
    argAddr (t.callEntry.withRegions rd wr) i = L.A + BitVec.ofNat 64 (80 + 4 * i) := by
  have := hL.nB
  rw [argAddr, hc.ce_esp, BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 76 + (4 + 4 * i) = 80 + 4 * i by omega,
    VG.Proof.Scrypt.X86.Whole.addr_B (by omega)]

theorem ce_arg (rd wr : List Region) (i : Nat) (hi : i < 9) :
    VG.X86.arg (t.callEntry.withRegions rd wr) i = t.mem.readW (L.A + BitVec.ofNat 64 (80 + 4 * i)) 32 := by
  rw [VG.X86.arg, hc.ce_argAddr hL rd wr i hi, hc.ce_word hL rd wr (by omega) (by omega)]

/-- The bytes of a region the return address of a call misses, on entry to the callee. -/
theorem ce_bytesAt (rd wr : List Region) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.A + BitVec.ofNat 64 76, 4⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt (t.callEntry.withRegions rd wr).mem p n = bytesAt t.mem p n := by
  rw [hc.ce_mem hL]
  exact Memory.frame_bytesAt (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
    (Region.contains_self _ _)) (by simpa using hd) hn

theorem ce_bytesAt' (rd wr : List Region) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.A + BitVec.ofNat 64 76, 4⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt (t.callEntry.withRegions rd wr).mem p n = Spec.Sha256.bytesAt t.mem p n :=
  hc.ce_bytesAt hL rd wr hd hn

end Ctx

theorem covers {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86.Whole.Within r R) (hwsub : ∀ r ∈ wr, VG.Proof.Scrypt.X86.Whole.InBuf L r ∨ VG.Proof.Scrypt.X86.Whole.Within r L.FR) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with (h | h | h | h) | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call of verified code (see `WP.call`), which uses at most 76 bytes of
stack and is given regions within ours to read, and within the writable
buffers or the frame to write: afterwards `Ctx` holds again, memory changed
only within what it writes and the 80 bytes below the frame, and the
callee's postcondition holds. -/
theorem call_ok (hL : L.Ok) {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hst : stackUse c ≤ 76) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86.Whole.Within r R) (hwsub : ∀ r ∈ wr, VG.Proof.Scrypt.X86.Whole.InBuf L r ∨ VG.Proof.Scrypt.X86.Whole.Within r L.FR)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ s' → Frame (wr ++ [⟨L.A, 80⟩]) t.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hnB := hL.nB
  have hesp : (t.gpr .esp).toNat = L.B.toNat + 80 := by rw [hc.esp, VG.Proof.Scrypt.X86.Whole.toNat_B L hL (by omega)]
  obtain ⟨hcov, hcovw⟩ := VG.Proof.Scrypt.X86.Whole.covers hc hsub hwsub
  refine WP.call hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf _ hpost => ?_
  have hb : Region.Sub (below (t.gpr .esp) (stackUse c + 4)) ⟨L.A, 80⟩ := by
    show Region.Sub ⟨(t.gpr .esp - BitVec.ofNat 32 (stackUse c + 4)).setWidth 64, _⟩ _
    rw [hc.esp, Offset.sub_ofNat_eq _ (show stackUse c + 4 ≤ 80 by omega), BitVec.add_sub_cancel,
      VG.Proof.Scrypt.X86.Whole.addr_B (by omega)]
    exact Offset.sub_base _ (by omega)
  have hf' : Frame (wr ++ [⟨L.A, 80⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hb⟩
  have hfs : Region.Sub L.FR L.STK := Offset.sub_base _ (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hc.kept.frame hf' fun R hR => ?_, hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hpost
  · rw [hcs .esp (by simp [calleeSaved]), hc.esp]
  · rcases List.mem_append.mp hR with hR | hR
    · rcases hwsub R hR with h | h
      · exact hL.args_in (by omega) (by omega) h
      · exact (Offset.disjoint _ (by omega) (by omega) (by omega)).sub_right h.sub
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · obtain ⟨R', hR', hs⟩ := h.sub
        rcases hR' with rfl | rfl | rfl | rfl
        · exact ⟨_, by simp, hs⟩
        · exact ⟨_, by simp, hs⟩
        · exact ⟨_, by simp, hs⟩
        · exact ⟨_, by simp, hs⟩
      · exact ⟨L.STK, by simp, VG.Proof.Scrypt.X86.Whole.sub_trans h.sub hfs⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Region.sub_prefix (by omega)⟩

/-- The return address of a call from the frame is in `STK`. -/
theorem ret_stk (L : VG.Proof.Scrypt.X86.Whole.Lay) : Region.Sub ⟨L.A + BitVec.ofNat 64 76, 4⟩ L.STK := Offset.sub_base _ (by omega)

namespace Lay.Ok

variable (hL : L.Ok)
include hL

theorem scr_in : VG.Proof.Scrypt.X86.Whole.InBuf L ⟨L.scr.setWidth 64, 200 * 8⟩ :=
  .inr (.inr (.inl (VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen17; omega))))

theorem stk_pw {d n : Nat} (h₁ : d + n ≤ 116) : Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ L.PW :=
  hL.kp.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-! ## PBKDF2 -/

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : VG.Proof.Scrypt.X86.Whole.Lay) (salt sl : BitVec 32) : List Region := [L.PW, ⟨salt.setWidth 64, sl.toNat⟩]
abbrev pbkWr (L : VG.Proof.Scrypt.X86.Whole.Lay) (out ol : BitVec 32) : List Region :=
  [⟨out.setWidth 64, ol.toNat⟩, ⟨L.scr.setWidth 64, 200 * 8⟩, ⟨L.A + BitVec.ofNat 64 80, 32⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : VG.Proof.Scrypt.X86.Whole.Lay) (salt sl out ol : BitVec 32) : Prop where
  sw : ∃ R ∈ L.regions, VG.Proof.Scrypt.X86.Whole.Within ⟨salt.setWidth 64, sl.toNat⟩ R
  ow : VG.Proof.Scrypt.X86.Whole.InBuf L ⟨out.setWidth 64, ol.toNat⟩
  so : Region.Disjoint ⟨salt.setWidth 64, sl.toNat⟩ ⟨out.setWidth 64, ol.toNat⟩
  sc : Region.Disjoint ⟨salt.setWidth 64, sl.toNat⟩ ⟨L.scr.setWidth 64, 200 * 8⟩
  oc : Region.Disjoint ⟨out.setWidth 64, ol.toNat⟩ ⟨L.scr.setWidth 64, 200 * 8⟩
  ks : L.STK.Disjoint ⟨salt.setWidth 64, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 32
  no : out.toNat + ol.toNat ≤ 2 ^ 32
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

/-- `A + 76 - 76`. -/
theorem stack76 (L : VG.Proof.Scrypt.X86.Whole.Lay) : L.A + BitVec.ofNat 64 76 - BitVec.ofNat 64 76 = L.A := BitVec.add_sub_cancel _ _

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : VG.Proof.Scrypt.X86.Whole.PbkArgs L salt sl out ol t.mem) (hr : VG.Proof.Scrypt.X86.Whole.PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol)) := by
  have hnB := hL.nB
  have a := hc.ce_arg hL (VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol)
  have ea := hc.ce_argAddr hL (VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol) 0 (by omega)
  have esp := hc.ce_esp (VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol)
  have e76 : (L.B + BitVec.ofNat 32 76).setWidth 64 = L.A + BitVec.ofNat 64 76 := VG.Proof.Scrypt.X86.Whole.addr_B (by omega)
  have sw := hL.scr_in
  simp only [VG.Proof.Scrypt.X86.Whole.pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr, a 0 (by omega),
    a 1 (by omega), a 2 (by omega), a 3 (by omega), a 4 (by omega), a 5 (by omega), a 6 (by omega),
    a 7 (by omega), Nat.reduceMul, Nat.reduceAdd, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6, ha.a7, ea,
    esp, e76, VG.Proof.Scrypt.X86.Whole.stack76, VG.Proof.Scrypt.X86.Whole.toNat_B L hL (show 76 < 172 by omega)]
  refine ⟨by omega, by omega, trivial, trivial, hL.pw_in hr.ow, hL.pw_in sw, (hL.stk_pw (by omega)).symm,
    hr.so, hr.sc, hr.ks.symm.sub_right (Offset.sub_base _ (by omega)), hr.oc,
    (hL.stk_in (d := 80) (n := 32) (by omega) hr.ow).symm,
    (hL.stk_in (d := 80) (n := 32) (by omega) sw).symm,
    hL.stk_pw (by omega), hr.ks.sub_left (VG.Proof.Scrypt.X86.Whole.ret_stk L),
    hL.stk_in (by omega) hr.ow, hL.stk_in (by omega) sw, Offset.disjoint _ (by omega) (by omega) (by omega),
    hL.kp.sub_left (Region.sub_prefix (by omega)), hr.ks.sub_left (Region.sub_prefix (by omega)),
    by simpa using hL.stk_in (d := 0) (n := 76) (by omega) hr.ow,
    by simpa using hL.stk_in (d := 0) (n := 76) (by omega) sw,
    Offset.base_disjoint _ (by omega) (by omega), hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt sl out ol : BitVec 32} (hr : VG.Proof.Scrypt.X86.Whole.PbkRegions L salt sl out ol) :
    ∀ r ∈ VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl ++ VG.Proof.Scrypt.X86.Whole.pbkWr L out ol, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86.Whole.Within r R := by
  simp only [VG.Proof.Scrypt.X86.Whole.pbkRd, VG.Proof.Scrypt.X86.Whole.pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _)⟩
  · obtain ⟨R, hR, hw⟩ := hr.sw
    exact ⟨R, by simpa using hR, hw⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen17; omega)⟩
  · exact ⟨L.FR, by simp, VG.Proof.Scrypt.X86.Whole.within_base _ (by omega)⟩

theorem pbk_wsub (hL : L.Ok) {out ol : BitVec 32} (hr : VG.Proof.Scrypt.X86.Whole.InBuf L ⟨out.setWidth 64, ol.toNat⟩) :
    ∀ r ∈ VG.Proof.Scrypt.X86.Whole.pbkWr L out ol, VG.Proof.Scrypt.X86.Whole.InBuf L r ∨ VG.Proof.Scrypt.X86.Whole.Within r L.FR := by
  simp only [VG.Proof.Scrypt.X86.Whole.pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl hr
  · exact .inl hL.scr_in
  · exact .inr (VG.Proof.Scrypt.X86.Whole.within_base _ (by omega))

theorem pbk_call {pbk : Prog isa}
    (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76))
    (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String) (hL : L.Ok) {t : State}
    (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : VG.Proof.Scrypt.X86.Whole.PbkArgs L salt sl out ol t.mem) (hr : VG.Proof.Scrypt.X86.Whole.PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧
      Frame (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol ++ [⟨L.A, 80⟩]) t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem (L.pw.setWidth 64) L.pwl.toNat)
        (bytesAt t.mem (salt.setWidth 64) sl.toNat) 1 ol.toNat =
        some (bytesAt t'.mem (out.setWidth 64) ol.toNat) := by
  have hnB := hL.nB
  refine VG.Proof.Scrypt.X86.Whole.call_ok hL (VG.Proof.Scrypt.X86.Whole.pbk_correct hv) hsp hst hc (VG.Proof.Scrypt.X86.Whole.pbk_pre' hL hc ha hr) (VG.Proof.Scrypt.X86.Whole.pbk_sub hL hr) (VG.Proof.Scrypt.X86.Whole.pbk_wsub hL hr.ow)
    fun s' hc' hf ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  have a := hc.ce_arg hL (VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol)
  have h := hpost
  simp only [VG.Proof.Scrypt.X86.Whole.pbkK, pbkG, Spec.Hmac.sha256S, hm, a 0 (by omega), a 1 (by omega), a 2 (by omega),
    a 3 (by omega), a 4 (by omega), a 5 (by omega), a 6 (by omega), Nat.reduceMul, Nat.reduceAdd, ha.a0,
    ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6] at h
  rw [hc.ce_bytesAt' hL _ _ (hL.stk_pw (by omega)).symm (by have := hL.np; omega),
    hc.ce_bytesAt' hL _ _ (hr.ks.sub_left (VG.Proof.Scrypt.X86.Whole.ret_stk L)).symm (by have := hr.ns; omega),
    show (1 : BitVec 32).toNat = 1 from rfl] at h
  exact h

/-! ## ROMix -/

/-- Block `i` of `b`. -/
abbrev blk (L : VG.Proof.Scrypt.X86.Whole.Lay) (i : Nat) : Addr := L.b.setWidth 64 + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- Its address, as a word. -/
abbrev cur (L : VG.Proof.Scrypt.X86.Whole.Lay) (i : Nat) : BitVec 32 := L.b + BitVec.ofNat 32 (128 * L.r.toNat * i)

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem cur_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) : (VG.Proof.Scrypt.X86.Whole.cur L i).setWidth 64 = VG.Proof.Scrypt.X86.Whole.blk L i := by
  have := VG.Proof.Scrypt.X86.Whole.blk_le hL hi; have := hL.nb; have := hL.rpos
  exact VG.Proof.Scrypt.X86.Whole.addr_B (by omega)

theorem toNat_cur (hL : L.Ok) {i : Nat} (hi : i < L.pp) : (VG.Proof.Scrypt.X86.Whole.cur L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
  have := VG.Proof.Scrypt.X86.Whole.blk_le hL hi; have := hL.nb; have := hL.rpos
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * L.r.toNat * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : VG.Proof.Scrypt.X86.Whole.InBuf L ⟨VG.Proof.Scrypt.X86.Whole.blk L i, L.r.toNat * 128⟩ :=
  .inl (VG.Proof.Scrypt.X86.Whole.within_off _ (VG.Proof.Scrypt.X86.Whole.blk_le hL hi))

/-- The regions a call of ROMix on block `i` reads and writes. -/
abbrev romixRd (L : VG.Proof.Scrypt.X86.Whole.Lay) : List Region := [⟨L.A + BitVec.ofNat 64 80, 24⟩]
abbrev romixWr (L : VG.Proof.Scrypt.X86.Whole.Lay) (i : Nat) : List Region :=
  [⟨VG.Proof.Scrypt.X86.Whole.blk L i, L.r.toNat * 128⟩, ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩,
    ⟨L.scr.setWidth 64, (L.r.toNat + 2) * 128⟩]

theorem r2 (hL : L.Ok) : (L.r + 2).toNat = L.r.toNat + 2 := by
  have := hL.r25
  rw [BitVec.toNat_add, show (2 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem stack36 (L : VG.Proof.Scrypt.X86.Whole.Lay) : L.A + BitVec.ofNat 64 76 - 36 = L.A + BitVec.ofNat 64 40 := by
  rw [show BitVec.ofNat 64 76 = BitVec.ofNat 64 40 + 36 from rfl, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem romix_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.X86.Whole.RomixArgs L (VG.Proof.Scrypt.X86.Whole.cur L i) t.mem) :
    Proof.Scrypt.roMixX86.pre (t.callEntry.withRegions (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i)) := by
  have hnB := hL.nB
  have hb := VG.Proof.Scrypt.X86.Whole.blk_in hL hi
  have hv : VG.Proof.Scrypt.X86.Whole.InBuf L ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩ := .inr (.inl (VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _)))
  have hs : VG.Proof.Scrypt.X86.Whole.InBuf L ⟨L.scr.setWidth 64, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen; omega))))
  have a := hc.ce_arg hL (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i)
  have ea := hc.ce_argAddr hL (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i) 0 (by omega)
  have esp := hc.ce_esp (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i)
  have e76 : (L.B + BitVec.ofNat 32 76).setWidth 64 = L.A + BitVec.ofNat 64 76 := VG.Proof.Scrypt.X86.Whole.addr_B (by omega)
  simp only [Proof.Scrypt.roMixX86, State.withRegions_rd, State.withRegions_wr, a 0 (by omega),
    a 1 (by omega), a 2 (by omega), a 3 (by omega), a 4 (by omega), a 5 (by omega), Nat.reduceMul,
    Nat.reduceAdd, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ea, esp, e76, VG.Proof.Scrypt.X86.Whole.stack36, VG.Proof.Scrypt.X86.Whole.r2 hL, VG.Proof.Scrypt.X86.Whole.cur_eq hL hi,
    VG.Proof.Scrypt.X86.Whole.toNat_cur hL hi, VG.Proof.Scrypt.X86.Whole.toNat_B L hL (show 76 < 172 by omega)]
  have kb := Within.sub (VG.Proof.Scrypt.X86.Whole.within_off (L.b.setWidth 64) (VG.Proof.Scrypt.X86.Whole.blk_le hL hi))
  have ks := Within.sub (VG.Proof.Scrypt.X86.Whole.within_base (L.scr.setWidth 64) (n := (L.r.toNat + 2) * 128)
    (k := L.slen.toNat * 128) (by have := hL.slen; omega))
  refine ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    hL.stk_in (by omega) hb, hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb,
    hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb, hL.stk_in (by omega) hv,
    hL.stk_in (by omega) hs, by have := VG.Proof.Scrypt.X86.Whole.blk_le hL hi; have := hL.nb; omega, hL.nv,
    by have := hL.nc; have := hL.slen; omega, by omega, by omega, hL.rpos, hL.vmod,
    Whole.valid_pow hL.valid, trivial⟩

theorem roMix_nosp : NoSp Impl.Scrypt.X86.roMix := NoSp.of_all (by lit_decide)

theorem roMix_stack : stackUse Impl.Scrypt.X86.roMix ≤ 76 := by lit_decide

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ VG.Proof.Scrypt.X86.Whole.romixRd L ++ VG.Proof.Scrypt.X86.Whole.romixWr L i, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86.Whole.Within r R := by
  simp only [VG.Proof.Scrypt.X86.Whole.romixRd, VG.Proof.Scrypt.X86.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, VG.Proof.Scrypt.X86.Whole.within_base _ (by omega)⟩
  · exact ⟨L.BB, by simp, VG.Proof.Scrypt.X86.Whole.within_off _ (VG.Proof.Scrypt.X86.Whole.blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen; omega)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ VG.Proof.Scrypt.X86.Whole.romixWr L i, VG.Proof.Scrypt.X86.Whole.InBuf L r ∨ VG.Proof.Scrypt.X86.Whole.Within r L.FR := by
  simp only [VG.Proof.Scrypt.X86.Whole.romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (VG.Proof.Scrypt.X86.Whole.blk_in hL hi)
  · exact .inl (.inr (.inl (VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _))))
  · exact .inl (.inr (.inr (.inl (VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen; omega)))))

theorem romix_call (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.X86.Whole.RomixArgs L (VG.Proof.Scrypt.X86.Whole.cur L i) t.mem) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧
      Frame (VG.Proof.Scrypt.X86.Whole.romixWr L i ++ [⟨L.A, 80⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (VG.Proof.Scrypt.X86.Whole.blk L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (VG.Proof.Scrypt.X86.Whole.blk L i) (128 * L.r.toNat)) := by
  have hb := VG.Proof.Scrypt.X86.Whole.blk_in hL hi
  refine VG.Proof.Scrypt.X86.Whole.call_ok hL RoMix.roMix_correct VG.Proof.Scrypt.X86.Whole.roMix_nosp VG.Proof.Scrypt.X86.Whole.roMix_stack hc (VG.Proof.Scrypt.X86.Whole.romix_pre hL hc hi ha)
    (VG.Proof.Scrypt.X86.Whole.romix_sub hL hi) (VG.Proof.Scrypt.X86.Whole.romix_wsub hL hi) fun s' hc' hf ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  have a := hc.ce_arg hL (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i)
  have h := hpost
  simp only [Proof.Scrypt.roMixX86, hm, a 0 (by omega), a 1 (by omega), a 3 (by omega), Nat.reduceMul,
    Nat.reduceAdd, ha.a0, ha.a1, ha.a3, VG.Proof.Scrypt.X86.Whole.cur_eq hL hi] at h
  rw [hc.ce_bytesAt hL _ _ (hL.stk_in (by omega) (by simpa [Nat.mul_comm] using hb)).symm
    (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86.Whole.blk_le hL hi; omega)] at h
  exact h

end

end VG.Proof.Scrypt.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86.Whole.Verified`. -/
section

section

/-!
# scrypt on x86 (32-bit): correctness

As on x86-64 (`Proof/Scrypt/X86_64/Whole/Correct.lean`): step 1 leaves the
blocks `X k` of `PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`);
the loop replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`);
step 3 derives the key from them (`step3_ok`). `scrypt_ok` puts the frame
around it (`push_ctx`), for any implementation `pbk` of PBKDF2 verified
against its shared contract that uses at most 76 bytes of stack.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)

variable {L : VG.Proof.Scrypt.X86.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem (L.pw.setWidth 64) L.pwl.toNat = bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega)

theorem salt_bytes :
    bytesAt t.mem (L.salt.setWidth 64) L.sl.toNat = bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : VG.Proof.Scrypt.X86.Whole.Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat)
    L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : VG.Proof.Scrypt.X86.Whole.Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
    (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) 1 (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : VG.Proof.Scrypt.X86.Whole.Step1 L m₀ (bytesAt m (L.b.setWidth 64) (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : VG.Proof.Scrypt.X86.Whole.X L m₀ k = bytesAt m (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) 1 (L.pp * 128 * L.r.toNat) =
      some (bytesAt m (L.b.setWidth 64) (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  rw [VG.Proof.Scrypt.X86.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := VG.Proof.Scrypt.X86.Whole.blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86.Whole.blk L k, 128 * L.r.toNat⟩ ⟨VG.Proof.Scrypt.X86.Whole.blk L i, L.r.toNat * 128⟩ := by
  have h₁ := VG.Proof.Scrypt.X86.Whole.blk_le hL hk
  have h₂ := VG.Proof.Scrypt.X86.Whole.blk_le hL hi
  have := hL.nb
  have hr := hL.rpos
  refine Offset.disjoint _ ?_ (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨VG.Proof.Scrypt.X86.Whole.blk L k, 128 * L.r.toNat⟩ L.BB := by
  have := VG.Proof.Scrypt.X86.Whole.blk_le' hL hk
  exact Offset.sub_base _ (by omega)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr.setWidth 64, 200 * 8⟩ L.SC :=
  Within.sub (VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen17; omega))

/-- A range in `b` misses the stack. -/
theorem b_stk (hL : L.Ok) {p : Addr} {n : Nat} (h : Region.Sub ⟨p, n⟩ L.BB) {d k : Nat} (hd : d + k ≤ 116) :
    Region.Disjoint ⟨p, n⟩ ⟨L.A + BitVec.ofNat 64 d, k⟩ :=
  (hL.kb.symm.sub_left h).sub_right (Offset.sub_base _ hd)

theorem toNat_blen (hL : L.Ok) : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL.blen_lt]

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hsp hst in
theorem pbk1_regions (hL : L.Ok) :
    VG.Proof.Scrypt.X86.Whole.PbkRegions L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) := by
  refine ⟨⟨L.SALT, by simp, VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _)⟩, ?_, ?_, hL.sc.sub_right (VG.Proof.Scrypt.X86.Whole.scr_sub hL), ?_, hL.ks,
    hL.ns, ?_, ?_⟩
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact .inl (VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _))
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.sb
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.bc.sub_right (VG.Proof.Scrypt.X86.Whole.scr_sub hL)
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.nb
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.ol1

theorem step1_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧
      VG.Proof.Scrypt.X86.Whole.Step1 L m₀ (bytesAt t'.mem (L.b.setWidth 64) (L.blen.toNat * 128)) := by
  refine WP.seq (VG.Proof.Scrypt.X86.Whole.pbk1Args_ok hL hc fun t₁ hc₁ _ ha₁ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86.Whole.pbk_call hv hsp hst name hL hc₁ ha₁ (VG.Proof.Scrypt.X86.Whole.pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
  exact hp

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : VG.Proof.Scrypt.X86.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = VG.Proof.Scrypt.X86.Whole.cur L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86.Whole.X L m₀ k) else VG.Proof.Scrypt.X86.Whole.X L m₀ k

abbrev Inv (L : VG.Proof.Scrypt.X86.Whole.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t ∧ VG.Proof.Scrypt.X86.Whole.InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : VG.Proof.Scrypt.X86.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = VG.Proof.Scrypt.X86.Whole.cur L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86.Whole.X L m₀ k) else VG.Proof.Scrypt.X86.Whole.X L m₀ k

theorem cur0' (L : VG.Proof.Scrypt.X86.Whole.Lay) : VG.Proof.Scrypt.X86.Whole.cur L 0 = L.b := by
  simp only [VG.Proof.Scrypt.X86.Whole.cur, Nat.mul_zero]; exact BitVec.add_zero _

/-- The bytes of a block, across a change of the frame. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) {m m' : Mem} (hf : Frame [L.FR] m m') :
    bytesAt m' (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) = bytesAt m (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) :=
  Memory.frame_bytesAt hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Scrypt.X86.Whole.b_stk hL (VG.Proof.Scrypt.X86.Whole.blk_sub hL hk) (by omega))
    (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86.Whole.blk_le hL hk; omega)

theorem start_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t)
    (h1 : VG.Proof.Scrypt.X86.Whole.Step1 L m₀ (bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128))) :
    WP isa (.block cur0) t (VG.Proof.Scrypt.X86.Whole.Inv L g m₀ 0) :=
  VG.Proof.Scrypt.X86.Whole.cur0_ok hL hc fun t' hc' hf hb => ⟨hc', hb.trans (VG.Proof.Scrypt.X86.Whole.cur0' L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [VG.Proof.Scrypt.X86.Whole.blk_fr hL hk hf, VG.Proof.Scrypt.X86.Whole.X_of hL h1 hk]⟩

theorem next_eq (L : VG.Proof.Scrypt.X86.Whole.Lay) (i : Nat) :
    VG.Proof.Scrypt.X86.Whole.cur L i + BitVec.ofNat 32 (L.r.toNat * 128) = VG.Proof.Scrypt.X86.Whole.cur L (i + 1) := by
  simp only [VG.Proof.Scrypt.X86.Whole.cur]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem beq32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem zf_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (VG.Proof.Scrypt.X86.Whole.cur L (i + 1) - (BitVec.ofNat 32 (L.blen.toNat * 128) + L.b) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := VG.Proof.Scrypt.X86.Whole.blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 32 := by
    rw [Nat.mul_succ]; omega
  rw [BitVec.add_comm (BitVec.ofNat 32 _) L.b]
  simp only [VG.Proof.Scrypt.X86.Whole.cur]
  rw [Offset.add_sub_add_left, ← hL.len_b, VG.Proof.Scrypt.X86.Whole.beq32 e₁ (by rw [hL.len_b]; exact hb)]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t)
    (hb : VG.Proof.Scrypt.X86.Whole.InvB L m₀ i t) (ha : VG.Proof.Scrypt.X86.Whole.RomixArgs L (VG.Proof.Scrypt.X86.Whole.cur L i) t.mem) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧ VG.Proof.Scrypt.X86.Whole.Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (VG.Proof.Scrypt.X86.Whole.romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (r := ⟨L.A + BitVec.ofNat 64 112, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [VG.Proof.Scrypt.X86.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega) (VG.Proof.Scrypt.X86.Whole.blk_in hL hi)
    · exact hL.stk_in (by omega) (.inr (.inl (VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega) (.inr (.inr (.inl (VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen; omega)))))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) = bytesAt t.mem (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [VG.Proof.Scrypt.X86.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact VG.Proof.Scrypt.X86.Whole.blk_disj hL hk hi hki
          · exact hL.bv.sub_left (VG.Proof.Scrypt.X86.Whole.blk_sub hL hk)
          · exact (hL.bc.sub_left (VG.Proof.Scrypt.X86.Whole.blk_sub hL hk)).sub_right
              (Within.sub (VG.Proof.Scrypt.X86.Whole.within_base _ (by have := hL.slen; omega)))
          · exact (hL.kb.symm.sub_left (VG.Proof.Scrypt.X86.Whole.blk_sub hL hk)).sub_right (Region.sub_prefix (by omega)))
          (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86.Whole.blk_le hL hk; omega)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega
        simp only [hlt, this, ite_false]

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : VG.Proof.Scrypt.X86.Whole.Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix)
      (.block nextBlock))) t fun t' => VG.Proof.Scrypt.X86.Whole.Inv L g m₀ (i + 1) t' ∧ t'.zf = some (decide (i + 1 = L.pp)) :=
  WP.seq (VG.Proof.Scrypt.X86.Whole.romixArgs_ok hL h.1 h.2.cur fun t₁ hc₁ hf₁ ha₁ hcur₁ =>
    WP.seq (WP.mono (VG.Proof.Scrypt.X86.Whole.call_step hL hi hc₁ ⟨hcur₁, fun k hk => by rw [VG.Proof.Scrypt.X86.Whole.blk_fr hL hk hf₁]; exact h.2.blks k hk⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => VG.Proof.Scrypt.X86.Whole.nextBlock_ok hL hc₂ hm₂.cur fun t₃ hc₃ hf₃ hb₃ hz₃ =>
        ⟨⟨hc₃, by rw [hb₃, VG.Proof.Scrypt.X86.Whole.next_eq], fun k hk => by rw [VG.Proof.Scrypt.X86.Whole.blk_fr hL hk hf₃]; exact hm₂.blks k hk⟩,
          by rw [hz₃, VG.Proof.Scrypt.X86.Whole.next_eq, VG.Proof.Scrypt.X86.Whole.zf_eq hL hi]⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.X86.Whole.Inv L g m₀ 0 t) : WP isa romixLoop t (VG.Proof.Scrypt.X86.Whole.Inv L g m₀ L.pp) :=
  count_loop hL.pp_pos (VG.Proof.Scrypt.X86.Whole.Inv L g m₀) (fun _ hi _ h => VG.Proof.Scrypt.X86.Whole.body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hsp hst in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.X86.Whole.Inv L g m₀ L.pp t) :
    bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86.Whole.X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hsp hst in
theorem pbk2_regions (hL : L.Ok) :
    VG.Proof.Scrypt.X86.Whole.PbkRegions L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol := by
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (VG.Proof.Scrypt.X86.Whole.scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact VG.Proof.Scrypt.X86.Whole.within_base _ (Nat.le_refl _)
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.bo
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.bc.sub_right (VG.Proof.Scrypt.X86.Whole.scr_sub hL)
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.kb
  · rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.X86.Whole.Inv L g m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86.Whole.X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem (L.out.setWidth 64) L.ol.toNat) := by
  refine WP.seq (VG.Proof.Scrypt.X86.Whole.pbk2Args_ok hL h.1 fun t₁ hc₁ hf₁ ha₁ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86.Whole.pbk_call hv hsp hst name hL hc₁ ha₁ (VG.Proof.Scrypt.X86.Whole.pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  have e : bytesAt t₁.mem (L.b.setWidth 64) (L.blen.toNat * 128) =
      bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128) :=
    Memory.frame_bytesAt hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Scrypt.X86.Whole.b_stk hL (fun _ h => h) (by omega))
      (by have := hL.blen_lt; omega)
  rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL, hc₁.pw_bytes hL, e, VG.Proof.Scrypt.X86.Whole.final_bytes' hL h] at hp
  exact hp

/-- The frame's body. -/
theorem body_scrypt_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) :
    WP isa (scryptBody name pbk) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧
      Spec.Scrypt.scrypt (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat)
        L.NN L.r.toNat L.pp L.ol.toNat = some (bytesAt t'.mem (L.out.setWidth 64) L.ol.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.Whole.step1_ok hv hsp hst name hL hc) fun t₁ ⟨hc₁, h1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.Whole.start_ok hL hc₁ h1) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.Whole.loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86.Whole.step3_ok hv hsp hst name hL h₃) fun t₄ ⟨hc₄, hp⟩ => ⟨hc₄, ?_⟩
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem (L.b.setWidth 64) (L.blen.toNat * 128))
    (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [VG.Proof.Scrypt.X86.Whole.X_of hL h1 hk, Whole.chunk_bytesAt _ _ (VG.Proof.Scrypt.X86.Whole.blk_le' hL hk)]

end

/-! ## The whole function -/

theorem sub36 (x : BitVec 32) : x - BitVec.ofNat 32 (4 * 9) = x - BitVec.ofNat 32 116 + BitVec.ofNat 32 80 := by
  rw [Offset.sub_ofNat_eq x (show 4 * 9 ≤ 116 by omega)]

theorem push_ctx {s : State} (h : Proof.Scrypt.scryptX86.pre s) :
    VG.Proof.Scrypt.X86.Whole.Ctx (VG.Proof.Scrypt.X86.Whole.lay s) s.gpr s.mem (pushed pushRs s) := by
  have h116 := h.1
  have h56 := h.2.1
  have hn : 4 * pushRs.length ≤ (s.gpr .esp).toNat := by show 4 * 9 ≤ _; omega
  have hL := VG.Proof.Scrypt.X86.Whole.lay_ok h
  have hnB := hL.nB
  have hf := pushed_frame (s := s) (rs := pushRs) (by decide) hn
  have hfr : below (s.gpr .esp) (4 * pushRs.length) = (VG.Proof.Scrypt.X86.Whole.lay s).FR := by
    show (⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 9)).setWidth 64, 36⟩ : Region) = _
    rw [VG.Proof.Scrypt.X86.Whole.sub36, show s.gpr .esp - BitVec.ofNat 32 116 = (VG.Proof.Scrypt.X86.Whole.lay s).B from rfl, VG.Proof.Scrypt.X86.Whole.addr_B (by omega)]
  rw [hfr] at hf
  have ha : ∀ i, i < 13 → (pushed pushRs s).mem.readW ((VG.Proof.Scrypt.X86.Whole.lay s).A + BitVec.ofNat 64 (120 + 4 * i)) 32 =
      arg s i := fun i hi => by
    have e : (VG.Proof.Scrypt.X86.Whole.lay s).A + BitVec.ofNat 64 (120 + 4 * i) = argAddr s i := by
      rw [Lay.A, ← VG.Proof.Scrypt.X86.Whole.addr_B (by rw [VG.Proof.Scrypt.X86.Whole.lay_B h116]; omega), argAddr]
      congr 1
      rw [show 120 + 4 * i = 116 + (4 + 4 * i) by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc]
      simp only [VG.Proof.Scrypt.X86.Whole.lay]; rw [BitVec.sub_add_cancel]
    rw [arg, ← e]
    refine hf.readW (r := ⟨(VG.Proof.Scrypt.X86.Whole.lay s).A + BitVec.ofNat 64 (120 + 4 * i), 4⟩) (Region.contains_self _ _)
      (fun R hR => ?_) (by decide)
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨by rw [pushed_rd, h.2.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    ⟨ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega), ha 5 (by omega),
      ha 6 (by omega), ha 7 (by omega), ha 8 (by omega), ha 9 (by omega), ha 11 (by omega),
      ha 12 (by omega)⟩, ?_⟩
  · rw [pushed_wr, hfr, h.2.2.2.1, ← VG.Proof.Scrypt.X86.Whole.lay_args h116 h56]; rfl
  · rw [pushed_esp]; show s.gpr .esp - BitVec.ofNat 32 (4 * 9) = _; rw [VG.Proof.Scrypt.X86.Whole.sub36]; rfl
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(VG.Proof.Scrypt.X86.Whole.lay s).STK, by simp, Offset.sub_base _ (by omega)⟩

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

theorem pop_esp (B : BitVec 32) : B + BitVec.ofNat 32 80 + BitVec.ofNat 32 (4 * 9) = B + BitVec.ofNat 32 116 := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hst in
theorem body_nosp : NoSp (scryptBody name pbk) := by
  have hb : ∀ is : List Instr, is.all (fun i => !Taint.clobbers i .esp) = true →
      ∀ i ∈ is, Taint.clobbers i .esp = false := fun is h i hi => by
    simpa using List.all_eq_true.mp h i hi
  intro i hi
  replace hi : i ∈ (pbk1Args ++ VG.instrs pbk) ++ (cur0 ++ ((romixArgs ++
      (VG.instrs Impl.Scrypt.X86.roMix ++ nextBlock)) ++ (pbk2Args ++ VG.instrs pbk))) := hi
  simp only [List.mem_append, or_assoc] at hi
  rcases hi with h | h | h | h | h | h | h | h
  · exact hb _ (by decide) i h
  · exact hsp i h
  · exact hb _ (by decide) i h
  · exact hb _ (by decide) i h
  · exact VG.Proof.Scrypt.X86.Whole.roMix_nosp i h
  · exact hb _ (by decide) i h
  · exact hb _ (by decide) i h
  · exact hsp i h

/-- `vg_scrypt` meets `scryptX86` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptX86.pre s) :
    ∃ t s', Exec isa (scrypt name pbk) s t s' ∧ abiPreserved s s' ∧ Proof.Scrypt.scryptX86.post s s' := by
  have hL := VG.Proof.Scrypt.X86.Whole.lay_ok h
  have hc := VG.Proof.Scrypt.X86.Whole.push_ctx h
  have hnB := hL.nB
  refine WP.frame (rs := pushRs) (r := .eax) (by decide) (by decide) (by decide)
    (by show 4 * 9 ≤ _; have := h.1; omega) (VG.Proof.Scrypt.X86.Whole.body_nosp hsp name)
    (WP.mono (VG.Proof.Scrypt.X86.Whole.body_scrypt_ok hv hsp hst name hL hc) fun u ⟨hu, ho⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩)
  · by_cases hr' : r = .esp
    · subst hr'
      rw [popped_esp, hu.esp, show pushRs.length = 9 from rfl, VG.Proof.Scrypt.X86.Whole.pop_esp, VG.Proof.Scrypt.X86.Whole.lay_esp]
    · rw [popped_gpr _ _ _ hr' (VG.Proof.Scrypt.X86.Whole.ne_cs hr (by decide)), hu.cs r hr hr']
  · rw [popped_mem]
    refine hu.frame.readW (r := (VG.Proof.Scrypt.X86.Whole.lay s).RET) ?_ ?_ (by decide)
    · rw [Lay.RET, VG.Proof.Scrypt.X86.Whole.lay_ret h.1 h.2.1]; exact Region.contains_self _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      exacts [hL.rb, hL.rv, hL.rc, hL.ro, Offset.disjoint_base _ (by omega) (by omega)]
  · simp only [Proof.Scrypt.scryptX86, popped_mem]
    exact ho

end

end VG.Proof.Scrypt.X86.Whole

end

section

/-!
# scrypt on x86 (32-bit): constant time, up to the indices `j`

As on x86-64 (`Proof/Scrypt/X86_64/Whole/CT.lean`): two runs whose public data
agree have the same layout, so between the frame's push and pop they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs), whatever their secrets, and the indices of all the scryptROMix
calls agree (`LeakEq`, from the contract's leakage). The blocks address only
the stack, from `esp` (the taint analysis); each call is of constant-time code
whose public data agree (`RelCT.call`): for PBKDF2 its arguments, for
scryptROMix also the indices of its block, which `LeakEq` gives (`leak_X`);
the loop's branch agrees since both runs count the same blocks.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : VG.Proof.Scrypt.X86.Whole.Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₁ (L.salt.setWidth 64) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₂ (L.salt.setWidth 64) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : VG.Proof.Scrypt.X86.Whole.Lay} {m₁ m₂ : Mem} (h : VG.Proof.Scrypt.X86.Whole.LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.X86.Whole.X L m₁ k) = roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.X86.Whole.X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₁ (L.salt.setWidth 64) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₂ (L.salt.setWidth 64) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  simp only [VG.Proof.Scrypt.X86.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env := VG.Proof.Scrypt.X86.Whole.Lay × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : VG.Proof.Scrypt.X86.Whole.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : VG.Proof.Scrypt.X86.Whole.Env, e.1.Ok ∧ VG.Proof.Scrypt.X86.Whole.LeakEq e.1 e.2.2.2.1 e.2.2.2.2 ∧ VG.Proof.Scrypt.X86.Whole.Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    VG.Proof.Scrypt.X86.Whole.Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Scrypt.X86.Whole.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Scrypt.X86.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.X86.Whole.Two Φ) c (VG.Proof.Scrypt.X86.Whole.Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem esp_two {L : VG.Proof.Scrypt.X86.Whole.Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : VG.Proof.Scrypt.X86.Whole.Ctx L g₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.X86.Whole.Ctx L g₂ m₂ t₂) : t₁.gpr .esp = t₂.gpr .esp :=
  c₁.esp.trans c₂.esp.symm

/-- A block whose addresses depend only on `esp`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : VG.Proof.Scrypt.X86.Whole.Lay → Mem → State → Prop}
    (h : ∃ hc, (VG.Taint.check taint (τr [.esp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : VG.Proof.Scrypt.X86.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.X86.Whole.Two Φ) (.block is) (VG.Proof.Scrypt.X86.Whole.Two Ψ) := by
  obtain ⟨_, h⟩ := h
  exact VG.Proof.Scrypt.X86.Whole.two_wp (RelCT.taint (A := taint) (τr [.esp])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Scrypt.X86.Whole.esp_two c₁ c₂) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : VG.Proof.Scrypt.X86.Whole.Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Scrypt.X86.Whole.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Scrypt.X86.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : VG.Proof.Scrypt.X86.Whole.Lay) t₁ t₂ g₁ g₂ m₁ m₂, L.Ok → VG.Proof.Scrypt.X86.Whole.LeakEq L m₁ m₂ → VG.Proof.Scrypt.X86.Whole.Ctx L g₁ m₁ t₁ → VG.Proof.Scrypt.X86.Whole.Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : VG.Proof.Scrypt.X86.Whole.Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86.Whole.Within r R)
    (hwsub : ∀ (L : VG.Proof.Scrypt.X86.Whole.Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, VG.Proof.Scrypt.X86.Whole.InBuf L r ∨ VG.Proof.Scrypt.X86.Whole.Within r L.FR)
    (hw : ∀ (L : VG.Proof.Scrypt.X86.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.X86.Whole.Two Φ) (.call n c) (VG.Proof.Scrypt.X86.Whole.Two Ψ) :=
  VG.Proof.Scrypt.X86.Whole.two_wp (RelCT.exists_ fun (e : VG.Proof.Scrypt.X86.Whole.Env) => RelCT.call hv hct (rd e.1) (wr e.1) (P := fun a b => e.1.Ok ∧
    VG.Proof.Scrypt.X86.Whole.LeakEq e.1 e.2.2.2.1 e.2.2.2.2 ∧ VG.Proof.Scrypt.X86.Whole.Ctx e.1 e.2.1 e.2.2.2.1 a ∧ VG.Proof.Scrypt.X86.Whole.Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧
    Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b) fun _ _ ⟨hL, hk, c₁, c₂, f₁, f₂⟩ =>
    ⟨hpre _ _ _ _ hL c₁ f₁, hpre _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, (VG.Proof.Scrypt.X86.Whole.covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)).1,
      (VG.Proof.Scrypt.X86.Whole.covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)).2,
      (VG.Proof.Scrypt.X86.Whole.covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)).1,
      (VG.Proof.Scrypt.X86.Whole.covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)).2, VG.Proof.Scrypt.X86.Whole.esp_two c₁ c₂⟩) hw

/-! ## The calls -/

theorem pbk_pub_two {L : VG.Proof.Scrypt.X86.Whole.Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (c₁ : VG.Proof.Scrypt.X86.Whole.Ctx L g₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.X86.Whole.Ctx L g₂ m₂ t₂) {salt sl out ol : BitVec 32}
    (a₁ : VG.Proof.Scrypt.X86.Whole.PbkArgs L salt sl out ol t₁.mem) (a₂ : VG.Proof.Scrypt.X86.Whole.PbkArgs L salt sl out ol t₂.mem) :
    pbkK.pub (t₁.callEntry.withRegions (VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol))
      (t₂.callEntry.withRegions (VG.Proof.Scrypt.X86.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86.Whole.pbkWr L out ol)) := by
  refine ⟨by rw [c₁.ce_esp, c₂.ce_esp], fun i hi => ?_⟩
  rw [c₁.ce_arg hL _ _ i (by omega), c₂.ce_arg hL _ _ i (by omega)]
  match i, hi with
  | 0, _ => exact a₁.a0.trans a₂.a0.symm
  | 1, _ => exact a₁.a1.trans a₂.a1.symm
  | 2, _ => exact a₁.a2.trans a₂.a2.symm
  | 3, _ => exact a₁.a3.trans a₂.a3.symm
  | 4, _ => exact a₁.a4.trans a₂.a4.symm
  | 5, _ => exact a₁.a5.trans a₂.a5.symm
  | 6, _ => exact a₁.a6.trans a₂.a6.symm
  | 7, _ => exact a₁.a7.trans a₂.a7.symm

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : VG.Proof.Scrypt.X86.Whole.Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Scrypt.X86.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86.Whole.blk L k) (128 * L.r.toNat) =
      if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86.Whole.X L m₀ k) else VG.Proof.Scrypt.X86.Whole.X L m₀ k) (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (VG.Proof.Scrypt.X86.Whole.blk L i) (128 * L.r.toNat) = VG.Proof.Scrypt.X86.Whole.X L m₀ i := by
  rw [hc.ce_bytesAt hL _ _ (hL.stk_in (by omega) (by simpa [Nat.mul_comm] using VG.Proof.Scrypt.X86.Whole.blk_in hL hi)).symm
    (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86.Whole.blk_le hL hi; omega), hb i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : VG.Proof.Scrypt.X86.Whole.Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (hk : VG.Proof.Scrypt.X86.Whole.LeakEq L m₁ m₂) (c₁ : VG.Proof.Scrypt.X86.Whole.Ctx L g₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.X86.Whole.Ctx L g₂ m₂ t₂) {i : Nat} (hi : i < L.pp)
    (b₁ : VG.Proof.Scrypt.X86.Whole.InvB L m₁ i t₁) (b₂ : VG.Proof.Scrypt.X86.Whole.InvB L m₂ i t₂) (a₁ : VG.Proof.Scrypt.X86.Whole.RomixArgs L (VG.Proof.Scrypt.X86.Whole.cur L i) t₁.mem)
    (a₂ : VG.Proof.Scrypt.X86.Whole.RomixArgs L (VG.Proof.Scrypt.X86.Whole.cur L i) t₂.mem) :
    Proof.Scrypt.roMixX86.pub (t₁.callEntry.withRegions (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i))
      (t₂.callEntry.withRegions (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i)) := by
  refine ⟨by rw [c₁.ce_esp, c₂.ce_esp], fun j hj => ?_, ?_⟩
  · rw [c₁.ce_arg hL _ _ j (by omega), c₂.ce_arg hL _ _ j (by omega)]
    match j, hj with
    | 0, _ => exact a₁.a0.trans a₂.a0.symm
    | 1, _ => exact a₁.a1.trans a₂.a1.symm
    | 2, _ => exact a₁.a2.trans a₂.a2.symm
    | 3, _ => exact a₁.a3.trans a₂.a3.symm
    | 4, _ => exact a₁.a4.trans a₂.a4.symm
    | 5, _ => exact a₁.a5.trans a₂.a5.symm
  · have a := c₁.ce_arg hL (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i)
    have a' := c₂.ce_arg hL (VG.Proof.Scrypt.X86.Whole.romixRd L) (VG.Proof.Scrypt.X86.Whole.romixWr L i)
    simp only [a 0 (by omega), a 1 (by omega), a 3 (by omega), a' 0 (by omega), a' 1 (by omega),
      a' 3 (by omega), Nat.reduceMul, Nat.reduceAdd, a₁.a0, a₁.a1, a₁.a3, a₂.a0, a₂.a1, a₂.a3, VG.Proof.Scrypt.X86.Whole.cur_eq hL hi,
      VG.Proof.Scrypt.X86.Whole.romix_bytes hL c₁ hi b₁.blks, VG.Proof.Scrypt.X86.Whole.romix_bytes hL c₂ hi b₂.blks]
    exact VG.Proof.Scrypt.X86.Whole.leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : VG.Proof.Scrypt.X86.Whole.Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86.Whole.InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (VG.Proof.Scrypt.X86.Whole.Two (VG.Proof.Scrypt.X86.Whole.LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.X86.roMix) (.block nextBlock)))
      (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two (VG.Proof.Scrypt.X86.Whole.LoopAt n)) (.block romixArgs) (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      VG.Proof.Scrypt.X86.Whole.InvB L m₀ (L.pp - n) t ∧ VG.Proof.Scrypt.X86.Whole.RomixArgs L (VG.Proof.Scrypt.X86.Whole.cur L (L.pp - n)) t.mem) :=
    VG.Proof.Scrypt.X86.Whole.two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc ⟨h0, hn, hb⟩ =>
      VG.Proof.Scrypt.X86.Whole.romixArgs_ok hL hc hb.cur fun _ hc' hf ha hcur => ⟨hc', h0, hn,
        ⟨hcur, fun k hk => by rw [VG.Proof.Scrypt.X86.Whole.blk_fr hL hk hf]; exact hb.blks k hk⟩, ha⟩
  have b : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86.Whole.InvB L m₀ (L.pp - n) t ∧
      VG.Proof.Scrypt.X86.Whole.RomixArgs L (VG.Proof.Scrypt.X86.Whole.cur L (L.pp - n)) t.mem) (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix)
      (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86.Whole.Mid L m₀ (L.pp - n) t) :=
    VG.Proof.Scrypt.X86.Whole.two_call RoMix.roMix_correct RoMix.roMix_ct (fun L => VG.Proof.Scrypt.X86.Whole.romixRd L) (fun L => VG.Proof.Scrypt.X86.Whole.romixWr L (L.pp - n))
      (fun _ _ _ _ hL hc ⟨h0, hn, _, ha⟩ => VG.Proof.Scrypt.X86.Whole.romix_pre hL hc (by omega) ha)
      (fun _ _ _ _ _ _ _ hL hk c₁ c₂ ⟨h0, hn, b₁, a₁⟩ ⟨_, _, b₂, a₂⟩ =>
        VG.Proof.Scrypt.X86.Whole.romix_pub_two hL hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ hL ⟨h0, hn, _⟩ => VG.Proof.Scrypt.X86.Whole.romix_sub hL (by omega))
      (fun _ _ _ hL ⟨h0, hn, _⟩ => VG.Proof.Scrypt.X86.Whole.romix_wsub hL (by omega))
      (fun _ _ _ _ hL hc ⟨h0, hn, hb, ha⟩ =>
        WP.mono (VG.Proof.Scrypt.X86.Whole.call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86.Whole.Mid L m₀ (L.pp - n) t) (.block nextBlock)
      (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) :=
    VG.Proof.Scrypt.X86.Whole.two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      VG.Proof.Scrypt.X86.Whole.nextBlock_ok hL hc hm.cur fun _ hc' hf hb hz => ⟨hc', h0, hn,
        ⟨by rw [hb, VG.Proof.Scrypt.X86.Whole.next_eq], fun k hk => by rw [VG.Proof.Scrypt.X86.Whole.blk_fr hL hk hf]; exact hm.blks k hk⟩,
        by rw [hz, VG.Proof.Scrypt.X86.Whole.next_eq, VG.Proof.Scrypt.X86.Whole.zf_eq hL (by omega)]⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86.Whole.InvB L m₀ 0 t) romixLoop (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86.Whole.InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86.Whole.InvB L m₀ L.pp t)
    (fun n => VG.Proof.Scrypt.X86.Whole.Two (VG.Proof.Scrypt.X86.Whole.LoopAt n)) (fun n => (VG.Proof.Scrypt.X86.Whole.body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨h0, hn, b₁, z₁⟩, ⟨-, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.1.pp - n + 1 = e.1.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show VG.Proof.Scrypt.X86.Whole.InvB e.1 _ e.1.pp a from hl ▸ b₁,
          show VG.Proof.Scrypt.X86.Whole.InvB e.1 _ e.1.pp b from hl ▸ b₂⟩
      · have hl : e.1.pp - n + 1 ≠ e.1.pp := by simpa using ht
        have e₁ : e.1.pp - (n - 1) = e.1.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, c₁, c₂, ⟨by omega, by omega, e₁ ▸ b₁⟩,
          ⟨by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, b₁, b₂⟩ => ⟨e.1.pp, e, hL, hk, c₁, c₂,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

theorem scryptBody_ct : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun _ _ _ => True) (scryptBody name pbk) fun _ _ => True := by
  have p1a : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun _ _ _ => True) (.block pbk1Args)
      (VG.Proof.Scrypt.X86.Whole.Two fun L _ t => VG.Proof.Scrypt.X86.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t.mem) :=
    VG.Proof.Scrypt.X86.Whole.two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc _ => VG.Proof.Scrypt.X86.Whole.pbk1Args_ok hL hc fun _ hc' _ ha => ⟨hc', ha⟩
  have p1c : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun L _ t => VG.Proof.Scrypt.X86.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t.mem)
      (.call name pbk) (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86.Whole.Step1 L m₀ (bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128))) :=
    VG.Proof.Scrypt.X86.Whole.two_call (VG.Proof.Scrypt.X86.Whole.pbk_correct hv) (VG.Proof.Scrypt.X86.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.X86.Whole.pbkRd L L.salt L.sl)
      (fun L => VG.Proof.Scrypt.X86.Whole.pbkWr L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
      (fun _ _ _ _ hL hc ha => VG.Proof.Scrypt.X86.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.X86.Whole.pbk1_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => VG.Proof.Scrypt.X86.Whole.pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => VG.Proof.Scrypt.X86.Whole.pbk_sub hL (VG.Proof.Scrypt.X86.Whole.pbk1_regions hL)) (fun _ _ _ hL _ => VG.Proof.Scrypt.X86.Whole.pbk_wsub hL (VG.Proof.Scrypt.X86.Whole.pbk1_regions hL).ow)
      (fun _ _ _ _ hL hc ha => WP.mono (VG.Proof.Scrypt.X86.Whole.pbk_call hv hsp hst name hL hc ha (VG.Proof.Scrypt.X86.Whole.pbk1_regions hL))
        fun _ ⟨hc', _, hp⟩ => ⟨hc', by rw [VG.Proof.Scrypt.X86.Whole.toNat_blen hL, hc.pw_bytes hL, hc.salt_bytes hL] at hp; exact hp⟩)
  have c0 : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86.Whole.Step1 L m₀ (bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128)))
      (.block cur0) (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86.Whole.InvB L m₀ 0 t) :=
    VG.Proof.Scrypt.X86.Whole.two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc h1 => VG.Proof.Scrypt.X86.Whole.start_ok hL hc h1
  have p2a : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86.Whole.InvB L m₀ L.pp t) (.block pbk2Args)
      (VG.Proof.Scrypt.X86.Whole.Two fun L _ t => VG.Proof.Scrypt.X86.Whole.PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t.mem) :=
    VG.Proof.Scrypt.X86.Whole.two_blk ⟨_, by taint_decide⟩ fun _ _ _ _ hL hc _ => VG.Proof.Scrypt.X86.Whole.pbk2Args_ok hL hc fun _ hc' _ ha => ⟨hc', ha⟩
  have p2c : RelCT isa (VG.Proof.Scrypt.X86.Whole.Two fun L _ t => VG.Proof.Scrypt.X86.Whole.PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t.mem)
      (.call name pbk) (VG.Proof.Scrypt.X86.Whole.Two fun _ _ _ => True) :=
    VG.Proof.Scrypt.X86.Whole.two_call (VG.Proof.Scrypt.X86.Whole.pbk_correct hv) (VG.Proof.Scrypt.X86.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.X86.Whole.pbkRd L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
      (fun L => VG.Proof.Scrypt.X86.Whole.pbkWr L L.out L.ol)
      (fun _ _ _ _ hL hc ha => VG.Proof.Scrypt.X86.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.X86.Whole.pbk2_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => VG.Proof.Scrypt.X86.Whole.pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => VG.Proof.Scrypt.X86.Whole.pbk_sub hL (VG.Proof.Scrypt.X86.Whole.pbk2_regions hL)) (fun _ _ _ hL _ => VG.Proof.Scrypt.X86.Whole.pbk_wsub hL (VG.Proof.Scrypt.X86.Whole.pbk2_regions hL).ow)
      (fun _ _ _ _ hL hc ha =>
        WP.mono (VG.Proof.Scrypt.X86.Whole.pbk_call hv hsp hst name hL hc ha (VG.Proof.Scrypt.X86.Whole.pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  exact ((p1a.seq p1c).seq (c0.seq (loop_ct.seq (p2a.seq p2c)))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptX86.pre Proof.Scrypt.scryptX86.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (VG.Proof.Scrypt.X86.Whole.scryptBody_ct hv hsp hst name) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp', ha, hlk⟩, rfl, rfl⟩
  have e : VG.Proof.Scrypt.X86.Whole.lay s₂ = VG.Proof.Scrypt.X86.Whole.lay s₁ := by
    simp only [VG.Proof.Scrypt.X86.Whole.lay, ← ha 0 (by omega), ← ha 1 (by omega), ← ha 2 (by omega), ← ha 3 (by omega),
      ← ha 4 (by omega), ← ha 5 (by omega), ← ha 6 (by omega), ← ha 7 (by omega), ← ha 8 (by omega),
      ← ha 9 (by omega), ← ha 10 (by omega), ← ha 11 (by omega), ← ha 12 (by omega), hsp']
  refine ⟨⟨VG.Proof.Scrypt.X86.Whole.lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, VG.Proof.Scrypt.X86.Whole.lay_ok h₁, ?_, VG.Proof.Scrypt.X86.Whole.push_ctx h₁, e ▸ VG.Proof.Scrypt.X86.Whole.push_ctx h₂,
    trivial, trivial⟩
  rw [← ha 0 (by omega), ← ha 1 (by omega), ← ha 2 (by omega), ← ha 3 (by omega), ← ha 4 (by omega),
    ← ha 6 (by omega), ← ha 8 (by omega)] at hlk
  exact hlk

end

end VG.Proof.Scrypt.X86.Whole

end

/-!
# scrypt on x86 (32-bit): the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract that never writes `esp` and uses at most 76 bytes of
stack, is verified against `Spec.Scrypt.scryptContract` for the 116 bytes of
stack its frame and calls use (`scrypt_verified_of`); and so is the one
calling the `vg_pbkdf2_hmac_sha256_scratch` made with any SHA-256 backend
(`scrypt_verified`), whose code never writes `esp` but by the frame
(`scrypt_spSafe`).
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Proof.Pbkdf2.Whole.X86 (argVal32 setWidth32_64 toNat_setWidth64 setWidth_inj32)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- Memory holding the arguments `0x1000, 0, 0x1100, 0, 1, 0x3000, 1, 0x4000, 2, 0x5000, 17, 0x6000, 1`
at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x800D then 0x11 else if a = 0x8014 then 1 else
  if a = 0x8019 then 0x30 else if a = 0x801C then 1 else if a = 0x8021 then 0x40 else
  if a = 0x8024 then 2 else if a = 0x8029 then 0x50 else if a = 0x802C then 17 else
  if a = 0x8031 then 0x60 else if a = 0x8034 then 1 else 0

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Scrypt.X86.Whole.satMem
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩]
  wr := [⟨0x3000, 128⟩, ⟨0x4000, 256⟩, ⟨0x5000, 2176⟩, ⟨0x6000, 1⟩, ⟨0x8004, 52⟩]

theorem scrypt_implies : Proof.Scrypt.scryptX86.Implies (Spec.Scrypt.scryptContract X86.abi 116) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi] at h
        simp only [argVal32, setWidth32_64, toNat_setWidth64,
          show argBytes [32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32] = 52 from rfl] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi]
        simp only [argVal32, setWidth32_64]
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi] at h
        simp only [argVal32] at h
        obtain ⟨e, hlk, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
        refine ⟨e, fun i hi => ?_, ?_⟩
        · match i, hi with
          | 0, _ => exact setWidth_inj32 a0
          | 1, _ => exact setWidth_inj32 a1
          | 2, _ => exact setWidth_inj32 a2
          | 3, _ => exact setWidth_inj32 a3
          | 4, _ => exact setWidth_inj32 a4
          | 5, _ => exact setWidth_inj32 a5
          | 6, _ => exact setWidth_inj32 a6
          | 7, _ => exact setWidth_inj32 a7
          | 8, _ => exact setWidth_inj32 a8
          | 9, _ => exact setWidth_inj32 a9
          | 10, _ => exact setWidth_inj32 a10
          | 11, _ => exact setWidth_inj32 a11
          | 12, _ => exact setWidth_inj32 a12
        · simpa only [setWidth32_64, List.flatMap_def] using hlk
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes] [satState, satMem] using VG.Proof.Scrypt.X86.Whole.satState }

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified X86.target (scrypt name pbk) (Spec.Scrypt.scryptContract X86.abi 116) :=
  Verified.of_correct (fun _ h => VG.Proof.Scrypt.X86.Whole.scrypt_ok hv hsp hst name h) (VG.Proof.Scrypt.X86.Whole.scrypt_ct hv hsp hst name) VG.Proof.Scrypt.X86.Whole.scrypt_implies

end

/-! ## With the PBKDF2 made with a SHA-256 backend -/

variable (v : Backend)

/-- PBKDF2-HMAC-SHA256 made with `v`. -/
abbrev pbkOf : Prog isa := v.F.pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2ScratchApi.name ++ v.suffix

/-- `vg_scrypt` made with `v`. -/
theorem scrypt_verified :
    Verified X86.target (scrypt (VG.Proof.Scrypt.X86.Whole.pbkName v) (VG.Proof.Scrypt.X86.Whole.pbkOf v)) (Spec.Scrypt.scryptContract X86.abi 116) :=
  VG.Proof.Scrypt.X86.Whole.scrypt_verified_of (Proof.Pbkdf2.Whole.X86.sha256_verified v) (Proof.Pbkdf2.Whole.X86.nosp_of_all v.pbkdf2Sp)
    (Proof.Pbkdf2.Whole.X86.sha256_stack v) _

/-- No instruction writes `esp` but the frame's push and pop. -/
theorem scrypt_spSafe : (scrypt (VG.Proof.Scrypt.X86.Whole.pbkName v) (VG.Proof.Scrypt.X86.Whole.pbkOf v)).all (fun i => !isa.writesSp i) = true := by
  have hr : Impl.Scrypt.X86.roMix.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  simp only [VG.Proof.Scrypt.X86.Whole.pbkOf, scrypt, scryptBody, pbkCall, romixLoop, Code.all, v.pbkdf2Sp, hr, Bool.and_true,
    Bool.true_and]
  decide

end VG.Proof.Scrypt.X86.Whole

end
