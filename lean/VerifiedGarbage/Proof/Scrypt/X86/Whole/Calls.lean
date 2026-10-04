import VerifiedGarbage.Proof.Scrypt.X86.RoMixCT
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Impl.Scrypt.X86.Scrypt
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract

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
    let r := (arg s 4).toNat
    let pwR : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let saltR : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let bR : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 128⟩
    let vR : Region := ⟨(arg s 7).setWidth 64, (arg s 8).toNat * 128⟩
    let scR : Region := ⟨(arg s 9).setWidth 64, (arg s 10).toNat * 128⟩
    let outR : Region := ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩
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
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + (arg s 6).toNat * 128 ≤ 2 ^ 32 ∧ (arg s 7).toNat + (arg s 8).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 9).toNat + (arg s 10).toNat * 128 ≤ 2 ^ 32 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32 ∧
    0 < r ∧ (arg s 6).toNat % r = 0 ∧ (arg s 8).toNat % r = 0 ∧
    Spec.Scrypt.valid ((arg s 8).toNat / r) r ((arg s 6).toNat / r) (arg s 12).toNat ∧
    (arg s 12).toNat ≤ (2 ^ 32 - 1) * 32 ∧ (arg s 10).toNat = r + 16
  post s s' :=
    let r := (arg s 4).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
      (Spec.Scrypt.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) ((arg s 8).toNat / r) r
      ((arg s 6).toNat / r) (arg s 12).toNat =
      some (Spec.Scrypt.bytesAt s'.mem ((arg s 11).setWidth 64) (arg s 12).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 13, arg s₁ i = arg s₂ i) ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem ((arg s₁ 0).setWidth 64) (arg s₁ 1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem ((arg s₁ 2).setWidth 64) (arg s₁ 3).toNat) (arg s₁ 4).toNat
        ((arg s₁ 6).toNat / (arg s₁ 4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (arg s₁ 4).toNat ((arg s₁ 8).toNat / (arg s₁ 4).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem ((arg s₂ 0).setWidth 64) (arg s₂ 1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem ((arg s₂ 2).setWidth 64) (arg s₂ 3).toNat) (arg s₂ 4).toNat
        ((arg s₂ 6).toNat / (arg s₂ 4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (arg s₂ 4).toNat ((arg s₂ 8).toNat / (arg s₂ 4).toNat))

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

variable (L : Lay)

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
def InBuf (L : Lay) (r : Region) : Prop :=
  Within r L.BB ∨ Within r L.VV ∨ Within r L.SC ∨ Within r L.OUT

theorem InBuf.sub {L : Lay} {r : Region} (h : InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

omit h in
theorem toNat_A : L.A.toNat = L.B.toNat := toNat_setWidth64 _

/-- `[esp + d]` in the frame. -/
theorem ea_sp {d : Nat} (hd : d + 4 ≤ 92) :
    (L.B + BitVec.ofNat 32 80 + BitVec.ofNat 32 d).setWidth 64 = L.A + BitVec.ofNat 64 (80 + d) := by
  have := h.nB
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, addr_B (by omega)]

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_in {d n : Nat} (h₁ : d + n ≤ 116) {r : Region} (hr : InBuf L r) :
    Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.A + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  obtain ⟨R, hR, hsr⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hsr
  · exact (h.kv.sub_left hs).sub_right hsr
  · exact (h.kc.sub_left hs).sub_right hsr
  · exact (h.ko.sub_left hs).sub_right hsr

/-- A range in our arguments is disjoint from one in a writable buffer. -/
theorem args_in {d n : Nat} (h₁ : 120 ≤ d) (h₂ : d + n ≤ 172) {r : Region} (hr : InBuf L r) :
    Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.A + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  obtain ⟨R, hR, hsr⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hsr
  · exact (h.va.symm.sub_left hs).sub_right hsr
  · exact (h.ca.symm.sub_left hs).sub_right hsr
  · exact (h.oa.symm.sub_left hs).sub_right hsr

/-- The password misses every writable buffer. -/
theorem pw_in {r : Region} (hr : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.pb.sub_right hs, h.pv.sub_right hs, h.pc.sub_right hs, h.po.sub_right hs]

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

end Lay.Ok

/-! ## What the calls cannot change -/

/-- Our arguments, the words from `A + 120` (`[esp + 40]` in the frame). -/
structure Kept (L : Lay) (m : Mem) : Prop where
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
theorem Kept.frame {L : Lay} {m m' : Mem} {rs : List Region} (hk : Kept L m) (hf : Frame rs m m')
    (hd : ∀ R ∈ rs, L.ARGS.Disjoint R) : Kept L m' := by
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
structure Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT, L.ARGS]
  esp : t.gpr .esp = L.B + BitVec.ofNat 32 80
  cs : ∀ r ∈ calleeSaved, r ≠ .esp → t.gpr r = g r
  kept : Kept L t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6, arg s 7, arg s 8, arg s 9, arg s 10,
    arg s 11, arg s 12, s.gpr .esp - BitVec.ofNat 32 116⟩

theorem lay_esp (s : State) :
    (lay s).B + BitVec.ofNat 32 116 = s.gpr .esp := BitVec.sub_add_cancel _ _

theorem lay_B {s : State} (h : 116 ≤ (s.gpr .esp).toNat) : (lay s).B.toNat = (s.gpr .esp).toNat - 116 :=
  sub_toNat h

theorem lay_args {s : State} (h : 116 ≤ (s.gpr .esp).toNat) (h' : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (lay s).A + BitVec.ofNat 64 120 = argAddr s 0 := by
  rw [Lay.A, ← addr_B (by rw [lay_B h]; omega)]
  simp only [lay, argAddr]
  congr 1
  bv_omega

theorem lay_ret {s : State} (h : 116 ≤ (s.gpr .esp).toNat) (h' : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (lay s).A + BitVec.ofNat 64 116 = (s.gpr .esp).setWidth 64 := by
  rw [Lay.A, ← addr_B (by rw [lay_B h]; omega), lay_esp s]

theorem lay_stk {s : State} (h : 116 ≤ (s.gpr .esp).toNat) :
    (lay s).A = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116 := by
  apply BitVec.eq_of_toNat_eq
  have := (s.gpr .esp).isLt
  rw [Lay.A, toNat_setWidth64, lay_B h, Offset.toNat_sub_ofNat, toNat_setWidth64]
  omega

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptX86.pre s) : (lay s).Ok := by
  obtain ⟨h116, h56, -, -, pb, pv, pc, po, pa, sb, sv, sc, so, sa, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    rp, rs, rb, rv, rc, ro, -, kp, ks, kb, kv, kc, ko, -, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval,
    olb, slen⟩ := h
  have ea : (lay s).ARGS = ⟨argAddr s 0, 52⟩ := by simp only [Lay.ARGS, lay_args h116 h56]
  have er : (lay s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by simp only [Lay.RET, lay_ret h116 h56]
  have ek : (lay s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116, 116⟩ := by
    simp only [Lay.STK, lay_stk h116]
  exact ⟨pb, pv, pc, po, ea ▸ pa, sb, sv, sc, so, ea ▸ sa, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co,
    ea ▸ ca, ea ▸ oa, er ▸ rp, er ▸ rs, er ▸ rb, er ▸ rv, er ▸ rc, er ▸ ro, ek ▸ kp, ek ▸ ks, ek ▸ kb,
    ek ▸ kv, ek ▸ kc, ek ▸ ko, np, ns, nb, nv, nc, no, by rw [lay_B h116]; omega, rpos, bmod, vmod, hval,
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

variable {L : Lay} (h : L.Ok)
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
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

namespace Ctx

variable {t t' : State} (hc : Ctx L g m₀ t)
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
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) (hf : Frame [L.FR] t.mem t'.mem) : Ctx L g m₀ t' := by
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
structure PbkArgs (L : Lay) (salt sl out ol : BitVec 32) (m : Mem) : Prop where
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

theorem Same.refl (t : State) : Same t t := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem Same.esp {t u : State} (h : Same t u) : u.gpr .esp = t.gpr .esp := h.cs .esp (by simp [calleeSaved])

theorem Same.setReg {t u : State} (h : Same t u) {r : Reg} (hr : r ∉ calleeSaved) (v : BitVec 32) :
    Same t (u.setReg r v) :=
  ⟨h.rd, h.wr, fun r' hr' => by
    rw [RegUpd.gpr_setReg]; split
    · subst r'; exact absurd hr' hr
    · exact h.cs r' hr', h.mem⟩

theorem Same.setFlags {t u : State} (h : Same t u) (a b c d : Option Bool) : Same t (u.setFlags a b c d) :=
  ⟨h.rd, h.wr, h.cs, h.mem⟩

theorem Same.arithFlags {t u : State} (h : Same t u) (x : BitVec 32) (c o : Bool) :
    Same t (VG.X86.arithFlags u x c o) := ⟨h.rd, h.wr, h.cs, h.mem⟩

theorem eax_cs : Reg.eax ∉ calleeSaved := by decide
theorem ecx_cs : Reg.ecx ∉ calleeSaved := by decide
theorem edx_cs : Reg.edx ∉ calleeSaved := by decide

/-- A step of a block, from a state `Same` as `t`. -/
def Step (t : State) (P : State → Prop) (is : List Instr) (Q : State → Prop) : Prop :=
  ∀ u, Same t u → P u → WP isa (.block is) u Q

/-- A load of `[esp + a]`, a word of the frame or of our arguments. -/
theorem ld_eq (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (a : Nat) (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92)
    {u : State} (hu : Same t u) :
    readSrc u (.mem (sp a)) = some (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32) := by
  have hin : InRegions (u.rd ++ u.wr) (L.A + BitVec.ofNat 64 (80 + a)) 4 := by
    rw [hu.rd, hu.wr]
    rcases ha with ha | ha
    · exact hc.inFr hL _ (by omega) (by omega)
    · exact hc.inArgs hL _ (by omega) (by omega)
  simp only [readSrc, State.load32, ea_esp, hu.esp, hc.esp, hL.ea_sp (d := a) (by omega), hin, ↓reduceIte,
    hu.mem]

/-- `mov e, [esp + a]`. -/
theorem ld_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {e : Reg} (he : e ∉ calleeSaved) (a : Nat)
    (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92) {is : List Instr} {Q : State → Prop} {u : State}
    (hu : Same t u)
    (h : ∀ u', Same t u' → u'.gpr e = t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32 →
      (∀ r, r ≠ e → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) :
    WP isa (.block (.mov e (.mem (sp a)) :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ (hu.setReg he (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32))
    (RegUpd.gpr_setReg_self _ _ _) fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩
  simp only [exec, ld_eq hL hc a ha hu, Option.map_some]

/-- `mov e, imm`. -/
theorem imm_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) (x : BitVec 32) {is : List Instr}
    {Q : State → Prop} {u : State} (hu : Same t u)
    (h : ∀ u', Same t u' → u'.gpr e = x → (∀ r, r ≠ e → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) :
    WP isa (.block (.mov e (.imm x) :: is)) u Q :=
  WP.block_cons_iff.mpr ⟨_, rfl, h _ (hu.setReg he _) (RegUpd.gpr_setReg_self _ _ _)
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `ror e, 25`: times 128. -/
theorem ror_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) {is : List Instr}
    {Q : State → Prop} {u : State} (hu : Same t u)
    (h : ∀ u', Same t u' → u'.gpr e = (u.gpr e).rotateRight 25 → (∀ r, r ≠ e → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) :
    WP isa (.block (times128 e :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ ((hu.setFlags (some ((u.gpr e).rotateRight 25).msb) none u.zf u.sf).setReg
    he _) (RegUpd.gpr_setReg_self _ _ _) fun _ hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]⟩
  simp only [exec, execShift]
  rfl

/-- `add e, src`. -/
theorem add_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) {src : Src} {x : BitVec 32}
    {is : List Instr} {Q : State → Prop} {u : State} (hu : Same t u) (hx : readSrc u src = some x)
    (h : ∀ u', Same t u' → u'.gpr e = u.gpr e + x → (∀ r, r ≠ e → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) :
    WP isa (.block (.alu .add e src :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ ((hu.arithFlags (u.gpr e + x) (2 ^ 32 ≤ (u.gpr e).toNat + x.toNat)
    (addOverflow (u.gpr e) x (u.gpr e + x))).setReg he _) (RegUpd.gpr_setReg_self _ _ _)
    fun _ hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]⟩
  simp only [exec, execAlu, hx, Option.bind_some]

/-- `mov [esp + d], eax`, a word of the frame, ending a step. -/
theorem st_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (d : Nat) (hd : d + 4 ≤ 36) {u : State}
    (hu : Same t u) {is : List Instr} {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
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
  simp only [exec, State.store32, ea_esp, hu.esp, hc.esp, hL.ea_sp (d := d) (by omega), hin, ↓reduceIte]

/-- A word copied from `[esp + a]` to `[esp + d]`. -/
theorem cp_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (a d : Nat)
    (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92) (hd : d + 4 ≤ 36) {is : List Instr} {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem = t.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32) →
      WP isa (.block is) t' Q) :
    WP isa (.block (.mov .eax (.mem (sp a)) :: .store (sp d) .eax :: is)) t Q :=
  ld_ok hL hc eax_cs a ha (Same.refl t) fun _ hu he _ =>
    st_ok hL hc d hd hu fun t' hc' hf hm _ => h t' hc' hf (he ▸ hm)

theorem frame_trans {t₁ t₂ t₃ : State} (h₁ : Frame [L.FR] t₁.mem t₂.mem) (h₂ : Frame [L.FR] t₂.mem t₃.mem) :
    Frame [L.FR] t₁.mem t₃.mem := h₁.trans h₂

theorem pbk1Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t'.mem → Q t') :
    WP isa (.block pbk1Args) t Q := by
  unfold pbk1Args
  refine cp_ok hL hc 40 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine cp_ok hL hc₁ 44 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine cp_ok hL hc₂ 48 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine cp_ok hL hc₃ 52 12 (by omega) (by omega) fun t₄ hc₄ hf₄ hm₄ => ?_
  refine imm_ok eax_cs 1 (Same.refl t₄) fun u hu he _ => ?_
  refine st_ok hL hc₄ 16 (by omega) hu fun t₅ hc₅ hf₅ hm₅ _ => ?_
  rw [he] at hm₅
  refine cp_ok hL hc₅ 60 20 (by omega) (by omega) fun t₆ hc₆ hf₆ hm₆ => ?_
  refine ld_ok hL hc₆ eax_cs 64 (by omega) (Same.refl t₆) fun u hu he _ => ?_
  refine ror_ok eax_cs hu fun u' hu' he' _ => ?_
  refine st_ok hL hc₆ 24 (by omega) hu' fun t₇ hc₇ hf₇ hm₇ _ => ?_
  rw [he', he, hc₆.kept.blen, ror25 _ hL.blen25] at hm₇
  refine cp_ok hL hc₇ 76 28 (by omega) (by omega) fun t₈ hc₈ hf₈ hm₈ => ?_
  refine WP.block_nil (h t₈ hc₈ (frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    frame_trans hf₅ <| frame_trans hf₆ <| frame_trans hf₇ hf₈) ?_)
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  rw [hc.kept.pw] at hm₁; rw [hc₁.kept.pwl] at hm₂; rw [hc₂.kept.salt] at hm₃; rw [hc₃.kept.sl] at hm₄
  rw [hc₅.kept.b] at hm₆; rw [hc₇.kept.scr] at hm₈
  constructor <;> simp (disch := decide) only [hm₈, hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off,
    Mem.readW_writeW_self32]
/-- `cmp e, e'`, ending a block. -/
theorem cmp_ok {e e' : Reg} {u : State} {Q : State → Prop}
    (h : Q (VG.X86.arithFlags u (u.gpr e - u.gpr e') ((u.gpr e).toNat < (u.gpr e').toNat)
      (subOverflow (u.gpr e) (u.gpr e') (u.gpr e - u.gpr e')))) :
    WP isa (.block [.alu .cmp e (.reg e')]) u Q :=
  WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil h⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem → t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = L.b →
      Q t') :
    WP isa (.block cur0) t Q :=
  cp_ok hL hc 60 32 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => WP.block_nil (h t₁ hc₁ hf₁ (by
    simp only [Nat.reduceAdd] at hm₁; rw [hm₁, Mem.readW_writeW_self32, hc.kept.b]))

/-- The arguments of a call of ROMix on the block at `cur`, in the frame. -/
structure RomixArgs (L : Lay) (cur : BitVec 32) (m : Mem) : Prop where
  a0 : m.readW (L.A + BitVec.ofNat 64 80) 32 = cur
  a1 : m.readW (L.A + BitVec.ofNat 64 84) 32 = L.r
  a2 : m.readW (L.A + BitVec.ofNat 64 88) 32 = L.v
  a3 : m.readW (L.A + BitVec.ofNat 64 92) 32 = L.vlen
  a4 : m.readW (L.A + BitVec.ofNat 64 96) 32 = L.scr
  a5 : m.readW (L.A + BitVec.ofNat 64 100) 32 = L.r + 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : BitVec 32}
    (hcur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem → RomixArgs L cur t'.mem →
      t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur → Q t') :
    WP isa (.block romixArgs) t Q := by
  unfold romixArgs
  refine cp_ok hL hc 32 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine cp_ok hL hc₁ 56 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine cp_ok hL hc₂ 68 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine cp_ok hL hc₃ 72 12 (by omega) (by omega) fun t₄ hc₄ hf₄ hm₄ => ?_
  refine cp_ok hL hc₄ 76 16 (by omega) (by omega) fun t₅ hc₅ hf₅ hm₅ => ?_
  refine ld_ok hL hc₅ eax_cs 56 (by omega) (Same.refl t₅) fun u hu he _ => ?_
  refine add_ok eax_cs hu rfl fun u' hu' he' _ => ?_
  refine st_ok hL hc₅ 20 (by omega) hu' fun t₆ hc₆ hf₆ hm₆ _ => WP.block_nil ?_
  rw [he', he] at hm₆
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆
  rw [hcur] at hm₁; rw [hc₁.kept.r] at hm₂; rw [hc₂.kept.v] at hm₃; rw [hc₃.kept.vlen] at hm₄
  rw [hc₄.kept.scr] at hm₅; rw [hc₅.kept.r] at hm₆
  refine h t₆ hc₆ (frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    frame_trans hf₅ hf₆) ?_ ?_
  · constructor <;> simp (disch := decide) only [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off,
      Mem.readW_writeW_self32]
  · simp (disch := decide) only [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off, hcur]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t'.mem → Q t') :
    WP isa (.block pbk2Args) t Q := by
  unfold pbk2Args
  refine cp_ok hL hc 40 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine cp_ok hL hc₁ 44 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine cp_ok hL hc₂ 60 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine ld_ok hL hc₃ eax_cs 64 (by omega) (Same.refl t₃) fun u hu he _ => ?_
  refine ror_ok eax_cs hu fun u' hu' he' _ => ?_
  refine st_ok hL hc₃ 12 (by omega) hu' fun t₄ hc₄ hf₄ hm₄ _ => ?_
  rw [he', he, hc₃.kept.blen, ror25 _ hL.blen25] at hm₄
  refine imm_ok eax_cs 1 (Same.refl t₄) fun u hu he _ => ?_
  refine st_ok hL hc₄ 16 (by omega) hu fun t₅ hc₅ hf₅ hm₅ _ => ?_
  rw [he] at hm₅
  refine cp_ok hL hc₅ 84 20 (by omega) (by omega) fun t₆ hc₆ hf₆ hm₆ => ?_
  refine cp_ok hL hc₆ 88 24 (by omega) (by omega) fun t₇ hc₇ hf₇ hm₇ => ?_
  refine cp_ok hL hc₇ 76 28 (by omega) (by omega) fun t₈ hc₈ hf₈ hm₈ => ?_
  refine WP.block_nil (h t₈ hc₈ (frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    frame_trans hf₅ <| frame_trans hf₆ <| frame_trans hf₇ hf₈) ?_)
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  rw [hc.kept.pw] at hm₁; rw [hc₁.kept.pwl] at hm₂; rw [hc₂.kept.b] at hm₃; rw [hc₅.kept.out] at hm₆
  rw [hc₆.kept.ol] at hm₇; rw [hc₇.kept.scr] at hm₈
  constructor <;> simp (disch := decide) only [hm₈, hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off,
    Mem.readW_writeW_self32]

theorem Ctx.flags {t : State} (hL : L.Ok) (hc : Ctx L g m₀ t) (x : BitVec 32) (c o : Bool) :
    Ctx L g m₀ (VG.X86.arithFlags t x c o) :=
  hc.store hL rfl rfl (fun _ _ => rfl) (Frame.refl _ _)

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : BitVec 32}
    (hcur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur + BitVec.ofNat 32 (L.r.toNat * 128) →
      t'.zf = some (cur + BitVec.ofNat 32 (L.r.toNat * 128) -
        (BitVec.ofNat 32 (L.blen.toNat * 128) + L.b) == 0) → Q t') :
    WP isa (.block nextBlock) t Q := by
  unfold nextBlock
  refine ld_ok hL hc ecx_cs 56 (by omega) (Same.refl t) fun u₁ hu₁ e₁ _ => ?_
  refine ror_ok ecx_cs hu₁ fun u₂ hu₂ e₂ k₂ => ?_
  refine ld_ok hL hc eax_cs 32 (by omega) hu₂ fun u₃ hu₃ e₃ k₃ => ?_
  refine add_ok eax_cs hu₃ rfl fun u₄ hu₄ e₄ k₄ => ?_
  refine ld_ok hL hc edx_cs 64 (by omega) hu₄ fun u₅ hu₅ e₅ k₅ => ?_
  refine ror_ok edx_cs hu₅ fun u₆ hu₆ e₆ k₆ => ?_
  refine add_ok edx_cs hu₆ (ld_eq hL hc 60 (by omega) hu₆) fun u₇ hu₇ e₇ k₇ => ?_
  refine st_ok hL hc 32 (by omega) hu₇ fun t₁ hc₁ hf₁ hm₁ k₈ => cmp_ok ?_
  have ecx : u₃.gpr .ecx = BitVec.ofNat 32 (L.r.toNat * 128) := by
    rw [k₃ _ (by decide), e₂, e₁, hc.kept.r, ror25 _ hL.r25]
  have eax : u₇.gpr .eax = cur + BitVec.ofNat 32 (L.r.toNat * 128) := by
    rw [k₇ _ (by decide), k₆ _ (by decide), k₅ _ (by decide), e₄, e₃, ecx]
    simp only [Nat.reduceAdd]; rw [hcur]
  have edx : u₇.gpr .edx = BitVec.ofNat 32 (L.blen.toNat * 128) + L.b := by
    rw [e₇, e₆, e₅, hc.kept.blen, ror25 _ hL.blen25]
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
`vg_pbkdf2_hmac_sha256` (any implementation of it) is verified against the
shared contract `VG.Spec.Hmac.sha256I.pbkdf2Contract`; its caller works with
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
    (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, X86.abi]
  simp only [argVal32, setWidth32_64, toNat_setWidth64,
    show argBytes [32, 32, 32, 32, 32, 32, 32, 32] = 32 from rfl]
  simp only [pbkK, pbkG, Spec.Hmac.sha256S] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

theorem pbk_post {s s' : State} (h : (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76).post s s') :
    pbkK.post s s' := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86.abi] at h
  simp only [argVal32, setWidth32_64] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkK.pub s₁ s₂) :
    (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76).pub s₁ s₂ := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, X86.abi]
  simp only [argVal32]
  obtain ⟨e, h⟩ := h
  exact ⟨e, by rw [h 0 (by omega)], by rw [h 1 (by omega)], by rw [h 2 (by omega)],
    by rw [h 3 (by omega)], by rw [h 4 (by omega)], by rw [h 5 (by omega)],
    by rw [h 6 (by omega)], by rw [h 7 (by omega)]⟩

variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
include hv

theorem pbk_correct (s : State) (h : pbkK.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (pbk_pre h)
  exact ⟨t, s', he, ha, pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (pbk_pre h₁) (pbk_pre h₂) (pbk_pub hp) e₁ e₂

end VG.Proof.Scrypt.X86.Whole

end

/-!
# scrypt on x86 (32-bit): the calls

What a call of `vg_pbkdf2_hmac_sha256` (`pbk_call`) and of `vg_scrypt_romix`
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

theorem toNat_B (L : Lay) (hL : L.Ok) {k : Nat} (hk : k < 172) :
    (L.B + BitVec.ofNat 32 k).toNat = L.B.toNat + k := by
  have := hL.nB
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc

theorem ce_esp (rd wr : List Region) : (t.callEntry.withRegions rd wr).gpr .esp = L.B + BitVec.ofNat 32 76 := by
  rw [State.withRegions_gpr, State.callEntry_esp, hc.esp, e76]

include hL

theorem ret_at : (t.gpr .esp - 4).setWidth 64 = L.A + BitVec.ofNat 64 76 := by
  rw [hc.esp, e76, addr_B (by have := hL.nB; omega)]

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
    addr_B (by omega)]

theorem ce_arg (rd wr : List Region) (i : Nat) (hi : i < 9) :
    arg (t.callEntry.withRegions rd wr) i = t.mem.readW (L.A + BitVec.ofNat 64 (80 + 4 * i)) 32 := by
  rw [arg, hc.ce_argAddr hL rd wr i hi, hc.ce_word hL rd wr (by omega) (by omega)]

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

theorem covers {t : State} (hc : Ctx L g m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r ∨ Within r L.FR) :
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
    (hsp : NoSp c) (hst : stackUse c ≤ 76) {t : State} (hc : Ctx L g m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r ∨ Within r L.FR)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g m₀ s' → Frame (wr ++ [⟨L.A, 80⟩]) t.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hnB := hL.nB
  have hesp : (t.gpr .esp).toNat = L.B.toNat + 80 := by rw [hc.esp, toNat_B L hL (by omega)]
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.call hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf _ hpost => ?_
  have hb : Region.Sub (below (t.gpr .esp) (stackUse c + 4)) ⟨L.A, 80⟩ := by
    show Region.Sub ⟨(t.gpr .esp - BitVec.ofNat 32 (stackUse c + 4)).setWidth 64, _⟩ _
    rw [hc.esp, Offset.sub_ofNat_eq _ (show stackUse c + 4 ≤ 80 by omega), BitVec.add_sub_cancel,
      addr_B (by omega)]
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
      · exact ⟨L.STK, by simp, sub_trans h.sub hfs⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Region.sub_prefix (by omega)⟩

/-- The return address of a call from the frame is in `STK`. -/
theorem ret_stk (L : Lay) : Region.Sub ⟨L.A + BitVec.ofNat 64 76, 4⟩ L.STK := Offset.sub_base _ (by omega)

namespace Lay.Ok

variable (hL : L.Ok)
include hL

theorem scr_in : InBuf L ⟨L.scr.setWidth 64, 200 * 8⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega))))

theorem stk_pw {d n : Nat} (h₁ : d + n ≤ 116) : Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ L.PW :=
  hL.kp.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-! ## PBKDF2 -/

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt sl : BitVec 32) : List Region := [L.PW, ⟨salt.setWidth 64, sl.toNat⟩]
abbrev pbkWr (L : Lay) (out ol : BitVec 32) : List Region :=
  [⟨out.setWidth 64, ol.toNat⟩, ⟨L.scr.setWidth 64, 200 * 8⟩, ⟨L.A + BitVec.ofNat 64 80, 32⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt sl out ol : BitVec 32) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨salt.setWidth 64, sl.toNat⟩ R
  ow : InBuf L ⟨out.setWidth 64, ol.toNat⟩
  so : Region.Disjoint ⟨salt.setWidth 64, sl.toNat⟩ ⟨out.setWidth 64, ol.toNat⟩
  sc : Region.Disjoint ⟨salt.setWidth 64, sl.toNat⟩ ⟨L.scr.setWidth 64, 200 * 8⟩
  oc : Region.Disjoint ⟨out.setWidth 64, ol.toNat⟩ ⟨L.scr.setWidth 64, 200 * 8⟩
  ks : L.STK.Disjoint ⟨salt.setWidth 64, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 32
  no : out.toNat + ol.toNat ≤ 2 ^ 32
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

/-- `A + 76 - 76`. -/
theorem stack76 (L : Lay) : L.A + BitVec.ofNat 64 76 - BitVec.ofNat 64 76 = L.A := BitVec.add_sub_cancel _ _

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : PbkArgs L salt sl out ol t.mem) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hnB := hL.nB
  have a := hc.ce_arg hL (pbkRd L salt sl) (pbkWr L out ol)
  have ea := hc.ce_argAddr hL (pbkRd L salt sl) (pbkWr L out ol) 0 (by omega)
  have esp := hc.ce_esp (pbkRd L salt sl) (pbkWr L out ol)
  have e76 : (L.B + BitVec.ofNat 32 76).setWidth 64 = L.A + BitVec.ofNat 64 76 := addr_B (by omega)
  have sw := hL.scr_in
  simp only [pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr, a 0 (by omega),
    a 1 (by omega), a 2 (by omega), a 3 (by omega), a 4 (by omega), a 5 (by omega), a 6 (by omega),
    a 7 (by omega), Nat.reduceMul, Nat.reduceAdd, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6, ha.a7, ea,
    esp, e76, stack76, toNat_B L hL (show 76 < 172 by omega)]
  refine ⟨by omega, by omega, trivial, trivial, hL.pw_in hr.ow, hL.pw_in sw, (hL.stk_pw (by omega)).symm,
    hr.so, hr.sc, hr.ks.symm.sub_right (Offset.sub_base _ (by omega)), hr.oc,
    (hL.stk_in (d := 80) (n := 32) (by omega) hr.ow).symm,
    (hL.stk_in (d := 80) (n := 32) (by omega) sw).symm,
    hL.stk_pw (by omega), hr.ks.sub_left (ret_stk L),
    hL.stk_in (by omega) hr.ow, hL.stk_in (by omega) sw, Offset.disjoint _ (by omega) (by omega) (by omega),
    hL.kp.sub_left (Region.sub_prefix (by omega)), hr.ks.sub_left (Region.sub_prefix (by omega)),
    by simpa using hL.stk_in (d := 0) (n := 76) (by omega) hr.ow,
    by simpa using hL.stk_in (d := 0) (n := 76) (by omega) sw,
    Offset.base_disjoint _ (by omega) (by omega), hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt sl out ol : BitVec 32} (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr L out ol, ∃ R ∈ L.regions, Within r R := by
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (Nat.le_refl _)⟩
  · obtain ⟨R, hR, hw⟩ := hr.sw
    exact ⟨R, by simpa using hR, hw⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen17; omega)⟩
  · exact ⟨L.FR, by simp, within_base _ (by omega)⟩

theorem pbk_wsub (hL : L.Ok) {out ol : BitVec 32} (hr : InBuf L ⟨out.setWidth 64, ol.toNat⟩) :
    ∀ r ∈ pbkWr L out ol, InBuf L r ∨ Within r L.FR := by
  simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl hr
  · exact .inl hL.scr_in
  · exact .inr (within_base _ (by omega))

theorem pbk_call {pbk : Prog isa}
    (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
    (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : PbkArgs L salt sl out ol t.mem) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g m₀ t' ∧
      Frame (pbkWr L out ol ++ [⟨L.A, 80⟩]) t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem (L.pw.setWidth 64) L.pwl.toNat)
        (bytesAt t.mem (salt.setWidth 64) sl.toNat) 1 ol.toNat =
        some (bytesAt t'.mem (out.setWidth 64) ol.toNat) := by
  have hnB := hL.nB
  refine call_ok hL (pbk_correct hv) hsp hst hc (pbk_pre' hL hc ha hr) (pbk_sub hL hr) (pbk_wsub hL hr.ow)
    fun s' hc' hf ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  have a := hc.ce_arg hL (pbkRd L salt sl) (pbkWr L out ol)
  have h := hpost
  simp only [pbkK, pbkG, Spec.Hmac.sha256S, hm, a 0 (by omega), a 1 (by omega), a 2 (by omega),
    a 3 (by omega), a 4 (by omega), a 5 (by omega), a 6 (by omega), Nat.reduceMul, Nat.reduceAdd, ha.a0,
    ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6] at h
  rw [hc.ce_bytesAt' hL _ _ (hL.stk_pw (by omega)).symm (by have := hL.np; omega),
    hc.ce_bytesAt' hL _ _ (hr.ks.sub_left (ret_stk L)).symm (by have := hr.ns; omega),
    show (1 : BitVec 32).toNat = 1 from rfl] at h
  exact h

/-! ## ROMix -/

/-- Block `i` of `b`. -/
abbrev blk (L : Lay) (i : Nat) : Addr := L.b.setWidth 64 + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- Its address, as a word. -/
abbrev cur (L : Lay) (i : Nat) : BitVec 32 := L.b + BitVec.ofNat 32 (128 * L.r.toNat * i)

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem cur_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) : (cur L i).setWidth 64 = blk L i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  exact addr_B (by omega)

theorem toNat_cur (hL : L.Ok) {i : Nat} (hi : i < L.pp) : (cur L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * L.r.toNat * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blk L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

/-- The regions a call of ROMix on block `i` reads and writes. -/
abbrev romixRd (L : Lay) : List Region := [⟨L.A + BitVec.ofNat 64 80, 24⟩]
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blk L i, L.r.toNat * 128⟩, ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩,
    ⟨L.scr.setWidth 64, (L.r.toNat + 2) * 128⟩]

theorem r2 (hL : L.Ok) : (L.r + 2).toNat = L.r.toNat + 2 := by
  have := hL.r25
  rw [BitVec.toNat_add, show (2 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem stack36 (L : Lay) : L.A + BitVec.ofNat 64 76 - 36 = L.A + BitVec.ofNat 64 40 := by
  rw [show BitVec.ofNat 64 76 = BitVec.ofNat 64 40 + 36 from rfl, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (cur L i) t.mem) :
    Proof.Scrypt.roMixX86.pre (t.callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have hnB := hL.nB
  have hb := blk_in hL hi
  have hv : InBuf L ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨L.scr.setWidth 64, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))
  have a := hc.ce_arg hL (romixRd L) (romixWr L i)
  have ea := hc.ce_argAddr hL (romixRd L) (romixWr L i) 0 (by omega)
  have esp := hc.ce_esp (romixRd L) (romixWr L i)
  have e76 : (L.B + BitVec.ofNat 32 76).setWidth 64 = L.A + BitVec.ofNat 64 76 := addr_B (by omega)
  simp only [Proof.Scrypt.roMixX86, State.withRegions_rd, State.withRegions_wr, a 0 (by omega),
    a 1 (by omega), a 2 (by omega), a 3 (by omega), a 4 (by omega), a 5 (by omega), Nat.reduceMul,
    Nat.reduceAdd, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ea, esp, e76, stack36, r2 hL, cur_eq hL hi,
    toNat_cur hL hi, toNat_B L hL (show 76 < 172 by omega)]
  have kb := Within.sub (within_off (L.b.setWidth 64) (blk_le hL hi))
  have ks := Within.sub (within_base (L.scr.setWidth 64) (n := (L.r.toNat + 2) * 128)
    (k := L.slen.toNat * 128) (by have := hL.slen; omega))
  refine ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    hL.stk_in (by omega) hb, hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb,
    hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb, hL.stk_in (by omega) hv,
    hL.stk_in (by omega) hs, by have := blk_le hL hi; have := hL.nb; omega, hL.nv,
    by have := hL.nc; have := hL.slen; omega, by omega, by omega, hL.rpos, hL.vmod,
    Whole.valid_pow hL.valid, trivial⟩

theorem roMix_nosp : NoSp Impl.Scrypt.X86.roMix := NoSp.of_all (by lit_decide)

theorem roMix_stack : stackUse Impl.Scrypt.X86.roMix ≤ 76 := by lit_decide

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ romixRd L ++ romixWr L i, ∃ R ∈ L.regions, Within r R := by
  simp only [romixRd, romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
  · exact ⟨L.BB, by simp, within_off _ (blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen; omega)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r ∨ Within r L.FR := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (blk_in hL hi)
  · exact .inl (.inr (.inl (within_base _ (Nat.le_refl _))))
  · exact .inl (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega)))))

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (cur L i) t.mem) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix) t fun t' => Ctx L g m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.A, 80⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blk L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blk L i) (128 * L.r.toNat)) := by
  have hb := blk_in hL hi
  refine call_ok hL RoMix.roMix_correct roMix_nosp roMix_stack hc (romix_pre hL hc hi ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  have a := hc.ce_arg hL (romixRd L) (romixWr L i)
  have h := hpost
  simp only [Proof.Scrypt.roMixX86, hm, a 0 (by omega), a 1 (by omega), a 3 (by omega), Nat.reduceMul,
    Nat.reduceAdd, ha.a0, ha.a1, ha.a3, cur_eq hL hi] at h
  rw [hc.ce_bytesAt hL _ _ (hL.stk_in (by omega) (by simpa [Nat.mul_comm] using hb)).symm
    (by have := hL.blen_lt; have := blk_le hL hi; omega)] at h
  exact h

end

end VG.Proof.Scrypt.X86.Whole
