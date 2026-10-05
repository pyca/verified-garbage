import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Proof.Scrypt.Arm.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Scrypt.Arm.Scrypt
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.Arm.Whole.Calls`. -/
section

section

section

/-!
# scrypt on 32-bit ARM: where everything is

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Layout.lean`): the contract the
proof is written against (`scryptArm`), the function's buffers, its stack
arguments (`ARGS`, 36 bytes at the stack pointer) and the 40 bytes of stack
below the stack pointer the calls use (`STK`), and the save area in `scratch`
(`SV`, from `scratch + 128 (r + 15)`), which holds our caller's `r4`–`r11` and
our return address (`Saved`). `Ctx` is what holds between the calls.
-/

namespace VG.Proof.Scrypt

open VG.Arm in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. 32-bit ARM contract for
`vg_scrypt(password = r0, password_len = r1, salt = r2, salt_len = r3, r, b,
blen, v, vlen, scratch, slen, out, out_len)`, the last nine on the stack,
with 40 bytes of stack below the stack pointer. -/
def scryptArm : Contract Arm.isa where
  pre s :=
    let r := (VG.Arm.stackArg s 0).toNat
    let pwR : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let saltR : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let bR : Region := ⟨State.addr (VG.Arm.stackArg s 1), (VG.Arm.stackArg s 2).toNat * 128⟩
    let vR : Region := ⟨State.addr (VG.Arm.stackArg s 3), (VG.Arm.stackArg s 4).toNat * 128⟩
    let scR : Region := ⟨State.addr (VG.Arm.stackArg s 5), (VG.Arm.stackArg s 6).toNat * 128⟩
    let outR : Region := ⟨State.addr (VG.Arm.stackArg s 7), (VG.Arm.stackArg s 8).toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 36⟩
    let stack : Region := ⟨State.addr s.sp - BitVec.ofNat 64 40, 40⟩
    40 ≤ s.sp.toNat ∧ s.sp.toNat + 36 ≤ 2 ^ 32 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (VG.Arm.stackArg s 1).toNat + (VG.Arm.stackArg s 2).toNat * 128 ≤ 2 ^ 32 ∧
    (VG.Arm.stackArg s 3).toNat + (VG.Arm.stackArg s 4).toNat * 128 ≤ 2 ^ 32 ∧
    (VG.Arm.stackArg s 5).toNat + (VG.Arm.stackArg s 6).toNat * 128 ≤ 2 ^ 32 ∧
    (VG.Arm.stackArg s 7).toNat + (VG.Arm.stackArg s 8).toNat ≤ 2 ^ 32 ∧
    0 < r ∧ (VG.Arm.stackArg s 2).toNat % r = 0 ∧ (VG.Arm.stackArg s 4).toNat % r = 0 ∧
    Spec.Scrypt.valid ((VG.Arm.stackArg s 4).toNat / r) r ((VG.Arm.stackArg s 2).toNat / r) (VG.Arm.stackArg s 8).toNat ∧
    (VG.Arm.stackArg s 8).toNat ≤ (2 ^ 32 - 1) * 32 ∧ (VG.Arm.stackArg s 6).toNat = r + 16
  post s s' :=
    let r := (VG.Arm.stackArg s 0).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Scrypt.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) ((VG.Arm.stackArg s 4).toNat / r) r
      ((VG.Arm.stackArg s 2).toNat / r) (VG.Arm.stackArg s 8).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (State.addr (VG.Arm.stackArg s 7)) (VG.Arm.stackArg s 8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ VG.Arm.stackArg s₁ 0 = VG.Arm.stackArg s₂ 0 ∧ VG.Arm.stackArg s₁ 1 = VG.Arm.stackArg s₂ 1 ∧
    VG.Arm.stackArg s₁ 2 = VG.Arm.stackArg s₂ 2 ∧ VG.Arm.stackArg s₁ 3 = VG.Arm.stackArg s₂ 3 ∧ VG.Arm.stackArg s₁ 4 = VG.Arm.stackArg s₂ 4 ∧
    VG.Arm.stackArg s₁ 5 = VG.Arm.stackArg s₂ 5 ∧ VG.Arm.stackArg s₁ 6 = VG.Arm.stackArg s₂ 6 ∧ VG.Arm.stackArg s₁ 7 = VG.Arm.stackArg s₂ 7 ∧
    VG.Arm.stackArg s₁ 8 = VG.Arm.stackArg s₂ 8 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (s₁.gpr .r1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (State.addr (s₁.gpr .r2)) (s₁.gpr .r3).toNat) (VG.Arm.stackArg s₁ 0).toNat
        ((VG.Arm.stackArg s₁ 2).toNat / (VG.Arm.stackArg s₁ 0).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (VG.Arm.stackArg s₁ 0).toNat ((VG.Arm.stackArg s₁ 4).toNat / (VG.Arm.stackArg s₁ 0).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (s₂.gpr .r1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (State.addr (s₂.gpr .r2)) (s₂.gpr .r3).toNat) (VG.Arm.stackArg s₂ 0).toNat
        ((VG.Arm.stackArg s₂ 2).toNat / (VG.Arm.stackArg s₂ 0).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (VG.Arm.stackArg s₂ 0).toNat ((VG.Arm.stackArg s₂ 4).toNat / (VG.Arm.stackArg s₂ 0).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm

/-- The arguments and the stack pointer on entry. -/
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
  sp : BitVec 32

namespace Lay

variable (L : VG.Proof.Scrypt.Arm.Whole.Lay)

abbrev PW : Region := ⟨State.addr L.pw, L.pwl.toNat⟩
abbrev SALT : Region := ⟨State.addr L.salt, L.sl.toNat⟩
abbrev BB : Region := ⟨State.addr L.b, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨State.addr L.v, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨State.addr L.scr, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨State.addr L.out, L.ol.toNat⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨State.addr L.sp, 36⟩
/-- The stack the calls use. -/
abbrev STK : Region := ⟨State.addr L.sp - BitVec.ofNat 64 40, 40⟩
/-- The save area. -/
abbrev SVA : Addr := State.addr L.scr + BitVec.ofNat 64 (128 * (L.r.toNat + 15))
abbrev SV : Region := ⟨L.SVA, 36⟩

/-- `p` and `N`. -/
abbrev pp : Nat := L.blen.toNat / L.r.toNat
abbrev NN : Nat := L.vlen.toNat / L.r.toNat

/-- The save area's address, as the code computes it. -/
abbrev svb : BitVec 32 := L.scr + L.r <<< 7 + 1920

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
  np : L.pw.toNat + L.pwl.toNat ≤ 2 ^ 32
  ns : L.salt.toNat + L.sl.toNat ≤ 2 ^ 32
  nb : L.b.toNat + L.blen.toNat * 128 ≤ 2 ^ 32
  nv : L.v.toNat + L.vlen.toNat * 128 ≤ 2 ^ 32
  nc : L.scr.toNat + L.slen.toNat * 128 ≤ 2 ^ 32
  no : L.out.toNat + L.ol.toNat ≤ 2 ^ 32
  nS : 40 ≤ L.sp.toNat
  nA : L.sp.toNat + 36 ≤ 2 ^ 32
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

theorem Within.sub {r R : Region} (h : VG.Proof.Scrypt.Arm.Whole.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    VG.Proof.Scrypt.Arm.Whole.Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : VG.Proof.Scrypt.Arm.Whole.Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (by decide))

/-- A writable region is within one of the writable buffers. -/
def InBuf (L : VG.Proof.Scrypt.Arm.Whole.Lay) (r : Region) : Prop :=
  VG.Proof.Scrypt.Arm.Whole.Within r L.BB ∨ VG.Proof.Scrypt.Arm.Whole.Within r L.VV ∨ VG.Proof.Scrypt.Arm.Whole.Within r L.SC ∨ VG.Proof.Scrypt.Arm.Whole.Within r L.OUT

theorem InBuf.sub {L : VG.Proof.Scrypt.Arm.Whole.Lay} {r : Region} (h : VG.Proof.Scrypt.Arm.Whole.InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.Arm.Whole.Lay} (h : L.Ok)
include h

/-- The stack the calls use misses every writable buffer. -/
theorem stk_in {r : Region} (hr : VG.Proof.Scrypt.Arm.Whole.InBuf L r) : L.STK.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.kb.sub_right hs, h.kv.sub_right hs, h.kc.sub_right hs, h.ko.sub_right hs]

/-- Our stack arguments miss every writable buffer. -/
theorem args_in {r : Region} (hr : VG.Proof.Scrypt.Arm.Whole.InBuf L r) : L.ARGS.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.ba.symm.sub_right hs, h.va.symm.sub_right hs, h.ca.symm.sub_right hs, h.oa.symm.sub_right hs]

/-- The password misses every writable buffer. -/
theorem pw_in {r : Region} (hr : VG.Proof.Scrypt.Arm.Whole.InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.pb.sub_right hs, h.pv.sub_right hs, h.pc.sub_right hs, h.po.sub_right hs]

/-- So does the salt. -/
theorem salt_in {r : Region} (hr : VG.Proof.Scrypt.Arm.Whole.InBuf L r) : L.SALT.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.sb.sub_right hs, h.sv.sub_right hs, h.sc.sub_right hs, h.so.sub_right hs]

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

/-- The save area is in `scratch`. -/
theorem sv_sc : Region.Sub L.SV L.SC := by
  have := h.slen
  exact Offset.sub_base _ (by rw [this]; omega)

/-- The save area as the code computes it. -/
theorem svb_toNat : L.svb.toNat = L.scr.toNat + 128 * (L.r.toNat + 15) := by
  have := h.nc; have := h.slen; have := h.rpos
  have e : (L.r <<< 7).toNat = L.r.toNat * 128 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  simp only [Lay.svb, BitVec.toNat_add, e, show (1920 : BitVec 32).toNat = 1920 from rfl]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem svb_addr {k : Nat} (hk : k < 36) :
    State.addr (L.svb + BitVec.ofNat 32 k) = L.SVA + BitVec.ofNat 64 k := by
  have := h.nc; have := h.slen; have hs := h.svb_toNat
  have e : State.addr L.svb = L.SVA := by
    apply BitVec.eq_of_toNat_eq
    have := L.scr.isLt
    rw [VG.Proof.Scrypt.Arm.Whole.toNat_addr, hs, Lay.SVA, BitVec.toNat_add, VG.Proof.Scrypt.Arm.Whole.toNat_addr, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 128 * (L.r.toNat + 15)) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [addr_add (by omega), e]

/-- A word of our stack arguments, as `ldr t, [sp, #off]` reads it. -/
theorem arg_addr {k : Nat} (hk : k + 4 ≤ 36) :
    State.addr (L.sp + BitVec.ofNat 32 k) = State.addr L.sp + BitVec.ofNat 64 k :=
  addr_add (by have := h.nA; omega)

end Lay.Ok

/-! ## What the calls cannot change -/

/-- Our stack arguments, as `ldr t, [sp, #off]` reads them. -/
structure Args (L : VG.Proof.Scrypt.Arm.Whole.Lay) (m : Mem) : Prop where
  r : m.readW (State.addr L.sp + BitVec.ofNat 64 0) 32 = L.r
  b : m.readW (State.addr L.sp + BitVec.ofNat 64 4) 32 = L.b
  blen : m.readW (State.addr L.sp + BitVec.ofNat 64 8) 32 = L.blen
  v : m.readW (State.addr L.sp + BitVec.ofNat 64 12) 32 = L.v
  vlen : m.readW (State.addr L.sp + BitVec.ofNat 64 16) 32 = L.vlen
  scr : m.readW (State.addr L.sp + BitVec.ofNat 64 20) 32 = L.scr
  slen : m.readW (State.addr L.sp + BitVec.ofNat 64 24) 32 = L.slen
  out : m.readW (State.addr L.sp + BitVec.ofNat 64 28) 32 = L.out
  ol : m.readW (State.addr L.sp + BitVec.ofNat 64 32) 32 = L.ol

/-- The save area holds `g`'s `r4`–`r11` and `lr`. -/
structure Saved (L : VG.Proof.Scrypt.Arm.Whole.Lay) (g : Reg → BitVec 32) (m : Mem) : Prop where
  r4 : m.readW (L.SVA + BitVec.ofNat 64 0) 32 = g .r4
  r5 : m.readW (L.SVA + BitVec.ofNat 64 4) 32 = g .r5
  r6 : m.readW (L.SVA + BitVec.ofNat 64 8) 32 = g .r6
  r7 : m.readW (L.SVA + BitVec.ofNat 64 12) 32 = g .r7
  r8 : m.readW (L.SVA + BitVec.ofNat 64 16) 32 = g .r8
  r9 : m.readW (L.SVA + BitVec.ofNat 64 20) 32 = g .r9
  r10 : m.readW (L.SVA + BitVec.ofNat 64 24) 32 = g .r10
  r11 : m.readW (L.SVA + BitVec.ofNat 64 28) 32 = g .r11
  lr : m.readW (L.SVA + BitVec.ofNat 64 32) 32 = g .lr

/-- Our stack arguments survive changes to memory that miss them. -/
theorem Args.frame {L : VG.Proof.Scrypt.Arm.Whole.Lay} {m m' : Mem} {rs : List Region} (hk : VG.Proof.Scrypt.Arm.Whole.Args L m)
    (hf : Frame rs m m') (ha : ∀ R ∈ rs, L.ARGS.Disjoint R) : VG.Proof.Scrypt.Arm.Whole.Args L m' := by
  have ka : ∀ d, d + 4 ≤ 36 → m'.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 =
      m.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 := fun d hd =>
    hf.readW (r := L.ARGS) (Offset.contains_base _ (by omega) (by omega))
      (fun R hR => ha R hR) (by decide)
  exact ⟨(ka 0 (by omega)).trans hk.r, (ka 4 (by omega)).trans hk.b, (ka 8 (by omega)).trans hk.blen,
    (ka 12 (by omega)).trans hk.v, (ka 16 (by omega)).trans hk.vlen, (ka 20 (by omega)).trans hk.scr,
    (ka 24 (by omega)).trans hk.slen, (ka 28 (by omega)).trans hk.out, (ka 32 (by omega)).trans hk.ol⟩

/-- So does the save area. -/
theorem Saved.frame {L : VG.Proof.Scrypt.Arm.Whole.Lay} {g : Reg → BitVec 32} {m m' : Mem} {rs : List Region} (hk : VG.Proof.Scrypt.Arm.Whole.Saved L g m)
    (hf : Frame rs m m') (hs : ∀ R ∈ rs, L.SV.Disjoint R) : VG.Proof.Scrypt.Arm.Whole.Saved L g m' := by
  have ks : ∀ d, d + 4 ≤ 36 → m'.readW (L.SVA + BitVec.ofNat 64 d) 32 =
      m.readW (L.SVA + BitVec.ofNat 64 d) 32 := fun d hd =>
    hf.readW (r := L.SV) (Offset.contains_base _ (by omega) (by omega))
      (fun R hR => hs R hR) (by decide)
  exact ⟨(ks 0 (by omega)).trans hk.r4, (ks 4 (by omega)).trans hk.r5, (ks 8 (by omega)).trans hk.r6,
    (ks 12 (by omega)).trans hk.r7, (ks 16 (by omega)).trans hk.r8, (ks 20 (by omega)).trans hk.r9,
    (ks 24 (by omega)).trans hk.r10, (ks 28 (by omega)).trans hk.r11, (ks 32 (by omega)).trans hk.lr⟩

/-! ## Between the calls -/

/-- The state between the calls: `g` holds the registers on entry, `m₀` the
memory. -/
structure Ctx (L : VG.Proof.Scrypt.Arm.Whole.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.sp
  r5 : t.gpr .r5 = L.b + BitVec.ofNat 32 (L.blen.toNat * 128)
  r6 : t.gpr .r6 = L.r
  r7 : t.gpr .r7 = L.scr
  r8 : t.gpr .r8 = L.pw
  r9 : t.gpr .r9 = L.pwl
  args : VG.Proof.Scrypt.Arm.Whole.Args L t.mem
  saved : VG.Proof.Scrypt.Arm.Whole.Saved L g t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : VG.Proof.Scrypt.Arm.Whole.Lay) : List Region := [L.PW, L.SALT, L.BB, L.VV, L.SC, L.OUT]

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Scrypt.Arm.Whole.Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, VG.Arm.stackArg s 0, VG.Arm.stackArg s 1, VG.Arm.stackArg s 2, VG.Arm.stackArg s 3,
    VG.Arm.stackArg s 4, VG.Arm.stackArg s 5, VG.Arm.stackArg s 6, VG.Arm.stackArg s 7, VG.Arm.stackArg s 8, s.sp⟩

theorem lay_args (s : State) : (VG.Proof.Scrypt.Arm.Whole.lay s).ARGS = ⟨stackArgAddr s 0, 36⟩ := by
  simp only [Lay.ARGS, VG.Proof.Scrypt.Arm.Whole.lay, stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptArm.pre s) : (VG.Proof.Scrypt.Arm.Whole.lay s).Ok := by
  obtain ⟨h40, h36, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea := VG.Proof.Scrypt.Arm.Whole.lay_args s
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, h40, h36, rpos, bmod, vmod, hval, olb, slen⟩

end VG.Proof.Scrypt.Arm.Whole

end

/-!
# scrypt on 32-bit ARM: the blocks between the calls

The parameters as numbers (`Lay.Ok`), the saving of our caller's registers
(`save1_ok`, `save2_ok`, `save3_ok`), and what each block between the calls
does: it keeps `Ctx`, and sets up the next call's arguments (`PbkArgs`,
`RomixArgs`) or the next block; `restore_ok` restores our caller's registers.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)

/-! ## Arithmetic -/

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem lsl7 (x : BitVec 32) : x <<< 7 = BitVec.ofNat 32 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.Arm.Whole.Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

theorem blen_lt : L.blen.toNat * 128 < 2 ^ 32 := by
  have hnb := h.nb; have hS := h.nS; have hA := h.nA
  refine Nat.lt_of_not_le fun hge => ?_
  have hb0 : L.b.toNat = 0 := by omega
  have e : L.blen.toNat * 128 = 2 ^ 32 := by omega
  have eb : State.addr L.b = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [VG.Proof.Scrypt.Arm.Whole.toNat_addr, hb0]; rfl
  have ex : (State.addr L.sp - BitVec.ofNat 64 40).toNat = L.sp.toNat - 40 := by
    rw [Offset.toNat_sub_ofNat, VG.Proof.Scrypt.Arm.Whole.toNat_addr]; omega
  apply h.kb (State.addr L.sp - BitVec.ofNat 64 40)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · have z : ∀ x : BitVec 64, x - State.addr L.b = x := fun x => by rw [eb]; exact BitVec.sub_zero x
    simp only [Region.Contains, z, e, ex]; omega

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 32 := by have := h.blen_lt; have := h.r_le; omega

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
    (hx : x + 4 ≤ 64) (hy : y + 4 ≤ 64) :
    (m.writeW (P + BitVec.ofNat 64 y) v).readW (P + BitVec.ofNat 64 x) 32 =
      m.readW (P + BitVec.ofNat 64 x) 32 :=
  Mem.readW_writeW_sep (Offset.sep P h (by omega) (by omega)) (by decide)

theorem z32 : BitVec.ofNat 32 0 = 0 := rfl

theorem enc1 : encodable (1 : BitVec 32) = true := by decide
theorem enc2 : encodable (2 : BitVec 32) = true := by decide
theorem enc1920 : encodable (1920 : BitVec 32) = true := by decide

/-! ## Saving our caller's registers -/

/-- The state before the calls: our arguments, and our caller's `r0`–`r11`
(`g`) but `r12` and `lr`. -/
structure E (L : VG.Proof.Scrypt.Arm.Whole.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.sp
  regs : ∀ r, r ≠ .r12 → r ≠ .lr → t.gpr r = g r
  args : VG.Proof.Scrypt.Arm.Whole.Args L t.mem
  frame : Frame [L.SC] m₀ t.mem
  g0 : g .r0 = L.pw
  g1 : g .r1 = L.pwl
  g2 : g .r2 = L.salt
  g3 : g .r3 = L.sl

section
variable {L : VG.Proof.Scrypt.Arm.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem E.inArgs {t : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 k)) 4 :=
  ⟨L.ARGS, by rw [he.rd, he.wr]; simp, by
    rw [he.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega)⟩

theorem E.inSc {t : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) {k : Nat} (hk : k + 4 ≤ L.slen.toNat * 128) :
    InRegions t.wr (State.addr L.scr + BitVec.ofNat 64 k) 4 :=
  ⟨L.SC, by rw [he.wr]; simp, Offset.contains_base _ hk (by omega)⟩

/-- The save area is apart from the first word of `scratch`, and from our stack arguments. -/
theorem sv_sc0 (hL : L.Ok) : L.SV.Disjoint ⟨State.addr L.scr, 4⟩ :=
  Offset.disjoint_base _ (by omega) (by have := hL.nc; have := hL.slen; omega)

/-- `E` after code that writes only `r12`, `lr` and `scratch`. -/
theorem E.upd {t t' : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r, r ≠ .r12 → r ≠ .lr → t'.gpr r = t.gpr r)
    (hf : Frame [L.SC] t.mem t'.mem) : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t' :=
  ⟨hrd.trans he.rd, hwr.trans he.wr, hsp.trans he.sp, fun r h₁ h₂ => (hg r h₁ h₂).trans (he.regs r h₁ h₂),
    he.args.frame hf (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact hL.ca.symm),
    he.frame.trans hf, he.g0, he.g1, he.g2, he.g3⟩

/-- `save1`: our return address into the first word of `scratch`. -/
theorem save1_ok (hL : L.Ok) {t : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) (hlr : t.gpr .lr = g .lr) :
    WP isa (.block save1) t fun t' => VG.Proof.Scrypt.Arm.Whole.E L g m₀ t' ∧ t'.gpr .lr = g .lr ∧ t'.gpr .r12 = L.scr ∧
      t'.mem.readW (State.addr L.scr) 32 = g .lr := by
  have l20 := he.inArgs hL (k := 20) (by omega)
  have w0 := he.inSc (k := 0) (by have := hL.slen17; omega)
  rw [BitVec.add_zero] at w0
  have a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.scr
  apply WP.of_runBlock
  simp only [save1, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Nat.reduceLT, ite_true, l20, a20, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, BitVec.add_zero, w0, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, reduceCtorEq, ite_false, hlr]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ _ => by simp only [RegUpd.gpr_setReg, h₁, ite_false]) ?_,
    trivial, trivial, Mem.readW_writeW_self32 _ _ _⟩
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := hL.slen17; omega)

/-- A word read back past a store into the save area, from outside it. -/
theorem rd_dis {a P : Addr} {m : Mem} {y : Nat} {v : BitVec 32} (hd : Region.Disjoint ⟨a, 4⟩ ⟨P, 36⟩)
    (hy : y + 4 ≤ 36) : (m.writeW (P + BitVec.ofNat 64 y) v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (Region.Disjoint.sep hd (Region.contains_self _ _)
    (Offset.contains_base _ hy (by omega))) (by decide)

/-- The first eight words of the save area. -/
structure Saved8 (L : VG.Proof.Scrypt.Arm.Whole.Lay) (g : Reg → BitVec 32) (m : Mem) : Prop where
  r4 : m.readW (L.SVA + BitVec.ofNat 64 0) 32 = g .r4
  r5 : m.readW (L.SVA + BitVec.ofNat 64 4) 32 = g .r5
  r6 : m.readW (L.SVA + BitVec.ofNat 64 8) 32 = g .r6
  r7 : m.readW (L.SVA + BitVec.ofNat 64 12) 32 = g .r7
  r8 : m.readW (L.SVA + BitVec.ofNat 64 16) 32 = g .r8
  r9 : m.readW (L.SVA + BitVec.ofNat 64 20) 32 = g .r9
  r10 : m.readW (L.SVA + BitVec.ofNat 64 24) 32 = g .r10
  r11 : m.readW (L.SVA + BitVec.ofNat 64 28) 32 = g .r11

theorem sva_k (L : VG.Proof.Scrypt.Arm.Whole.Lay) (k : Nat) :
    L.SVA + BitVec.ofNat 64 k = State.addr L.scr + BitVec.ofNat 64 (128 * (L.r.toNat + 15) + k) := by
  rw [Lay.SVA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sv_con (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) : L.SC.Contains (L.SVA + BitVec.ofNat 64 k) 4 := by
  rw [VG.Proof.Scrypt.Arm.Whole.sva_k]
  exact Offset.contains_base _ (by have := hL.slen; omega) (by have := hL.nc; have := hL.slen; omega)

theorem sv_in (hL : L.Ok) {t : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions t.wr (L.SVA + BitVec.ofNat 64 k) 4 :=
  ⟨L.SC, by rw [he.wr]; simp, VG.Proof.Scrypt.Arm.Whole.sv_con hL hk⟩

/-- A store into the save area is within `scratch`. -/
theorem Frame.sv (hL : L.Ok) {m m' : Mem} (hf : Frame [L.SC] m m') {k : Nat} (hk : k + 4 ≤ 36)
    (v : BitVec 32) : Frame [L.SC] m (m'.writeW (L.SVA + BitVec.ofNat 64 k) v) :=
  hf.writeW (List.mem_singleton_self _) _ (VG.Proof.Scrypt.Arm.Whole.sv_con hL hk)

/-- `save2`: our caller's `r4`–`r11` into the save area, whose address is
left in `r12`. -/
theorem save2_ok (hL : L.Ok) {t : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) (h12 : t.gpr .r12 = L.scr)
    (h0 : t.mem.readW (State.addr L.scr) 32 = g .lr) :
    WP isa (.block save2) t fun t' => VG.Proof.Scrypt.Arm.Whole.E L g m₀ t' ∧ t'.gpr .r12 = L.svb ∧
      t'.mem.readW (State.addr L.scr) 32 = g .lr ∧ VG.Proof.Scrypt.Arm.Whole.Saved8 L g t'.mem := by
  have l0 := he.inArgs hL (k := 0) (by omega)
  have a0 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 0)) 32 = L.r := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.r
  have s0 := hL.svb_addr (k := 0) (by omega)
  have s4 := hL.svb_addr (k := 4) (by omega)
  have s8 := hL.svb_addr (k := 8) (by omega)
  have s12 := hL.svb_addr (k := 12) (by omega)
  have s16 := hL.svb_addr (k := 16) (by omega)
  have s20 := hL.svb_addr (k := 20) (by omega)
  have s24 := hL.svb_addr (k := 24) (by omega)
  have s28 := hL.svb_addr (k := 28) (by omega)
  have w0 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 0) (by omega)
  have w4 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 4) (by omega)
  have w8 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 8) (by omega)
  have w12 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 12) (by omega)
  have w16 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 16) (by omega)
  have w20 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 20) (by omega)
  have w24 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 24) (by omega)
  have w28 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 28) (by omega)
  apply WP.of_runBlock
  simp only [save2, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Op2.eval, Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l0, a0, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false, h12, VG.Proof.Scrypt.Arm.Whole.enc1920, s0, s4, s8, s12, s16, s20,
    s24, s28, w0, w4, w8, w12, w16, w20, w24, w28]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₁, h₂, ite_false]) ?_,
    trivial, ?_, ?_⟩
  · repeat (first | exact Frame.refl _ _ | refine Frame.sv hL ?_ (by omega) _)
  · simp (disch := decide) only [VG.Proof.Scrypt.Arm.Whole.rd_dis (VG.Proof.Scrypt.Arm.Whole.sv_sc0 hL).symm]; exact h0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := decide) only [VG.Proof.Scrypt.Arm.Whole.rd_off, Mem.readW_writeW_self32] <;>
      exact he.regs _ (by decide) (by decide)

/-- `save3`: our return address into the save area. -/
theorem save3_ok (hL : L.Ok) {t : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) (h12 : t.gpr .r12 = L.svb)
    (h0 : t.mem.readW (State.addr L.scr) 32 = g .lr) (h8 : VG.Proof.Scrypt.Arm.Whole.Saved8 L g t.mem) :
    WP isa (.block save3) t fun t' => VG.Proof.Scrypt.Arm.Whole.E L g m₀ t' ∧ VG.Proof.Scrypt.Arm.Whole.Saved L g t'.mem := by
  have l20 := he.inArgs hL (k := 20) (by omega)
  have a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.scr
  have r0 : InRegions (t.rd ++ t.wr) (State.addr L.scr) 4 :=
    ⟨L.SC, by rw [he.rd, he.wr]; simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := hL.slen17; omega⟩
  have s32 := hL.svb_addr (k := 32) (by omega)
  have w32 := VG.Proof.Scrypt.Arm.Whole.sv_in hL he (k := 32) (by omega)
  apply WP.of_runBlock
  simp only [save3, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Nat.reduceLT, ite_true, l20, a20, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, BitVec.add_zero, r0, h0,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, h12, s32, w32]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₂, ite_false])
    (Frame.sv hL (Frame.refl _ _) (by omega) _), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [VG.Proof.Scrypt.Arm.Whole.rd_off, Mem.readW_writeW_self32]
  exacts [h8.r4, h8.r5, h8.r6, h8.r7, h8.r8, h8.r9, h8.r10, h8.r11]

/-! ## The blocks between the calls -/

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, and the stack arguments to push,
`c = 1` and `scratch`. -/
structure PbkArgs (L : VG.Proof.Scrypt.Arm.Whole.Lay) (salt sl out ol : BitVec 32) (t : State) : Prop where
  r0 : t.gpr .r0 = L.pw
  r1 : t.gpr .r1 = L.pwl
  r2 : t.gpr .r2 = salt
  r3 : t.gpr .r3 = sl
  r10 : t.gpr .r10 = 1
  r11 : t.gpr .r11 = out
  r12 : t.gpr .r12 = ol
  lr : t.gpr .lr = L.scr

theorem sub_b (b x : BitVec 32) : b + x - b = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- The registers kept across the calls, and the first PBKDF2's arguments. -/
theorem pbk1Args_ok (hL : L.Ok) {t : State} (he : VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) (hs : VG.Proof.Scrypt.Arm.Whole.Saved L g t.mem) :
    WP isa (.block pbk1Args) t fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r4 = L.b ∧
      VG.Proof.Scrypt.Arm.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t' := by
  have l0 := he.inArgs hL (k := 0) (by omega)
  have l4 := he.inArgs hL (k := 4) (by omega)
  have l8 := he.inArgs hL (k := 8) (by omega)
  have l20 := he.inArgs hL (k := 20) (by omega)
  have a0 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 0)) 32 = L.r := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.r
  have a4 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 4)) 32 = L.b := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.b
  have a8 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 8)) 32 = L.blen := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.blen
  have a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.scr
  apply WP.of_runBlock
  simp only [pbk1Args, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l0, l4, l8, l20, a0, a4, a8, a20, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.sp_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, VG.Proof.Scrypt.Arm.Whole.enc1, VG.Proof.Scrypt.Arm.Whole.lsl7,
    VG.Proof.Scrypt.Arm.Whole.sub_b]
  have r0 := (he.regs .r0 (by decide) (by decide)).trans he.g0
  have r1 := (he.regs .r1 (by decide) (by decide)).trans he.g1
  have r2 := (he.regs .r2 (by decide) (by decide)).trans he.g2
  have r3 := (he.regs .r3 (by decide) (by decide)).trans he.g3
  exact ⟨⟨he.rd, he.wr, he.sp, rfl, rfl, rfl, r0, r1, he.args, hs, Frame.mono he.frame (by simp)⟩,
    trivial, trivial, ⟨r0, r1, r2, r3, rfl, rfl, rfl, rfl⟩⟩

theorem Ctx.inArgs {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 k)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, by
    rw [hc.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega)⟩

theorem Ctx.arg {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) {v : BitVec 32}
    (h : t.mem.readW (State.addr L.sp + BitVec.ofNat 64 k) 32 = v) :
    t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 k)) 32 = v := by
  rw [hc.sp, hL.arg_addr hk]; exact h

/-- `Ctx` after code that writes only registers other than `r4`–`r9`. -/
theorem Ctx.regs {t t' : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hg : ∀ r, r = .r5 ∨ r = .r6 ∨ r = .r7 ∨ r = .r8 ∨ r = .r9 → t'.gpr r = t.gpr r) : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by simp)).trans hc.r5,
    (hg _ (by simp)).trans hc.r6, (hg _ (by simp)).trans hc.r7, (hg _ (by simp)).trans hc.r8,
    (hg _ (by simp)).trans hc.r9, by rw [hm]; exact hc.args, by rw [hm]; exact hc.saved,
    by rw [hm]; exact hc.frame⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : VG.Proof.Scrypt.Arm.Whole.Lay) (cur : BitVec 32) (t : State) : Prop where
  r0 : t.gpr .r0 = cur
  r1 : t.gpr .r1 = L.r
  r2 : t.gpr .r2 = L.v
  r3 : t.gpr .r3 = L.vlen
  r12 : t.gpr .r12 = L.scr
  lr : t.gpr .lr = L.r + 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) :
    WP isa (.block romixArgs) t fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r4 = t.gpr .r4 ∧
      VG.Proof.Scrypt.Arm.Whole.RomixArgs L (t.gpr .r4) t' := by
  have l12 := hc.inArgs hL (k := 12) (by omega)
  have l16 := hc.inArgs hL (k := 16) (by omega)
  have a12 := hc.arg hL (k := 12) (by omega) hc.args.v
  have a16 := hc.arg hL (k := 16) (by omega) hc.args.vlen
  apply WP.of_runBlock
  simp only [romixArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, ite_true, l12, l16, a12, a16, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq,
    ite_false, VG.Proof.Scrypt.Arm.Whole.enc2, hc.r6, hc.r7]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nextBlock_ok {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) :
    WP isa (.block nextBlock) t fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r4 = t.gpr .r4 + BitVec.ofNat 32 (L.r.toNat * 128) ∧
      t'.z = (t.gpr .r4 + BitVec.ofNat 32 (L.r.toNat * 128) - (L.b + BitVec.ofNat 32 (L.blen.toNat * 128)) == 0) := by
  apply WP.of_runBlock
  simp only [nextBlock, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Nat.reduceLeDiff, and_self,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, hc.r6, VG.Proof.Scrypt.Arm.Whole.lsl7, subFlags]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, trivial, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [hc.r5]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) :
    WP isa (.block pbk2Args) t fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      VG.Proof.Scrypt.Arm.Whole.PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t' := by
  have l4 := hc.inArgs hL (k := 4) (by omega)
  have l8 := hc.inArgs hL (k := 8) (by omega)
  have l28 := hc.inArgs hL (k := 28) (by omega)
  have l32 := hc.inArgs hL (k := 32) (by omega)
  have a4 := hc.arg hL (k := 4) (by omega) hc.args.b
  have a8 := hc.arg hL (k := 8) (by omega) hc.args.blen
  have a28 := hc.arg hL (k := 28) (by omega) hc.args.out
  have a32 := hc.arg hL (k := 32) (by omega) hc.args.ol
  apply WP.of_runBlock
  simp only [pbk2Args, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l4, l8, l28, l32, a4, a8, a28, a32, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq, ite_false, VG.Proof.Scrypt.Arm.Whole.enc1, VG.Proof.Scrypt.Arm.Whole.lsl7, hc.r7, hc.r8, hc.r9]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem restore_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) :
    WP isa (.block VG.Impl.Scrypt.Arm.restore) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = t.sp ∧
      t'.mem = t.mem := by
  have s0 := hL.svb_addr (k := 0) (by omega)
  have s4 := hL.svb_addr (k := 4) (by omega)
  have s8 := hL.svb_addr (k := 8) (by omega)
  have s12 := hL.svb_addr (k := 12) (by omega)
  have s16 := hL.svb_addr (k := 16) (by omega)
  have s20 := hL.svb_addr (k := 20) (by omega)
  have s24 := hL.svb_addr (k := 24) (by omega)
  have s28 := hL.svb_addr (k := 28) (by omega)
  have s32 := hL.svb_addr (k := 32) (by omega)
  have i : ∀ k, k + 4 ≤ 36 → InRegions (t.rd ++ t.wr) (L.SVA + BitVec.ofNat 64 k) 4 := fun k hk =>
    ⟨L.SC, by rw [hc.rd, hc.wr]; simp, VG.Proof.Scrypt.Arm.Whole.sv_con hL hk⟩
  have i0 := i 0 (by omega)
  have i4 := i 4 (by omega)
  have i8 := i 8 (by omega)
  have i12 := i 12 (by omega)
  have i16 := i 16 (by omega)
  have i20 := i 20 (by omega)
  have i24 := i 24 (by omega)
  have i28 := i 28 (by omega)
  have i32 := i 32 (by omega)
  apply WP.of_runBlock
  simp only [VG.Impl.Scrypt.Arm.restore, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq,
    ite_false, VG.Proof.Scrypt.Arm.Whole.enc1920, hc.r6, hc.r7, s0, s4, s8, s12, s16, s20, s24, s28, s32, i0, i4, i8, i12, i16, i20,
    i24, i28, i32, hc.saved.r4, hc.saved.r5, hc.saved.r6, hc.saved.r7, hc.saved.r8, hc.saved.r9,
    hc.saved.r10, hc.saved.r11, hc.saved.lr]
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

end VG.Proof.Scrypt.Arm.Whole

end

section

/-!
# scrypt on 32-bit ARM: PBKDF2-HMAC-SHA256 as a callee

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Pbkdf2.lean`):
`vg_pbkdf2_hmac_sha256_scratch` is verified against the shared contract
`VG.Spec.Hmac.sha256I.pbkdf2ScratchContract`; its caller works with the same contract
spelt out (`pbkA`): `pbk_correct` and `pbk_ct` are its correctness and
constant time under `pbkA`, from its `Verified` proof.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG.Arm

/-- `pbkdf2(password = r0, password_len = r1, salt = r2, salt_len = r3, c,
out, out_len, scratch)`, the last four on the stack, with 1600 bytes of
scratch space and 24 bytes of stack below the stack pointer. -/
def pbkA : Contract isa where
  pre s :=
    let pw : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let salt : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let out : Region := ⟨State.addr (VG.Arm.stackArg s 1), (VG.Arm.stackArg s 2).toNat⟩
    let scratch : Region := ⟨State.addr (VG.Arm.stackArg s 3), 200 * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 24, 24⟩
    24 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32 ∧ s.rd = [pw, salt, args] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    stk.Disjoint pw ∧ stk.Disjoint salt ∧ stk.Disjoint out ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (VG.Arm.stackArg s 1).toNat + (VG.Arm.stackArg s 2).toNat ≤ 2 ^ 32 ∧ (VG.Arm.stackArg s 3).toNat + 200 * 8 ≤ 2 ^ 32 ∧
    0 < (VG.Arm.stackArg s 0).toNat ∧ (VG.Arm.stackArg s 2).toNat ≤ (2 ^ 32 - 1) * 32
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac Spec.Hmac.sha256S
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) (VG.Arm.stackArg s 0).toNat
      (VG.Arm.stackArg s 2).toNat =
      some (Spec.Sha256.bytesAt s'.mem (State.addr (VG.Arm.stackArg s 1)) (VG.Arm.stackArg s 2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ VG.Arm.stackArg s₁ 0 = VG.Arm.stackArg s₂ 0 ∧ VG.Arm.stackArg s₁ 1 = VG.Arm.stackArg s₂ 1 ∧
    VG.Arm.stackArg s₁ 2 = VG.Arm.stackArg s₂ 2 ∧ VG.Arm.stackArg s₁ 3 = VG.Arm.stackArg s₂ 3

theorem pbk_pre {s : State} (h : pbkA.pre s) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [VG.Proof.Scrypt.Arm.Whole.pbkA, State.addr] at h
  sig_split h
  sig_and_intros
  all_goals try simp only [State.addr]
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

theorem pbk_post {s s' : State} (h : (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24).post s s') :
    pbkA.post s s' := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkA.pub s₁ s₂) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24).pub s₁ s₂ := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact h

variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
include hv

theorem pbk_correct (s : State) (h : pbkA.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkA.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (VG.Proof.Scrypt.Arm.Whole.pbk_pre h)
  exact ⟨t, s', he, ha, VG.Proof.Scrypt.Arm.Whole.pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkA.pre pbkA.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (VG.Proof.Scrypt.Arm.Whole.pbk_pre h₁) (VG.Proof.Scrypt.Arm.Whole.pbk_pre h₂) (VG.Proof.Scrypt.Arm.Whole.pbk_pub hp) e₁ e₂

end VG.Proof.Scrypt.Arm.Whole

end

/-!
# scrypt on 32-bit ARM: the calls

Each call passes its stack arguments in a frame of its own: four words for
`vg_pbkdf2_hmac_sha256_scratch` (`frame4_ok`, as `frame2_ok` of PBKDF2's proof, whose
callee uses at most 24 bytes below it), two for `vg_scrypt_romix`
(`frame2_ok`). What such a call does from `Ctx` and its arguments (`PbkArgs`,
`RomixArgs`): it keeps `Ctx`, and changes memory only in what it writes and
the 40 bytes of stack below the stack pointer (`pbk_call`, `romix_call`).
`pbk_pre'` and `romix_pre` are their preconditions, which the proof of
constant time uses too.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Whole.Arm (After frame2_ok frame2_rel p2_arg0 p2_arg1 p2_argAddr stk)

/-! ## A frame of four words around a call -/

/-- The registers `pbkdf2`'s stack arguments are pushed from. -/
abbrev fr4 : List Reg := [.r10, .r11, .r12, .lr]

/-- What a call in a frame of four words leaves: the regions, the stack
pointer, the callee-saved registers but `lr`, and memory outside what it
may write and the 40 bytes below the stack pointer. -/
structure After4 (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [belowA s.sp 40]) s.mem s'.mem

section
variable {s : State}

theorem p4_sp : (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).sp = s.sp - BitVec.ofNat 32 16 := rfl

theorem p4_mem (h : 16 ≤ s.sp.toNat) :
    (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).mem =
      ((((s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 0) (s.gpr .r10)).writeW
        (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 4) (s.gpr .r11)).writeW
        (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 8) (s.gpr .r12)).writeW
        (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 12) (s.gpr .lr)) := by
  have e : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' h
  show storeWords s.mem (s.sp - BitVec.ofNat 32 16) [s.gpr .r10, s.gpr .r11, s.gpr .r12, s.gpr .lr] = _
  simp only [storeWords]
  rw [BitVec.add_zero, BitVec.add_assoc, BitVec.add_assoc,
    show (4 : BitVec 32) + 4 = BitVec.ofNat 32 8 from rfl,
    show (BitVec.ofNat 32 8 : BitVec 32) + 4 = BitVec.ofNat 32 12 from rfl,
    show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
    addr_add (by omega), addr_add (by omega), addr_add (by omega)]

theorem p4_arg (h : 16 ≤ s.sp.toNat) {rd wr : List Region} {i : Nat} (hi : i < 4) :
    VG.Arm.stackArg ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr) i = s.gpr VG.Proof.Scrypt.Arm.Whole.fr4[i] := by
  have hn := s.sp.isLt
  have e : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' h
  simp only [VG.Arm.stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, VG.Proof.Scrypt.Arm.Whole.p4_sp]
  rw [VG.Proof.Scrypt.Arm.Whole.p4_mem h, addr_add (by omega)]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [VG.Proof.Scrypt.Arm.Whole.rd_off, Mem.readW_writeW_self32, Nat.mul_zero, Nat.mul_one,
      Nat.reduceMul] <;> rfl

theorem p4_a0 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    VG.Arm.stackArg ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr) 0 = s.gpr .r10 := VG.Proof.Scrypt.Arm.Whole.p4_arg h (by decide)
theorem p4_a1 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    VG.Arm.stackArg ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr) 1 = s.gpr .r11 := VG.Proof.Scrypt.Arm.Whole.p4_arg h (by decide)
theorem p4_a2 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    VG.Arm.stackArg ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr) 2 = s.gpr .r12 := VG.Proof.Scrypt.Arm.Whole.p4_arg h (by decide)
theorem p4_a3 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    VG.Arm.stackArg ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr) 3 = s.gpr .lr := VG.Proof.Scrypt.Arm.Whole.p4_arg h (by decide)

theorem p4_argAddr {rd wr : List Region} :
    stackArgAddr ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 16) := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Scrypt.Arm.Whole.p4_sp, Nat.mul_zero]
  rw [BitVec.add_zero]

end

/-- A frame of four words, popped into `r12`, around a call of verified code
that uses at most 24 bytes of stack: the callee runs from the state after
the push, and the frame leaves `After4`. -/
theorem frame4_ok {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hst : armStack c ≤ 24) {s : State} (h40 : 40 ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).rd ++ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).wr))
    (hw : Covers wr (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).wr) {Q : State → Prop}
    (hQ : ∀ s₂ : State, VG.Proof.Scrypt.Arm.Whole.After4 s wr (popped .r12 16 s₂) →
      k.post ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s).callEntry.withRegions rd wr) (s₂.withRegions rd wr) → Q (popped .r12 16 s₂)) :
    WP isa (.frame (.push VG.Proof.Scrypt.Arm.Whole.fr4) (.call n c) (.pop .r12 16)) s Q := by
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega)
  refine WP.frame (rs := VG.Proof.Scrypt.Arm.Whole.fr4) (r := .r12) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine WP.callF hv hpre hc hw (by rw [VG.Proof.Scrypt.Arm.Whole.p4_sp, h16]; omega) fun s₂ hrd hwr hsp hf hcs hpost => ?_
  refine hQ s₂ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ hpost
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, VG.Proof.Scrypt.Arm.Whole.p4_sp]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    have f₀ := pushed_frameA (rs := VG.Proof.Scrypt.Arm.Whole.fr4) (s := s) (by simp only [List.length_cons, List.length_nil]; omega)
    refine Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      have := belowA_inner (sp := s.sp) (a := 16) (b := 40) (k := 0) (by omega) h40
      simpa using this
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [VG.Proof.Scrypt.Arm.Whole.p4_sp]
        exact belowA_inner (k := 16) (by omega) h40

/-- Two runs of such a frame leak the same, if their stack pointers are the
same and the callee's preconditions and public data hold. -/
theorem frame4_rel {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧
      k.pre ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₁).callEntry.withRegions rd wr) ∧
      k.pre ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₂).callEntry.withRegions rd wr) ∧
      k.pub ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₁).callEntry.withRegions rd wr) ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₂).callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₁).rd ++ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₁).wr) ∧ Covers wr (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₁).wr ∧
      Covers (rd ++ wr) ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₂).rd ++ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₂).wr) ∧ Covers wr (pushed VG.Proof.Scrypt.Arm.Whole.fr4 s₂).wr) :
    RelCT isa P (.frame (.push VG.Proof.Scrypt.Arm.Whole.fr4) (.call n c) (.pop .r12 16)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h s₁ s₂ hp).1) (RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_)
  rw [Pbkdf2.Stream.Arm.push_eq (by decide) pa, Pbkdf2.Stream.Arm.push_eq (by decide) pb]
  exact (h s₁ s₂ hp).2

/-! ## The stack below the stack pointer -/

section
variable {L : VG.Proof.Scrypt.Arm.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The 40 bytes below the stack pointer, as `belowA` has them. -/
theorem stk_eq (hL : L.Ok) : belowA L.sp 40 = L.STK := by
  simp only [belowA, addr_sub' hL.nS]

theorem a16 (hL : L.Ok) :
    State.addr (L.sp - BitVec.ofNat 32 16) = State.addr L.sp - BitVec.ofNat 64 40 + BitVec.ofNat 64 24 := by
  rw [addr_sub' (by have := hL.nS; omega), Offset.sub_ofNat_eq _ (by omega : 16 ≤ 40)]

theorem a40 (hL : L.Ok) :
    State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24 = State.addr L.sp - BitVec.ofNat 64 40 := by
  rw [addr_sub' (by have := hL.nS; omega), BitVec.sub_sub, BitVec.ofNat_add_ofNat]

theorem toNat_Q (hL : L.Ok) : (State.addr L.sp - BitVec.ofNat 64 40).toNat = L.sp.toNat - 40 := by
  rw [← addr_sub' hL.nS, VG.Proof.Scrypt.Arm.Whole.toNat_addr, sub_toNat' hL.nS]

/-- Our frames' words and the callee's stack are in `STK`, apart. -/
theorem args16_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ L.STK := by
  rw [VG.Proof.Scrypt.Arm.Whole.a16 hL]; exact Offset.sub_base _ (by omega)

theorem cstk_sub (hL : L.Ok) :
    Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩ L.STK := by
  rw [VG.Proof.Scrypt.Arm.Whole.a40 hL]; exact Region.sub_prefix (by omega)

theorem cstk_args (hL : L.Ok) :
    Region.Disjoint ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩
      ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ := by
  rw [VG.Proof.Scrypt.Arm.Whole.a40 hL, VG.Proof.Scrypt.Arm.Whole.a16 hL]
  exact (Offset.disjoint_base _ (by omega) (by omega)).symm

/-- `STK` is apart from our stack arguments. -/
theorem stk_args (hL : L.Ok) : L.STK.Disjoint L.ARGS := by
  have := hL.nA; have := hL.nS
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have e : x - State.addr L.sp = (x - (State.addr L.sp - BitVec.ofNat 64 40)) - BitVec.ofNat 64 40 := by
    rw [BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [e, Offset.toNat_sub_ofNat] at h₂
  have := (x - (State.addr L.sp - BitVec.ofNat 64 40)).isLt
  omega

/-- `STK` is apart from the save area. -/
theorem stk_sv (hL : L.Ok) : L.STK.Disjoint L.SV := hL.kc.sub_right hL.sv_sc

end

/-! ## PBKDF2 -/

section
variable {L : VG.Proof.Scrypt.Arm.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `scratch`'s first 1600 bytes, PBKDF2's working space. -/
abbrev scr1600 (L : VG.Proof.Scrypt.Arm.Whole.Lay) : Region := ⟨State.addr L.scr, 200 * 8⟩

theorem scr_in (hL : L.Ok) : VG.Proof.Scrypt.Arm.Whole.InBuf L (VG.Proof.Scrypt.Arm.Whole.scr1600 L) :=
  .inr (.inr (.inl (VG.Proof.Scrypt.Arm.Whole.within_base _ (by have := hL.slen17; omega))))

theorem scr_sv (hL : L.Ok) : (VG.Proof.Scrypt.Arm.Whole.scr1600 L).Disjoint L.SV :=
  (Offset.disjoint_base _ (by omega) (by have := hL.nc; have := hL.slen; omega)).symm

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : VG.Proof.Scrypt.Arm.Whole.Lay) (salt sl : BitVec 32) : List Region :=
  [L.PW, ⟨State.addr salt, sl.toNat⟩, ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩]
abbrev pbkWr (L : VG.Proof.Scrypt.Arm.Whole.Lay) (out ol : BitVec 32) : List Region := [⟨State.addr out, ol.toNat⟩, VG.Proof.Scrypt.Arm.Whole.scr1600 L]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : VG.Proof.Scrypt.Arm.Whole.Lay) (salt sl out ol : BitVec 32) : Prop where
  sw : ∃ R ∈ L.regions, VG.Proof.Scrypt.Arm.Whole.Within ⟨State.addr salt, sl.toNat⟩ R
  ow : VG.Proof.Scrypt.Arm.Whole.InBuf L ⟨State.addr out, ol.toNat⟩
  osv : Region.Disjoint ⟨State.addr out, ol.toNat⟩ L.SV
  so : Region.Disjoint ⟨State.addr salt, sl.toNat⟩ ⟨State.addr out, ol.toNat⟩
  sc : Region.Disjoint ⟨State.addr salt, sl.toNat⟩ (VG.Proof.Scrypt.Arm.Whole.scr1600 L)
  oc : Region.Disjoint ⟨State.addr out, ol.toNat⟩ (VG.Proof.Scrypt.Arm.Whole.scr1600 L)
  ks : L.STK.Disjoint ⟨State.addr salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 32
  no : out.toNat + ol.toNat ≤ 2 ^ 32
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : VG.Proof.Scrypt.Arm.Whole.PbkArgs L salt sl out ol t) (hr : VG.Proof.Scrypt.Arm.Whole.PbkRegions L salt sl out ol) :
    pbkA.pre ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).callEntry.withRegions (VG.Proof.Scrypt.Arm.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol)) := by
  have hS := hL.nS
  have hA := hL.nA
  have h16 : (L.sp - BitVec.ofNat 32 16).toNat = L.sp.toNat - 16 := sub_toNat' (by omega)
  have sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega
  simp only [VG.Proof.Scrypt.Arm.Whole.pbkA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.withRegions_gpr,
    State.callEntry_sp, VG.Proof.Scrypt.Arm.Whole.p4_sp, VG.Proof.Scrypt.Arm.Whole.p4_argAddr, VG.Proof.Scrypt.Arm.Whole.p4_a0 sp16, VG.Proof.Scrypt.Arm.Whole.p4_a1 sp16, VG.Proof.Scrypt.Arm.Whole.p4_a2 sp16, VG.Proof.Scrypt.Arm.Whole.p4_a3 sp16,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12, ha.lr, h16]
  have sw := VG.Proof.Scrypt.Arm.Whole.scr_in hL
  exact ⟨by omega, by omega, trivial, trivial, hL.pw_in hr.ow, hL.pw_in sw, hr.so, hr.sc, hr.oc,
    ((hL.stk_in hr.ow).sub_left (VG.Proof.Scrypt.Arm.Whole.args16_sub hL)).symm, ((hL.stk_in sw).sub_left (VG.Proof.Scrypt.Arm.Whole.args16_sub hL)).symm,
    hL.kp.sub_left (VG.Proof.Scrypt.Arm.Whole.cstk_sub hL), hr.ks.sub_left (VG.Proof.Scrypt.Arm.Whole.cstk_sub hL), (hL.stk_in hr.ow).sub_left (VG.Proof.Scrypt.Arm.Whole.cstk_sub hL),
    (hL.stk_in sw).sub_left (VG.Proof.Scrypt.Arm.Whole.cstk_sub hL), VG.Proof.Scrypt.Arm.Whole.cstk_args hL, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

/-- A region within a writable buffer is within `wr`. -/
theorem InBuf.wr {r : Region} (h : VG.Proof.Scrypt.Arm.Whole.InBuf L r) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) :
    ∃ R ∈ t.wr, VG.Proof.Scrypt.Arm.Whole.Within r R := by
  rw [hc.wr]
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩

theorem pbk_cov (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (hr : VG.Proof.Scrypt.Arm.Whole.PbkRegions L salt sl out ol) :
    Covers (VG.Proof.Scrypt.Arm.Whole.pbkRd L salt sl ++ VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol) ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).rd ++ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).wr) ∧
      Covers (VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol) (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).wr := by
  have up : ∀ {r : Region}, (∃ R ∈ t.wr, VG.Proof.Scrypt.Arm.Whole.Within r R) → ∃ R ∈ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).rd ++ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).wr,
      VG.Proof.Scrypt.Arm.Whole.Within r R := fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  have upw : ∀ {r : Region}, (∃ R ∈ t.wr, VG.Proof.Scrypt.Arm.Whole.Within r R) → ∃ R ∈ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).wr, VG.Proof.Scrypt.Arm.Whole.Within r R :=
    fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [VG.Proof.Scrypt.Arm.Whole.pbkRd, VG.Proof.Scrypt.Arm.Whole.pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.PW, by rw [pushed_rd, hc.rd]; simp, VG.Proof.Scrypt.Arm.Whole.within_base _ (Nat.le_refl _)⟩
    · obtain ⟨R, hR, hw⟩ := hr.sw
      refine ⟨R, ?_, hw⟩
      rw [pushed_rd, pushed_wr, hc.rd, hc.wr]
      simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · refine ⟨⟨State.addr (t.sp - BitVec.ofNat 32 (4 * fr4.length)), 4 * fr4.length⟩,
        by rw [pushed_wr]; simp, 0, ?_, by simp⟩
      simp only [hc.sp, BitVec.add_zero]; rfl
    · exact up (hr.ow.wr hc)
    · exact up ((VG.Proof.Scrypt.Arm.Whole.scr_in hL).wr hc)
  · simp only [VG.Proof.Scrypt.Arm.Whole.pbkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact upw (hr.ow.wr hc)
    · exact upw ((VG.Proof.Scrypt.Arm.Whole.scr_in hL).wr hc)

/-- The regions a call of PBKDF2 writes miss our stack arguments and the save area. -/
theorem pbk_apart (hL : L.Ok) {salt sl out ol : BitVec 32} (hr : VG.Proof.Scrypt.Arm.Whole.PbkRegions L salt sl out ol) :
    ∀ R ∈ VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol ++ [L.STK], L.ARGS.Disjoint R ∧ L.SV.Disjoint R := by
  simp only [VG.Proof.Scrypt.Arm.Whole.pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro R (rfl | rfl | rfl)
  · exact ⟨hL.args_in hr.ow, hr.osv.symm⟩
  · exact ⟨hL.args_in (VG.Proof.Scrypt.Arm.Whole.scr_in hL), (VG.Proof.Scrypt.Arm.Whole.scr_sv hL).symm⟩
  · exact ⟨(VG.Proof.Scrypt.Arm.Whole.stk_args hL).symm, (VG.Proof.Scrypt.Arm.Whole.stk_sv hL).symm⟩

theorem pbk_call {pbk : Prog isa}
    (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
    (hst : armStack pbk ≤ 24) (name : String) (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t)
    {salt sl out ol : BitVec 32} (ha : VG.Proof.Scrypt.Arm.Whole.PbkArgs L salt sl out ol t) (hr : VG.Proof.Scrypt.Arm.Whole.PbkRegions L salt sl out ol) :
    WP isa (pbkCall name pbk) t fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧ t'.gpr .r4 = t.gpr .r4 ∧
      Frame (VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol ++ [L.STK]) t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem (State.addr L.pw) L.pwl.toNat)
        (bytesAt t.mem (State.addr salt) sl.toNat) 1 ol.toNat =
        some (bytesAt t'.mem (State.addr out) ol.toNat) := by
  have hS := hL.nS
  obtain ⟨cov, covw⟩ := VG.Proof.Scrypt.Arm.Whole.pbk_cov hL hc hr
  refine VG.Proof.Scrypt.Arm.Whole.frame4_ok (VG.Proof.Scrypt.Arm.Whole.pbk_correct hv) hst (by rw [hc.sp]; exact hS) (VG.Proof.Scrypt.Arm.Whole.pbk_pre' hL hc ha hr) cov covw
    fun s₂ h4 hpost => ?_
  have hf : Frame (VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol ++ [L.STK]) t.mem (popped .r12 16 s₂).mem := by
    have := h4.frame; rwa [hc.sp, VG.Proof.Scrypt.Arm.Whole.stk_eq hL] at this
  have ap := VG.Proof.Scrypt.Arm.Whole.pbk_apart hL hr
  refine ⟨⟨h4.rd.trans hc.rd, h4.wr.trans hc.wr, h4.sp.trans hc.sp,
    (h4.cs .r5 (by decide) (by decide)).trans hc.r5, (h4.cs .r6 (by decide) (by decide)).trans hc.r6,
    (h4.cs .r7 (by decide) (by decide)).trans hc.r7, (h4.cs .r8 (by decide) (by decide)).trans hc.r8,
    (h4.cs .r9 (by decide) (by decide)).trans hc.r9, hc.args.frame hf fun R hR => (ap R hR).1,
    hc.saved.frame hf fun R hR => (ap R hR).2, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩,
    h4.cs .r4 (by decide) (by decide), hf, ?_⟩
  · simp only [VG.Proof.Scrypt.Arm.Whole.pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, hs⟩ := hr.ow.sub
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
    · exact ⟨L.SC, by simp, Within.sub (VG.Proof.Scrypt.Arm.Whole.within_base _ (by have := hL.slen17; omega))⟩
    · exact ⟨L.STK, by simp, fun _ h => h⟩
  · have h := hpost
    have sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega
    simp only [VG.Proof.Scrypt.Arm.Whole.pbkA, Spec.Hmac.sha256S, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      pushed_gpr, VG.Proof.Scrypt.Arm.Whole.p4_a0 sp16, VG.Proof.Scrypt.Arm.Whole.p4_a1 sp16, VG.Proof.Scrypt.Arm.Whole.p4_a2 sp16, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12] at h
    have f₀ := pushed_frameA (rs := VG.Proof.Scrypt.Arm.Whole.fr4) (s := t) (by simp only [List.length_cons, List.length_nil]; omega)
    have d16 : ∀ {r : Region}, L.STK.Disjoint r →
        ∀ R ∈ [(⟨State.addr (t.sp - BitVec.ofNat 32 (4 * fr4.length)), 4 * fr4.length⟩ : Region)],
        r.Disjoint R := fun hd R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      rw [hc.sp]; exact (hd.sub_left (VG.Proof.Scrypt.Arm.Whole.args16_sub hL)).symm
    have e₁ : Spec.Sha256.bytesAt (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).mem (State.addr L.pw) L.pwl.toNat =
        bytesAt t.mem (State.addr L.pw) L.pwl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hL.kp) (by have := L.pwl.isLt; omega)
    have e₂ : Spec.Sha256.bytesAt (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).mem (State.addr salt) sl.toNat =
        bytesAt t.mem (State.addr salt) sl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hr.ks) (by have := sl.isLt; omega)
    rw [e₁, e₂] at h
    exact h

end

/-! ## ROMix -/

section
variable {L : VG.Proof.Scrypt.Arm.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- Block `i` of `b`, as the code computes it, and its address. -/
abbrev blkAt (L : VG.Proof.Scrypt.Arm.Whole.Lay) (i : Nat) : BitVec 32 := L.b + BitVec.ofNat 32 (128 * L.r.toNat * i)
abbrev blkA (L : VG.Proof.Scrypt.Arm.Whole.Lay) (i : Nat) : Addr := State.addr L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem addr_blk (hL : L.Ok) {i : Nat} (hi : i < L.pp) : State.addr (VG.Proof.Scrypt.Arm.Whole.blkAt L i) = VG.Proof.Scrypt.Arm.Whole.blkA L i := by
  have := VG.Proof.Scrypt.Arm.Whole.blk_le hL hi; have := hL.nb; have := hL.rpos
  exact addr_add (by omega)

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : VG.Proof.Scrypt.Arm.Whole.InBuf L ⟨VG.Proof.Scrypt.Arm.Whole.blkA L i, L.r.toNat * 128⟩ :=
  .inl (VG.Proof.Scrypt.Arm.Whole.within_off _ (VG.Proof.Scrypt.Arm.Whole.blk_le hL hi))

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : VG.Proof.Scrypt.Arm.Whole.Lay) (i : Nat) : List Region :=
  [⟨VG.Proof.Scrypt.Arm.Whole.blkA L i, L.r.toNat * 128⟩, ⟨State.addr L.v, L.vlen.toNat * 128⟩, ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩]

/-- ROMix's stack arguments. -/
abbrev romixRd (L : VG.Proof.Scrypt.Arm.Whole.Lay) : List Region := [⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩]

theorem r2 (hL : L.Ok) : (L.r + 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  rw [BitVec.toNat_add, show (2 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem args8_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩ L.STK := by
  rw [addr_sub' (by have := hL.nS; omega), Offset.sub_ofNat_eq _ (by omega : 8 ≤ 40)]
  exact Offset.sub_base _ (by omega)

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ VG.Proof.Scrypt.Arm.Whole.romixWr L i, VG.Proof.Scrypt.Arm.Whole.InBuf L r := by
  simp only [VG.Proof.Scrypt.Arm.Whole.romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.Proof.Scrypt.Arm.Whole.blk_in hL hi
  · exact .inr (.inl (VG.Proof.Scrypt.Arm.Whole.within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (VG.Proof.Scrypt.Arm.Whole.within_base _ (by have := hL.slen; omega))))

theorem romix_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.Arm.Whole.RomixArgs L (VG.Proof.Scrypt.Arm.Whole.blkAt L i) t) :
    Proof.Scrypt.roMixArm.pre ((pushed [.r12, .lr] t).callEntry.withRegions (VG.Proof.Scrypt.Arm.Whole.romixRd L) (VG.Proof.Scrypt.Arm.Whole.romixWr L i)) := by
  have hS := hL.nS
  have hA := hL.nA
  have s8 : 8 ≤ t.sp.toNat := by rw [hc.sp]; omega
  have hb := VG.Proof.Scrypt.Arm.Whole.blk_in hL hi
  have hv : VG.Proof.Scrypt.Arm.Whole.InBuf L ⟨State.addr L.v, L.vlen.toNat * 128⟩ := .inr (.inl (VG.Proof.Scrypt.Arm.Whole.within_base _ (Nat.le_refl _)))
  have hs : VG.Proof.Scrypt.Arm.Whole.InBuf L ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (VG.Proof.Scrypt.Arm.Whole.within_base _ (by have := hL.slen; omega))))
  have h8 : (L.sp - BitVec.ofNat 32 8).toNat = L.sp.toNat - 8 := sub_toNat' (by omega)
  simp only [Proof.Scrypt.roMixArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.withRegions_gpr, State.callEntry_sp, pushed_sp, p2_argAddr, p2_arg0 s8, p2_arg1,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r12, ha.lr, VG.Proof.Scrypt.Arm.Whole.r2 hL, VG.Proof.Scrypt.Arm.Whole.addr_blk hL hi]
  have kb := Within.sub (VG.Proof.Scrypt.Arm.Whole.within_off (State.addr L.b) (VG.Proof.Scrypt.Arm.Whole.blk_le hL hi))
  have ks := Within.sub (VG.Proof.Scrypt.Arm.Whole.within_base (State.addr L.scr) (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  have := VG.Proof.Scrypt.Arm.Whole.blk_le hL hi; have := hL.nb; have := hL.nv; have := hL.nc; have := hL.slen; have := hL.blen_lt; have := hL.rpos
  have tb : (VG.Proof.Scrypt.Arm.Whole.blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * L.r.toNat * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    (hL.stk_in hb).sub_left (VG.Proof.Scrypt.Arm.Whole.args8_sub hL), (hL.stk_in hv).sub_left (VG.Proof.Scrypt.Arm.Whole.args8_sub hL),
    (hL.stk_in hs).sub_left (VG.Proof.Scrypt.Arm.Whole.args8_sub hL), by rw [tb]; omega, by omega, by omega,
    by simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, h8]; omega, hL.rpos,
    hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_cov (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) :
    Covers (VG.Proof.Scrypt.Arm.Whole.romixRd L ++ VG.Proof.Scrypt.Arm.Whole.romixWr L i) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (VG.Proof.Scrypt.Arm.Whole.romixWr L i) (pushed [.r12, .lr] t).wr := by
  have upw : ∀ {r : Region}, (∃ R ∈ t.wr, VG.Proof.Scrypt.Arm.Whole.Within r R) → ∃ R ∈ (pushed [.r12, .lr] t).wr, VG.Proof.Scrypt.Arm.Whole.Within r R :=
    fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  have hw := VG.Proof.Scrypt.Arm.Whole.romix_wsub hL hi
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => upw ((hw r hr).wr hc)⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [VG.Proof.Scrypt.Arm.Whole.romixRd, List.mem_singleton] at hr; subst hr
    refine ⟨⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩,
      by rw [pushed_wr]; simp, 0, ?_, by simp⟩
    simp only [hc.sp, BitVec.add_zero]; rfl
  · obtain ⟨R, hR, hw'⟩ := upw ((hw r hr).wr hc)
    exact ⟨R, List.mem_append_right _ hR, hw'⟩

theorem roMix_stack : armStack Impl.Scrypt.Arm.roMix ≤ 16 := by lit_decide

/-- The stack `frame2_ok` lets a call change is in `STK`. -/
theorem stk_sub {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) : Region.Sub (stk t) L.STK := by
  simp only [stk, hc.sp]
  show Region.Sub ⟨State.addr L.sp - BitVec.ofNat 64 24, 24⟩ ⟨State.addr L.sp - BitVec.ofNat 64 40, 40⟩
  rw [Offset.sub_ofNat_eq _ (by omega : 24 ≤ 40)]
  exact Offset.sub_base _ (by omega)

/-- The regions a call of ROMix writes miss our stack arguments and the save area. -/
theorem romix_apart (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ R ∈ VG.Proof.Scrypt.Arm.Whole.romixWr L i ++ [L.STK], L.ARGS.Disjoint R ∧ L.SV.Disjoint R := by
  have hw := VG.Proof.Scrypt.Arm.Whole.romix_wsub hL hi
  intro R hR
  rcases List.mem_append.mp hR with hR | hR
  · refine ⟨hL.args_in (hw R hR), ?_⟩
    simp only [VG.Proof.Scrypt.Arm.Whole.romixWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hL.bc.symm.sub_left hL.sv_sc).sub_right (Within.sub (VG.Proof.Scrypt.Arm.Whole.within_off _ (VG.Proof.Scrypt.Arm.Whole.blk_le hL hi)))
    · exact hL.vc.symm.sub_left hL.sv_sc
    · exact (Offset.disjoint_base _ (by have := hL.slen; omega) (by have := hL.nc; have := hL.slen; omega))
  · simp only [List.mem_singleton] at hR; subst hR
    exact ⟨(VG.Proof.Scrypt.Arm.Whole.stk_args hL).symm, (VG.Proof.Scrypt.Arm.Whole.stk_sv hL).symm⟩

theorem romix_call (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.Arm.Whole.RomixArgs L (VG.Proof.Scrypt.Arm.Whole.blkAt L i) t) :
    WP isa (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) t
      fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧ t'.gpr .r4 = t.gpr .r4 ∧
        Frame (VG.Proof.Scrypt.Arm.Whole.romixWr L i ++ [L.STK]) t.mem t'.mem ∧
        bytesAt t'.mem (VG.Proof.Scrypt.Arm.Whole.blkA L i) (128 * L.r.toNat) =
          Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (VG.Proof.Scrypt.Arm.Whole.blkA L i) (128 * L.r.toNat)) := by
  have hS := hL.nS
  obtain ⟨cov, covw⟩ := VG.Proof.Scrypt.Arm.Whole.romix_cov hL hc hi
  refine frame2_ok (by decide) (by decide) RoMix.roMix_correct VG.Proof.Scrypt.Arm.Whole.roMix_stack (by rw [hc.sp]; omega)
    (VG.Proof.Scrypt.Arm.Whole.romix_pre hL hc hi ha) cov covw fun s₂ h2 hpost => ?_
  have hf : Frame (VG.Proof.Scrypt.Arm.Whole.romixWr L i ++ [L.STK]) t.mem (popped .r12 8 s₂).mem :=
    Frame.sub h2.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.STK, by simp, VG.Proof.Scrypt.Arm.Whole.stk_sub hc⟩
  have ap := VG.Proof.Scrypt.Arm.Whole.romix_apart hL hi
  refine ⟨⟨h2.rd.trans hc.rd, h2.wr.trans hc.wr, h2.sp.trans hc.sp,
    (h2.cs .r5 (by decide) (by decide)).trans hc.r5, (h2.cs .r6 (by decide) (by decide)).trans hc.r6,
    (h2.cs .r7 (by decide) (by decide)).trans hc.r7, (h2.cs .r8 (by decide) (by decide)).trans hc.r8,
    (h2.cs .r9 (by decide) (by decide)).trans hc.r9, hc.args.frame hf fun R hR => (ap R hR).1,
    hc.saved.frame hf fun R hR => (ap R hR).2, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩,
    h2.cs .r4 (by decide) (by decide), hf, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨R, hR, hs⟩ := (VG.Proof.Scrypt.Arm.Whole.romix_wsub hL hi r hr).sub
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, fun _ h => h⟩
  · have h := hpost
    simp only [Proof.Scrypt.roMixArm, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, ha.r0, ha.r1, ha.r3,
      VG.Proof.Scrypt.Arm.Whole.addr_blk hL hi] at h
    have f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
      (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega)
    have e : Spec.Scrypt.bytesAt (pushed [.r12, .lr] t).mem (VG.Proof.Scrypt.Arm.Whole.blkA L i) (128 * L.r.toNat) =
        bytesAt t.mem (VG.Proof.Scrypt.Arm.Whole.blkA L i) (128 * L.r.toNat) :=
      Memory.frame_bytesAt f₀ (fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        have hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
            4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
          rw [hc.sp]; exact VG.Proof.Scrypt.Arm.Whole.args8_sub hL
        rw [Nat.mul_comm]
        exact ((hL.stk_in (VG.Proof.Scrypt.Arm.Whole.blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega)
    rw [e] at h
    exact h

end

end VG.Proof.Scrypt.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.Arm.Whole.Verified`. -/
section

section

section

/-!
# scrypt on 32-bit ARM: correctness

As on the other targets (`Proof/Scrypt/AArch64/Whole/Correct.lean`): our
caller's registers are saved (`entry_ok`); step 1 leaves the blocks `X k` of
`PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`); step 3
derives the key from them (`step3_ok`); our caller's registers are restored
(`scrypt_ok`).
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

variable {L : VG.Proof.Scrypt.Arm.Whole.Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem t32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem (State.addr L.pw) L.pwl.toNat = bytesAt m₀ (State.addr L.pw) L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := L.pwl.isLt; omega)

theorem salt_bytes : bytesAt t.mem (State.addr L.salt) L.sl.toNat = bytesAt m₀ (State.addr L.salt) L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := L.sl.isLt; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : VG.Proof.Scrypt.Arm.Whole.Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
    L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : VG.Proof.Scrypt.Arm.Whole.Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
    (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : VG.Proof.Scrypt.Arm.Whole.Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : VG.Proof.Scrypt.Arm.Whole.X L m₀ k = bytesAt m (VG.Proof.Scrypt.Arm.Whole.blkA L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.pp * 128 * L.r.toNat) =
      some (bytesAt m (State.addr L.b) (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  rw [VG.Proof.Scrypt.Arm.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨VG.Proof.Scrypt.Arm.Whole.blkA L k, 128 * L.r.toNat⟩ ⟨VG.Proof.Scrypt.Arm.Whole.blkA L i, L.r.toNat * 128⟩ := by
  have h₁ := VG.Proof.Scrypt.Arm.Whole.blk_le hL hk
  have h₂ := VG.Proof.Scrypt.Arm.Whole.blk_le hL hi
  have := hL.blen_lt
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
    Region.Sub ⟨VG.Proof.Scrypt.Arm.Whole.blkA L k, 128 * L.r.toNat⟩ L.BB := by
  have := VG.Proof.Scrypt.Arm.Whole.blk_le hL hk
  exact Offset.sub_base _ (by omega)

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := VG.Proof.Scrypt.Arm.Whole.blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : VG.Proof.Scrypt.Arm.Whole.Lay) : VG.Proof.Scrypt.Arm.Whole.blkAt L 0 = L.b := by
  simp only [VG.Proof.Scrypt.Arm.Whole.blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Entry -/

/-- The state on entry. -/
theorem entry_E {s : State} (h : Proof.Scrypt.scryptArm.pre s) : VG.Proof.Scrypt.Arm.Whole.E (VG.Proof.Scrypt.Arm.Whole.lay s) s.gpr s.mem s := by
  have hL := VG.Proof.Scrypt.Arm.Whole.lay_ok h
  have a : ∀ k, k + 4 ≤ 36 → s.mem.readW (State.addr (VG.Proof.Scrypt.Arm.Whole.lay s).sp + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [← hL.arg_addr hk]; rfl
  refine ⟨?_, h.2.2.2.1, rfl, fun _ _ _ => rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Frame.refl _ _, rfl, rfl,
    rfl, rfl⟩
  · rw [h.2.2.1, ← VG.Proof.Scrypt.Arm.Whole.lay_args]; rfl
  all_goals (rw [a _ (by omega)]; rfl)

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
theorem scr_sub (hL : L.Ok) : Region.Sub (VG.Proof.Scrypt.Arm.Whole.scr1600 L) L.SC :=
  Within.sub (VG.Proof.Scrypt.Arm.Whole.within_base _ (by have := hL.slen17; omega))

omit hv hst in
theorem pbk1_regions (hL : L.Ok) :
    VG.Proof.Scrypt.Arm.Whole.PbkRegions L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := VG.Proof.Scrypt.Arm.Whole.t32 hb
  refine ⟨⟨L.SALT, by simp, VG.Proof.Scrypt.Arm.Whole.within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, hL.sc.sub_right (VG.Proof.Scrypt.Arm.Whole.scr_sub hL), ?_,
    hL.ks, hL.ns, ?_, ?_⟩
  · rw [e]; exact .inl (VG.Proof.Scrypt.Arm.Whole.within_base _ (Nat.le_refl _))
  · rw [e]; exact (hL.bc.sub_right hL.sv_sc)
  · rw [e]; exact hL.sb
  · rw [e]; exact hL.bc.sub_right (VG.Proof.Scrypt.Arm.Whole.scr_sub hL)
  · rw [e]; exact hL.nb
  · rw [e]; exact hL.ol1

theorem step1_ok (hL : L.Ok) {t₁ : State} (hc₁ : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t₁) (h4 : t₁.gpr .r4 = L.b)
    (ha₁ : VG.Proof.Scrypt.Arm.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧
      t'.gpr .r4 = L.b ∧ VG.Proof.Scrypt.Arm.Whole.Step1 L m₀ (bytesAt t'.mem (State.addr L.b) (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (VG.Proof.Scrypt.Arm.Whole.blkA L k) (128 * L.r.toNat) = VG.Proof.Scrypt.Arm.Whole.X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (VG.Proof.Scrypt.Arm.Whole.pbk_call hv hst name hL hc₁ ha₁ (VG.Proof.Scrypt.Arm.Whole.pbk1_regions hL)) fun t₂ ⟨hc₂, h4₂, _, hp⟩ =>
    ⟨hc₂, h4₂.trans h4, ?_, fun k hk => ?_⟩
  · rw [VG.Proof.Scrypt.Arm.Whole.t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact hp
  · rw [VG.Proof.Scrypt.Arm.Whole.t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact (VG.Proof.Scrypt.Arm.Whole.X_of hL hp hk).symm

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : VG.Proof.Scrypt.Arm.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = VG.Proof.Scrypt.Arm.Whole.blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.Arm.Whole.blkA L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.Arm.Whole.X L m₀ k) else VG.Proof.Scrypt.Arm.Whole.X L m₀ k

abbrev Inv (L : VG.Proof.Scrypt.Arm.Whole.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t ∧ VG.Proof.Scrypt.Arm.Whole.InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : VG.Proof.Scrypt.Arm.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = VG.Proof.Scrypt.Arm.Whole.blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.Arm.Whole.blkA L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.Arm.Whole.X L m₀ k) else VG.Proof.Scrypt.Arm.Whole.X L m₀ k

theorem next_eq (L : VG.Proof.Scrypt.Arm.Whole.Lay) (i : Nat) :
    VG.Proof.Scrypt.Arm.Whole.blkAt L i + BitVec.ofNat 32 (L.r.toNat * 128) = VG.Proof.Scrypt.Arm.Whole.blkAt L (i + 1) := by
  simp only [VG.Proof.Scrypt.Arm.Whole.blkAt]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem z_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (VG.Proof.Scrypt.Arm.Whole.blkAt L (i + 1) - (L.b + BitVec.ofNat 32 (L.blen.toNat * 128)) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := VG.Proof.Scrypt.Arm.Whole.blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [VG.Proof.Scrypt.Arm.Whole.blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 32 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 32 := by rw [hL.len_b]; exact hb
  rw [VG.Proof.MdStream.Arm.sub_beq e₁ e₂]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t)
    (hb : VG.Proof.Scrypt.Arm.Whole.InvB L m₀ i t) (ha : VG.Proof.Scrypt.Arm.Whole.RomixArgs L (VG.Proof.Scrypt.Arm.Whole.blkAt L i) t) :
    WP isa (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) t
      fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧ VG.Proof.Scrypt.Arm.Whole.Mid L m₀ i t' := by
  refine WP.mono (VG.Proof.Scrypt.Arm.Whole.romix_call hL hc hi ha) fun t₂ ⟨hc₂, h4, hf₂, hr₂⟩ => ⟨hc₂, h4.trans hb.cur, fun k hk => ?_⟩
  by_cases hki : k = i
  · subst hki
    rw [hr₂, hb.blks k hk]
    simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
  · have e₂ : bytesAt t₂.mem (VG.Proof.Scrypt.Arm.Whole.blkA L k) (128 * L.r.toNat) = bytesAt t.mem (VG.Proof.Scrypt.Arm.Whole.blkA L k) (128 * L.r.toNat) :=
      Memory.frame_bytesAt hf₂ (fun r hr => by
        simp only [VG.Proof.Scrypt.Arm.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact VG.Proof.Scrypt.Arm.Whole.blk_disj hL hk hi hki
        · exact hL.bv.sub_left (VG.Proof.Scrypt.Arm.Whole.blk_sub hL hk)
        · exact (hL.bc.sub_left (VG.Proof.Scrypt.Arm.Whole.blk_sub hL hk)).sub_right
            (Within.sub (VG.Proof.Scrypt.Arm.Whole.within_base _ (by have := hL.slen; omega)))
        · exact (hL.kb.symm.sub_left (VG.Proof.Scrypt.Arm.Whole.blk_sub hL hk)))
        (by have := hL.blen_lt; have := VG.Proof.Scrypt.Arm.Whole.blk_le hL hk; omega)
    rw [e₂, hb.blks k hk]
    by_cases hlt : k < i
    · have : k < i + 1 := by omega
      simp only [hlt, this, ite_true]
    · have : ¬ k < i + 1 := by omega
      simp only [hlt, this, ite_false]

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : VG.Proof.Scrypt.Arm.Whole.Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix"
      Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock))) t fun t' =>
        VG.Proof.Scrypt.Arm.Whole.Inv L g m₀ (i + 1) t' ∧ t'.z = decide (i + 1 = L.pp) := by
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.romixArgs_ok hL h.1) fun t₁ ⟨hc₁, hm₁, h4₁, ha₁⟩ => ?_)
  rw [h.2.cur] at ha₁
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.call_step hL hi hc₁ ⟨h4₁.trans h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
    fun t₂ ⟨hc₂, hm₂⟩ => ?_)
  refine WP.mono (VG.Proof.Scrypt.Arm.Whole.nextBlock_ok hc₂) fun t₃ ⟨hc₃, hm₃, h4₃, hz₃⟩ =>
    ⟨⟨hc₃, ⟨by rw [h4₃, hm₂.cur, VG.Proof.Scrypt.Arm.Whole.next_eq], by rw [hm₃]; exact hm₂.blks⟩⟩, ?_⟩
  rw [hz₃, hm₂.cur, VG.Proof.Scrypt.Arm.Whole.next_eq, VG.Proof.Scrypt.Arm.Whole.z_eq hL hi]

theorem loop_ok (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.Arm.Whole.Inv L g m₀ 0 t) : WP isa romixLoop t (VG.Proof.Scrypt.Arm.Whole.Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (VG.Proof.Scrypt.Arm.Whole.Inv L g m₀) (fun _ hi _ h => VG.Proof.Scrypt.Arm.Whole.body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.Arm.Whole.Inv L g m₀ L.pp t) :
    bytesAt t.mem (State.addr L.b) (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.Arm.Whole.X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hst in
theorem pbk2_regions (hL : L.Ok) :
    VG.Proof.Scrypt.Arm.Whole.PbkRegions L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := VG.Proof.Scrypt.Arm.Whole.t32 hb
  have sc : Region.Sub (VG.Proof.Scrypt.Arm.Whole.scr1600 L) L.SC := Within.sub (VG.Proof.Scrypt.Arm.Whole.within_base _ (by have := hL.slen17; omega))
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (VG.Proof.Scrypt.Arm.Whole.within_base _ (Nat.le_refl _)))),
    hL.co.symm.sub_right hL.sv_sc, ?_, ?_, hL.co.symm.sub_right sc, ?_, ?_, hL.no, hL.olb⟩
  · rw [e]; exact VG.Proof.Scrypt.Arm.Whole.within_base _ (Nat.le_refl _)
  · rw [e]; exact hL.bo
  · rw [e]; exact hL.bc.sub_right sc
  · rw [e]; exact hL.kb
  · rw [e]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t t₁ : State} (h : VG.Proof.Scrypt.Arm.Whole.Inv L g m₀ L.pp t) (hc₁ : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t₁)
    (hm₁ : t₁.mem = t.mem) (ha₁ : VG.Proof.Scrypt.Arm.Whole.PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.Arm.Whole.X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem (State.addr L.out) L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.mono (VG.Proof.Scrypt.Arm.Whole.pbk_call hv hst name hL hc₁ ha₁ (VG.Proof.Scrypt.Arm.Whole.pbk2_regions hL)) fun t₂ ⟨hc₂, _, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [VG.Proof.Scrypt.Arm.Whole.t32 hb, hc₁.pw_bytes hL, hm₁, VG.Proof.Scrypt.Arm.Whole.final_bytes' hL h] at hp
  exact hp

end

/-! ## The whole function -/

/-- scrypt, from the two derivations and the blocks. -/
theorem body_post (hL : L.Ok) {m : Mem} {out : List Byte}
    (h1 : VG.Proof.Scrypt.Arm.Whole.Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128)))
    (hp : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.Arm.Whole.X L m₀ k)) 1 L.ol.toNat = some out) :
    Spec.Scrypt.scrypt (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
      L.NN L.r.toNat L.pp L.ol.toNat = some out := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt m (State.addr L.b) (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [VG.Proof.Scrypt.Arm.Whole.X_of hL h1 hk, Whole.chunk_bytesAt _ _ (VG.Proof.Scrypt.Arm.Whole.blk_le' hL hk)]

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt` meets `scryptArm` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptArm.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ Proof.Scrypt.scryptArm.post s s' := by
  have hL := VG.Proof.Scrypt.Arm.Whole.lay_ok h
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.save1_ok hL (VG.Proof.Scrypt.Arm.Whole.entry_E h) rfl) fun t₁ ⟨e₁, _, r₁, w₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.save2_ok hL e₁ r₁ w₁) fun t₂ ⟨e₂, r₂, w₂, s₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.save3_ok hL e₂ r₂ w₂ s₂) fun t₃ ⟨e₃, s₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.pbk1Args_ok hL e₃ s₃) fun t₄ ⟨hc₄, _, h4₄, ha₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.step1_ok hv hst name hL hc₄ h4₄ ha₄) fun t₅ ⟨hc₅, h4₅, h1, hx⟩ => ?_)
  have i0 : VG.Proof.Scrypt.Arm.Whole.Inv (VG.Proof.Scrypt.Arm.Whole.lay s) s.gpr s.mem 0 t₅ := ⟨hc₅, by rw [h4₅, VG.Proof.Scrypt.Arm.Whole.blk0], fun k hk => by
    rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.loop_ok hL i0) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.pbk2Args_ok hL h₆.1) fun t₇ ⟨hc₇, hm₇, ha₇⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.Arm.Whole.step3_ok hv hst name hL h₆ hc₇ hm₇ ha₇) fun t₈ ⟨hc₈, hp⟩ => ?_)
  refine WP.mono (VG.Proof.Scrypt.Arm.Whole.restore_ok hL hc₈) fun t₉ ⟨hr₉, hsp₉, hm₉⟩ => ⟨⟨hr₉, hsp₉.trans hc₈.sp⟩, ?_⟩
  simp only [Proof.Scrypt.scryptArm, hm₉]
  exact VG.Proof.Scrypt.Arm.Whole.body_post hL h1 hp

end

end VG.Proof.Scrypt.Arm.Whole

end

/-!
# scrypt on 32-bit ARM: constant time, up to the indices `j`

As on the other targets (`Proof/Scrypt/AArch64/Whole/CT.lean`): two runs whose
public data agree have the same layout, so they are related by `Two P`: both
satisfy `P` with that layout (each with its own registers on entry and
memory), whatever their secrets, and the indices of all the scryptROMix calls
agree (`LeakEq`). The blocks address only our stack arguments, from `sp`, and
`scratch` from registers that hold the same in both runs (the taint analysis,
with the stack arguments public); each call is of constant-time code whose
public data agree (`frame4_rel`, `frame2_rel`); the loop's branch agrees since
both runs count the same blocks.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Spec.Scrypt (bytesAt roMixIndices)
open VG.Proof.Pbkdf2.Whole.Arm (frame2_rel p2_arg0 p2_arg1)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : VG.Proof.Scrypt.Arm.Whole.Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat) (bytesAt m₁ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat) (bytesAt m₂ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : VG.Proof.Scrypt.Arm.Whole.Lay} {m₁ m₂ : Mem} (h : VG.Proof.Scrypt.Arm.Whole.LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.Arm.Whole.X L m₁ k) = roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.Arm.Whole.X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₁ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₂ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  simp only [VG.Proof.Scrypt.Arm.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : VG.Proof.Scrypt.Arm.Whole.Lay
  g₁ : Reg → BitVec 32
  g₂ : Reg → BitVec 32
  m₁ : Mem
  m₂ : Mem

/-- What one run has, from its layout, its registers and memory on entry. -/
abbrev Pred := VG.Proof.Scrypt.Arm.Whole.Lay → (Reg → BitVec 32) → Mem → State → Prop

/-- Two runs with the same layout, each satisfying `P`. -/
def Two (P : VG.Proof.Scrypt.Arm.Whole.Pred) (a b : State) : Prop :=
  ∃ e : VG.Proof.Scrypt.Arm.Whole.Env, e.L.Ok ∧ VG.Proof.Scrypt.Arm.Whole.LeakEq e.L e.m₁ e.m₂ ∧ P e.L e.g₁ e.m₁ a ∧ P e.L e.g₂ e.m₂ b

/-- `Ctx` and `Φ`. -/
abbrev C (Φ : VG.Proof.Scrypt.Arm.Whole.Lay → Mem → State → Prop) : VG.Proof.Scrypt.Arm.Whole.Pred := fun L g m₀ t => VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t ∧ Φ L m₀ t

/-- Code whose runs leak the same, and which establishes `Q`. -/
theorem two_wp {c : Prog isa} {P Q : VG.Proof.Scrypt.Arm.Whole.Pred} (hct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two P) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa c t (Q L g m₀)) :
    RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two P) c (VG.Proof.Scrypt.Arm.Whole.Two Q) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ s₁ hL c₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ s₂ hL c₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁, y₂⟩

/-- Two states agree on the taint with the stack arguments and `rs` public. -/
theorem agree_L {L : VG.Proof.Scrypt.Arm.Whole.Lay} (hL : L.Ok) {a b : State} (ha : a.sp = L.sp) (hb : b.sp = L.sp)
    (wa : a.wr = [L.BB, L.VV, L.SC, L.OUT]) (wb : b.wr = [L.BB, L.VV, L.SC, L.OUT])
    (ka : VG.Proof.Scrypt.Arm.Whole.Args L a.mem) (kb : VG.Proof.Scrypt.Arm.Whole.Args L b.mem) {rs : List Reg} (hr : ∀ r ∈ rs, a.gpr r = b.gpr r) :
    VG.Arm.Taint.Agree (argTaint rs 36) a b := by
  have hA := hL.nA
  have out : ∀ (t : State), t.sp = L.sp → t.wr = [L.BB, L.VV, L.SC, L.OUT] →
      t.sp.toNat + 36 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 36⟩ r := fun t hs hw => by
    refine ⟨by rw [hs]; exact hA, fun r hr => ?_⟩
    rw [hw] at hr
    rw [hs]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hL.ba.symm, hL.va.symm, hL.ca.symm, hL.oa.symm]
  refine agree_argTaint hr (ha.trans hb.symm) (out a ha wa) (out b hb wb)
    (argMem_of (j := 9) (ha.trans hb.symm) (by rw [ha]; exact hA) fun i hi => ?_)
  have st : ∀ (t : State), t.sp = L.sp → ∀ i < 9,
      stackArg t i = t.mem.readW (State.addr L.sp + BitVec.ofNat 64 (4 * i)) 32 := fun t hs i hi => by
    simp only [stackArg, stackArgAddr, hs]
    rw [hL.arg_addr (by omega)]
  rw [st a ha i hi, st b hb i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ka.r.trans kb.r.symm, ka.b.trans kb.b.symm, ka.blen.trans kb.blen.symm, ka.v.trans kb.v.symm,
    ka.vlen.trans kb.vlen.symm, ka.scr.trans kb.scr.symm, ka.slen.trans kb.slen.symm,
    ka.out.trans kb.out.symm, ka.ol.trans kb.ol.symm]

/-- What every `P` of a piece of straight-line code gives the taint analysis. -/
structure Wfp (P : VG.Proof.Scrypt.Arm.Whole.Pred) : Prop where
  sp : ∀ L g m₀ (t : State), P L g m₀ t → t.sp = L.sp
  wr : ∀ L g m₀ (t : State), P L g m₀ t → t.wr = [L.BB, L.VV, L.SC, L.OUT]
  args : ∀ L g m₀ (t : State), P L g m₀ t → VG.Proof.Scrypt.Arm.Whole.Args L t.mem

theorem Wfp.ctx (Φ : VG.Proof.Scrypt.Arm.Whole.Lay → Mem → State → Prop) : VG.Proof.Scrypt.Arm.Whole.Wfp (VG.Proof.Scrypt.Arm.Whole.C Φ) :=
  ⟨fun _ _ _ _ h => h.1.sp, fun _ _ _ _ h => h.1.wr, fun _ _ _ _ h => h.1.args⟩

/-- A block the taint analysis accepts with the stack arguments and `rs` public. -/
theorem two_blk {is : List Instr} {P Q : VG.Proof.Scrypt.Arm.Whole.Pred} (hP : VG.Proof.Scrypt.Arm.Whole.Wfp P) (rs : List Reg)
    (hr : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → P L g₁ m₁ a → P L g₂ m₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (taint.check (argTaint rs 36) (.block is) hc).isSome = true)
    (hw : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa (.block is) t (Q L g m₀)) :
    RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two P) (.block is) (VG.Proof.Scrypt.Arm.Whole.Two Q) :=
  VG.Proof.Scrypt.Arm.Whole.two_wp (RelCT.taint (A := taint) (argTaint rs 36) (fun _ _ ⟨_, hL, _, c₁, c₂⟩ =>
    VG.Proof.Scrypt.Arm.Whole.agree_L hL (hP.sp _ _ _ _ c₁) (hP.sp _ _ _ _ c₂) (hP.wr _ _ _ _ c₁) (hP.wr _ _ _ _ c₂)
      (hP.args _ _ _ _ c₁) (hP.args _ _ _ _ c₂) (hr _ _ _ _ _ _ _ hL c₁ c₂)) h) hw

/-! ## The calls -/

/-- A call in a frame of four words, of verified code whose contract and
public data hold in both runs. -/
theorem two_call4 {n : String} {c : Prog isa} {k : Contract isa} {P Q : VG.Proof.Scrypt.Arm.Whole.Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Scrypt.Arm.Whole.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).rd ++ (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).wr) ∧ Covers (wr L) (pushed VG.Proof.Scrypt.Arm.Whole.fr4 t).wr)
    (hpub : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → VG.Proof.Scrypt.Arm.Whole.LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 a).callEntry.withRegions (rd L) (wr L))
        ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push VG.Proof.Scrypt.Arm.Whole.fr4) (.call n c) (.pop .r12 16)) t (Q L g m₀)) :
    RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two P) (.frame (.push VG.Proof.Scrypt.Arm.Whole.fr4) (.call n c) (.pop .r12 16)) (VG.Proof.Scrypt.Arm.Whole.Two Q) :=
  VG.Proof.Scrypt.Arm.Whole.two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact VG.Proof.Scrypt.Arm.Whole.frame4_rel hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-- The same for a frame of two words. -/
theorem two_call2 {n : String} {c : Prog isa} {k : Contract isa} {P Q : VG.Proof.Scrypt.Arm.Whole.Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Scrypt.Arm.Whole.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed [.r12, .lr] t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (wr L) (pushed [.r12, .lr] t).wr)
    (hpub : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → VG.Proof.Scrypt.Arm.Whole.LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed [.r12, .lr] a).callEntry.withRegions (rd L) (wr L))
        ((pushed [.r12, .lr] b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : VG.Proof.Scrypt.Arm.Whole.Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) t (Q L g m₀)) :
    RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two P) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) (VG.Proof.Scrypt.Arm.Whole.Two Q) :=
  VG.Proof.Scrypt.Arm.Whole.two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact frame2_rel (by decide) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

theorem pbk_pub_two {L : VG.Proof.Scrypt.Arm.Whole.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (c₁ : VG.Proof.Scrypt.Arm.Whole.Ctx L g₁ m₁ a) (c₂ : VG.Proof.Scrypt.Arm.Whole.Ctx L g₂ m₂ b) (hL : L.Ok) {salt sl out ol : BitVec 32}
    (a₁ : VG.Proof.Scrypt.Arm.Whole.PbkArgs L salt sl out ol a) (a₂ : VG.Proof.Scrypt.Arm.Whole.PbkArgs L salt sl out ol b) :
    a.sp = b.sp ∧ pbkA.pub ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 a).callEntry.withRegions (VG.Proof.Scrypt.Arm.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol))
      ((pushed VG.Proof.Scrypt.Arm.Whole.fr4 b).callEntry.withRegions (VG.Proof.Scrypt.Arm.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.Arm.Whole.pbkWr L out ol)) := by
  have s1 : 16 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega
  have s2 : 16 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [VG.Proof.Scrypt.Arm.Whole.pbkA, State.withRegions_sp, State.callEntry_sp, VG.Proof.Scrypt.Arm.Whole.p4_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, VG.Proof.Scrypt.Arm.Whole.p4_a0 s1, VG.Proof.Scrypt.Arm.Whole.p4_a1 s1, VG.Proof.Scrypt.Arm.Whole.p4_a2 s1, VG.Proof.Scrypt.Arm.Whole.p4_a3 s1, VG.Proof.Scrypt.Arm.Whole.p4_a0 s2, VG.Proof.Scrypt.Arm.Whole.p4_a1 s2, VG.Proof.Scrypt.Arm.Whole.p4_a2 s2, VG.Proof.Scrypt.Arm.Whole.p4_a3 s2,
    c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r10, a₁.r11, a₁.r12, a₁.lr, a₂.r0, a₂.r1, a₂.r2, a₂.r3,
    a₂.r10, a₂.r11, a₂.r12, a₂.lr, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : VG.Proof.Scrypt.Arm.Whole.Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Scrypt.Arm.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : VG.Proof.Scrypt.Arm.Whole.InvB L m₀ i t) (rd wr : List Region) :
    bytesAt ((pushed [.r12, .lr] t).callEntry.withRegions rd wr).mem (VG.Proof.Scrypt.Arm.Whole.blkA L i) (128 * L.r.toNat) =
      VG.Proof.Scrypt.Arm.Whole.X L m₀ i := by
  have hS := hL.nS
  have f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
    (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega)
  rw [State.withRegions_mem, State.callEntry_mem, Memory.frame_bytesAt f₀ (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
        rw [hc.sp]; exact VG.Proof.Scrypt.Arm.Whole.args8_sub hL
      rw [Nat.mul_comm]
      exact ((hL.stk_in (VG.Proof.Scrypt.Arm.Whole.blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega), hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : VG.Proof.Scrypt.Arm.Whole.Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (hk : VG.Proof.Scrypt.Arm.Whole.LeakEq L m₁ m₂) (c₁ : VG.Proof.Scrypt.Arm.Whole.Ctx L g₁ m₁ a) (c₂ : VG.Proof.Scrypt.Arm.Whole.Ctx L g₂ m₂ b) {i : Nat} (hi : i < L.pp)
    (b₁ : VG.Proof.Scrypt.Arm.Whole.InvB L m₁ i a) (b₂ : VG.Proof.Scrypt.Arm.Whole.InvB L m₂ i b) (a₁ : VG.Proof.Scrypt.Arm.Whole.RomixArgs L (VG.Proof.Scrypt.Arm.Whole.blkAt L i) a)
    (a₂ : VG.Proof.Scrypt.Arm.Whole.RomixArgs L (VG.Proof.Scrypt.Arm.Whole.blkAt L i) b) :
    a.sp = b.sp ∧ Proof.Scrypt.roMixArm.pub ((pushed [.r12, .lr] a).callEntry.withRegions (VG.Proof.Scrypt.Arm.Whole.romixRd L) (VG.Proof.Scrypt.Arm.Whole.romixWr L i))
      ((pushed [.r12, .lr] b).callEntry.withRegions (VG.Proof.Scrypt.Arm.Whole.romixRd L) (VG.Proof.Scrypt.Arm.Whole.romixWr L i)) := by
  have s1 : 8 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega
  have s2 : 8 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega
  have y₁ := VG.Proof.Scrypt.Arm.Whole.romix_bytes hL c₁ hi b₁ (VG.Proof.Scrypt.Arm.Whole.romixRd L) (VG.Proof.Scrypt.Arm.Whole.romixWr L i)
  have y₂ := VG.Proof.Scrypt.Arm.Whole.romix_bytes hL c₂ hi b₂ (VG.Proof.Scrypt.Arm.Whole.romixRd L) (VG.Proof.Scrypt.Arm.Whole.romixWr L i)
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [Proof.Scrypt.roMixArm, State.withRegions_sp, State.callEntry_sp, pushed_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, p2_arg0 s1, p2_arg1, p2_arg0 s2, c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r12, a₁.lr,
    a₂.r0, a₂.r1, a₂.r2, a₂.r3, a₂.r12, a₂.lr, VG.Proof.Scrypt.Arm.Whole.addr_blk hL hi, true_and]
  rw [y₁, y₂]
  exact VG.Proof.Scrypt.Arm.Whole.leak_X hk hi

/-! ## The pieces -/

theorem Wfp.e {P : VG.Proof.Scrypt.Arm.Whole.Pred} (h : ∀ L g m₀ t, P L g m₀ t → VG.Proof.Scrypt.Arm.Whole.E L g m₀ t) : VG.Proof.Scrypt.Arm.Whole.Wfp P :=
  ⟨fun _ _ _ _ hp => (h _ _ _ _ hp).sp, fun _ _ _ _ hp => (h _ _ _ _ hp).wr,
    fun _ _ _ _ hp => (h _ _ _ _ hp).args⟩

abbrev P0 : VG.Proof.Scrypt.Arm.Whole.Pred := fun L g m₀ t => VG.Proof.Scrypt.Arm.Whole.E L g m₀ t ∧ t.gpr .lr = g .lr
abbrev P1 : VG.Proof.Scrypt.Arm.Whole.Pred := fun L g m₀ t => VG.Proof.Scrypt.Arm.Whole.E L g m₀ t ∧ t.gpr .r12 = L.scr ∧ t.mem.readW (State.addr L.scr) 32 = g .lr
abbrev P2 : VG.Proof.Scrypt.Arm.Whole.Pred := fun L g m₀ t =>
  VG.Proof.Scrypt.Arm.Whole.E L g m₀ t ∧ t.gpr .r12 = L.svb ∧ t.mem.readW (State.addr L.scr) 32 = g .lr ∧ VG.Proof.Scrypt.Arm.Whole.Saved8 L g t.mem
abbrev P3 : VG.Proof.Scrypt.Arm.Whole.Pred := fun L g m₀ t => VG.Proof.Scrypt.Arm.Whole.E L g m₀ t ∧ VG.Proof.Scrypt.Arm.Whole.Saved L g t.mem

theorem save1_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two VG.Proof.Scrypt.Arm.Whole.P0) (.block save1) (VG.Proof.Scrypt.Arm.Whole.Two VG.Proof.Scrypt.Arm.Whole.P1) :=
  VG.Proof.Scrypt.Arm.Whole.two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hl⟩ => WP.mono (VG.Proof.Scrypt.Arm.Whole.save1_ok hL he hl) fun _ ⟨e, _, r, w⟩ => ⟨e, r, w⟩

theorem save2_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two VG.Proof.Scrypt.Arm.Whole.P1) (.block save2) (VG.Proof.Scrypt.Arm.Whole.Two VG.Proof.Scrypt.Arm.Whole.P2) :=
  VG.Proof.Scrypt.Arm.Whole.two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw⟩ => VG.Proof.Scrypt.Arm.Whole.save2_ok hL he hr hw

theorem save3_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two VG.Proof.Scrypt.Arm.Whole.P2) (.block save3) (VG.Proof.Scrypt.Arm.Whole.Two VG.Proof.Scrypt.Arm.Whole.P3) :=
  VG.Proof.Scrypt.Arm.Whole.two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw, h8⟩ => VG.Proof.Scrypt.Arm.Whole.save3_ok hL he hr hw h8

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : VG.Proof.Scrypt.Arm.Whole.Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.Arm.Whole.InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C (VG.Proof.Scrypt.Arm.Whole.LoopAt n))) (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock)))
      (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.Arm.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C (VG.Proof.Scrypt.Arm.Whole.LoopAt n))) (.block romixArgs) (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      VG.Proof.Scrypt.Arm.Whole.InvB L m₀ (L.pp - n) t ∧ VG.Proof.Scrypt.Arm.Whole.RomixArgs L (VG.Proof.Scrypt.Arm.Whole.blkAt L (L.pp - n)) t)) :=
    VG.Proof.Scrypt.Arm.Whole.two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hb⟩ =>
        WP.mono (VG.Proof.Scrypt.Arm.Whole.romixArgs_ok hL hc) fun _ ⟨hc', hm, h4, ha⟩ =>
          ⟨hc', h0, hn, ⟨h4.trans hb.cur, by rw [hm]; exact hb.blks⟩, by rw [hb.cur] at ha; exact ha⟩
  have b : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.Arm.Whole.InvB L m₀ (L.pp - n) t ∧
      VG.Proof.Scrypt.Arm.Whole.RomixArgs L (VG.Proof.Scrypt.Arm.Whole.blkAt L (L.pp - n)) t)) (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8))
      (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.Arm.Whole.Mid L m₀ (L.pp - n) t)) :=
    VG.Proof.Scrypt.Arm.Whole.two_call2 RoMix.roMix_correct RoMix.roMix_ct (fun L => VG.Proof.Scrypt.Arm.Whole.romixRd L) (fun L => VG.Proof.Scrypt.Arm.Whole.romixWr L (L.pp - n))
      (fun L _ _ _ hL ⟨hc, h0, hn, _, ha⟩ => ⟨VG.Proof.Scrypt.Arm.Whole.romix_pre hL hc (i := L.pp - n) (by omega) ha,
        VG.Proof.Scrypt.Arm.Whole.romix_cov hL hc (i := L.pp - n) (by omega)⟩)
      (fun _ _ _ _ _ _ _ hL hk ⟨c₁, h0, hn, b₁, a₁⟩ ⟨c₂, _, _, b₂, a₂⟩ =>
        VG.Proof.Scrypt.Arm.Whole.romix_pub_two hL hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ _ hL ⟨hc, h0, hn, hb, ha⟩ =>
        WP.mono (VG.Proof.Scrypt.Arm.Whole.call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.Arm.Whole.Mid L m₀ (L.pp - n) t)) (.block nextBlock)
      (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.Arm.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) :=
    VG.Proof.Scrypt.Arm.Whole.two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hm⟩ =>
        WP.mono (VG.Proof.Scrypt.Arm.Whole.nextBlock_ok hc) fun _ ⟨hc', hm', h4, hz⟩ =>
          ⟨hc', h0, hn, ⟨by rw [h4, hm.cur, VG.Proof.Scrypt.Arm.Whole.next_eq], by rw [hm']; exact hm.blks⟩,
            by rw [hz, hm.cur, VG.Proof.Scrypt.Arm.Whole.next_eq, VG.Proof.Scrypt.Arm.Whole.z_eq hL (by omega)]⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => VG.Proof.Scrypt.Arm.Whole.InvB L m₀ 0 t)) romixLoop (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => VG.Proof.Scrypt.Arm.Whole.InvB L m₀ L.pp t)) := by
  have ev : ∀ x : State, isa.eval .ne x = some (!x.z) := fun x => VG.Proof.MdStream.Arm.eval_ne x
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => VG.Proof.Scrypt.Arm.Whole.InvB L m₀ L.pp t))
    (fun n => VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C (VG.Proof.Scrypt.Arm.Whole.LoopAt n))) (fun n => (VG.Proof.Scrypt.Arm.Whole.body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, ⟨c₁, h0, hn, b₁, z₁⟩, ⟨c₂, -, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, ⟨c₁, show VG.Proof.Scrypt.Arm.Whole.InvB e.L e.m₁ e.L.pp a from hl ▸ b₁⟩,
          ⟨c₂, show VG.Proof.Scrypt.Arm.Whole.InvB e.L e.m₂ e.L.pp b from hl ▸ b₂⟩⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, ⟨c₁, by omega, by omega, e₁ ▸ b₁⟩,
          ⟨c₂, by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, ⟨c₁, b₁⟩, ⟨c₂, b₂⟩⟩ => ⟨e.L.pp, e, hL, hk,
    ⟨c₁, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨c₂, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

abbrev Args1 (L : VG.Proof.Scrypt.Arm.Whole.Lay) (_ : Mem) (t : State) : Prop :=
  t.gpr .r4 = L.b ∧ VG.Proof.Scrypt.Arm.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t
abbrev Args2 (L : VG.Proof.Scrypt.Arm.Whole.Lay) (_ : Mem) (t : State) : Prop :=
  VG.Proof.Scrypt.Arm.Whole.PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t

theorem pbk1_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two VG.Proof.Scrypt.Arm.Whole.P3) (.block pbk1Args) (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C VG.Proof.Scrypt.Arm.Whole.Args1)) :=
  VG.Proof.Scrypt.Arm.Whole.two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hs⟩ => WP.mono (VG.Proof.Scrypt.Arm.Whole.pbk1Args_ok hL he hs) fun _ ⟨hc, _, h4, ha⟩ => ⟨hc, h4, ha⟩

theorem pbk2_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => VG.Proof.Scrypt.Arm.Whole.InvB L m₀ L.pp t)) (.block pbk2Args) (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C VG.Proof.Scrypt.Arm.Whole.Args2)) :=
  VG.Proof.Scrypt.Arm.Whole.two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (VG.Proof.Scrypt.Arm.Whole.pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩

theorem restore_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun _ _ _ => True)) (.block restore) fun _ _ => True :=
  (VG.Proof.Scrypt.Arm.Whole.two_blk (Q := fun _ _ _ _ => True) (Wfp.ctx _) [.r6, .r7]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact c₁.1.r6.trans c₂.1.r6.symm
      · exact c₁.1.r7.trans c₂.1.r7.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (VG.Proof.Scrypt.Arm.Whole.restore_ok hL hc) fun _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

theorem call1_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C VG.Proof.Scrypt.Arm.Whole.Args1)) (pbkCall name pbk) (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun L m₀ t => VG.Proof.Scrypt.Arm.Whole.InvB L m₀ 0 t)) :=
  VG.Proof.Scrypt.Arm.Whole.two_call4 (VG.Proof.Scrypt.Arm.Whole.pbk_correct hv) (VG.Proof.Scrypt.Arm.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.Arm.Whole.pbkRd L L.salt L.sl)
    (fun L => VG.Proof.Scrypt.Arm.Whole.pbkWr L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun _ _ _ _ hL ⟨hc, _, ha⟩ => ⟨VG.Proof.Scrypt.Arm.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.Arm.Whole.pbk1_regions hL), VG.Proof.Scrypt.Arm.Whole.pbk_cov hL hc (VG.Proof.Scrypt.Arm.Whole.pbk1_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, _, a₁⟩ ⟨c₂, _, a₂⟩ => VG.Proof.Scrypt.Arm.Whole.pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, h4, ha⟩ => WP.mono (VG.Proof.Scrypt.Arm.Whole.step1_ok hv hst name hL hc h4 ha) fun _ ⟨hc', h4', _, hx⟩ =>
      ⟨hc', by rw [h4', VG.Proof.Scrypt.Arm.Whole.blk0], fun k hk => by rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩)

theorem call2_ct : RelCT isa (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C VG.Proof.Scrypt.Arm.Whole.Args2)) (pbkCall name pbk) (VG.Proof.Scrypt.Arm.Whole.Two (VG.Proof.Scrypt.Arm.Whole.C fun _ _ _ => True)) :=
  VG.Proof.Scrypt.Arm.Whole.two_call4 (VG.Proof.Scrypt.Arm.Whole.pbk_correct hv) (VG.Proof.Scrypt.Arm.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.Arm.Whole.pbkRd L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun L => VG.Proof.Scrypt.Arm.Whole.pbkWr L L.out L.ol)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => ⟨VG.Proof.Scrypt.Arm.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.Arm.Whole.pbk2_regions hL), VG.Proof.Scrypt.Arm.Whole.pbk_cov hL hc (VG.Proof.Scrypt.Arm.Whole.pbk2_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ => VG.Proof.Scrypt.Arm.Whole.pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => WP.mono (VG.Proof.Scrypt.Arm.Whole.pbk_call hv hst name hL hc ha (VG.Proof.Scrypt.Arm.Whole.pbk2_regions hL)) fun _ h =>
      ⟨h.1, trivial⟩)

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptArm.pre Proof.Scrypt.scryptArm.pub (scrypt name pbk) := by
  refine RelCT.constantTime ((save1_ct.seq (save2_ct.seq (save3_ct.seq (pbk1_ct.seq
    ((VG.Proof.Scrypt.Arm.Whole.call1_ct hv hst name).seq (loop_ct.seq (pbk2_ct.seq ((VG.Proof.Scrypt.Arm.Whole.call2_ct hv hst name).seq VG.Proof.Scrypt.Arm.Whole.restore_ct)))))))).mono
    ?_ fun _ _ _ => trivial)
  rintro s₁ s₂ ⟨h₁, h₂, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp, hlk⟩
  have e : VG.Proof.Scrypt.Arm.Whole.lay s₂ = VG.Proof.Scrypt.Arm.Whole.lay s₁ := by
    simp only [VG.Proof.Scrypt.Arm.Whole.lay, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp]
  refine ⟨⟨VG.Proof.Scrypt.Arm.Whole.lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, VG.Proof.Scrypt.Arm.Whole.lay_ok h₁, ?_, ⟨VG.Proof.Scrypt.Arm.Whole.entry_E h₁, rfl⟩,
    ⟨e ▸ VG.Proof.Scrypt.Arm.Whole.entry_E h₂, rfl⟩⟩
  rw [← h0, ← h1, ← h2, ← h3, ← a0, ← a2, ← a4] at hlk
  exact hlk

end

end VG.Proof.Scrypt.Arm.Whole

end

/-!
# scrypt on 32-bit ARM: the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract whose frames use at most 24 bytes of stack, is verified
against `Spec.Scrypt.scryptContract` for the 40 bytes of stack its calls use
(`scrypt_verified_of`); and so is the one calling `vg_pbkdf2_hmac_sha256_scratch`
(`scrypt_verified`).
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack

theorem map_range9 {α : Type} (f : Nat → α) :
    List.map f (List.range 9) = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8] := rfl

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
words at `0x9000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000
    | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9000 then 1 else if a = 0x9005 then 0x30 else if a = 0x9008 then 1
    else if a = 0x900D then 0x40 else if a = 0x9010 then 2 else if a = 0x9015 then 0x50
    else if a = 0x9018 then 17 else if a = 0x901D then 0x60 else if a = 0x9020 then 1 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x9000, 36⟩]
  wr := [⟨0x3000, 128⟩, ⟨0x4000, 256⟩, ⟨0x5000, 2176⟩, ⟨0x6000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptArm.Implies (Spec.Scrypt.scryptContract Arm.abi 40) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, VG.Proof.Scrypt.Arm.Whole.map_range9, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, VG.Proof.Scrypt.Arm.Whole.map_range9, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, VG.Proof.Scrypt.Arm.Whole.map_range9, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, VG.Proof.Scrypt.Arm.Whole.map_range9, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, VG.Proof.Scrypt.Arm.Whole.map_range9, List.append_eq] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 a0 a1 a2 a3 a4 a5 a6 a7
        exact ⟨h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, VG.Proof.Scrypt.Arm.Whole.map_range9, List.append_eq, VG.Proof.Scrypt.Arm.Whole.satState] [satState]
          using VG.Proof.Scrypt.Arm.Whole.satState }

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified Arm.target (scrypt name pbk) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := VG.Proof.Scrypt.Arm.Whole.scrypt_ok hv hst name h
    exact ⟨t, s', he, hp⟩) (VG.Proof.Scrypt.Arm.Whole.scrypt_ct hv hst name) VG.Proof.Scrypt.Arm.Whole.scrypt_implies

end

/-! ## With `vg_pbkdf2_hmac_sha256_scratch` -/

theorem armStack_zero {c : Prog isa} (h : c.noFrames = true) : armStack c = 0 := by
  induction c <;> simp_all [Code.noFrames, armStack]

/-- How much stack the frames of `pbkdf2` use. -/
theorem pbkdf2_stack {F : Impl.Pbkdf2.Whole.Arm.Fns} (hi : F.H.initC.noFrames = true)
    (hu : F.H.updC.noFrames = true) (hf : F.H.finC.noFrames = true) (h₁ : armStack F.hiC ≤ 16)
    (h₂ : armStack F.hfC ≤ 16) (h₃ : armStack F.itC ≤ 16) : armStack F.pbkdf2 ≤ 24 := by
  simp only [Impl.Pbkdf2.Whole.Arm.Fns.pbkdf2, Impl.Pbkdf2.Whole.Arm.Fns.key,
    Impl.Pbkdf2.Whole.Arm.Fns.hashKey, Impl.Pbkdf2.Whole.Arm.Fns.setup, Impl.Pbkdf2.Whole.Arm.Fns.block,
    Impl.Pbkdf2.Whole.Arm.Fns.outLen, Impl.Pbkdf2.Whole.Arm.Fns.outLoop, Impl.Pbkdf2.Stream.Arm.copy,
    Impl.Pbkdf2.Stream.Arm.Hash.callInit, armStack, VG.Proof.Scrypt.Arm.Whole.armStack_zero hi, VG.Proof.Scrypt.Arm.Whole.armStack_zero hu, VG.Proof.Scrypt.Arm.Whole.armStack_zero hf,
    List.length_cons, List.length_nil, Nat.max_le]
  omega

/-- The code of `vg_pbkdf2_hmac_sha256_scratch`. -/
abbrev pbkC : Prog isa := Proof.Pbkdf2.Whole.Arm.sha256F.pbkdf2

theorem pbk_stack : armStack VG.Proof.Scrypt.Arm.Whole.pbkC ≤ 24 :=
  VG.Proof.Scrypt.Arm.Whole.pbkdf2_stack Proof.Pbkdf2.Stream.Arm.sha256OK.initNF Proof.Pbkdf2.Stream.Arm.sha256OK.updNF
    Proof.Pbkdf2.Stream.Arm.sha256OK.finNF Proof.Pbkdf2.Whole.Arm.sha256OKF.hiSt
    Proof.Pbkdf2.Whole.Arm.sha256OKF.hfSt Proof.Pbkdf2.Whole.Arm.sha256OKF.itSt

/-- `vg_scrypt`. -/
theorem scrypt_verified :
    Verified Arm.target (scrypt Spec.Hmac.sha256I.pbkdf2ScratchApi.name VG.Proof.Scrypt.Arm.Whole.pbkC) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  VG.Proof.Scrypt.Arm.Whole.scrypt_verified_of Proof.Pbkdf2.Whole.Arm.sha256 VG.Proof.Scrypt.Arm.Whole.pbk_stack _

end VG.Proof.Scrypt.Arm.Whole

end
