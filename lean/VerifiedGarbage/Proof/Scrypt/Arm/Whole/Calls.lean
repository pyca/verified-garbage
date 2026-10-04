import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Proof.Scrypt.Arm.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
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
    let r := (stackArg s 0).toNat
    let pwR : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let saltR : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let bR : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat * 128⟩
    let vR : Region := ⟨State.addr (stackArg s 3), (stackArg s 4).toNat * 128⟩
    let scR : Region := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat * 128⟩
    let outR : Region := ⟨State.addr (stackArg s 7), (stackArg s 8).toNat⟩
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
    (stackArg s 1).toNat + (stackArg s 2).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 5).toNat + (stackArg s 6).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 32 ∧
    0 < r ∧ (stackArg s 2).toNat % r = 0 ∧ (stackArg s 4).toNat % r = 0 ∧
    Spec.Scrypt.valid ((stackArg s 4).toNat / r) r ((stackArg s 2).toNat / r) (stackArg s 8).toNat ∧
    (stackArg s 8).toNat ≤ (2 ^ 32 - 1) * 32 ∧ (stackArg s 6).toNat = r + 16
  post s s' :=
    let r := (stackArg s 0).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Scrypt.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) ((stackArg s 4).toNat / r) r
      ((stackArg s 2).toNat / r) (stackArg s 8).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (State.addr (stackArg s 7)) (stackArg s 8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧
    stackArg s₁ 5 = stackArg s₂ 5 ∧ stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧
    stackArg s₁ 8 = stackArg s₂ 8 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (s₁.gpr .r1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (State.addr (s₁.gpr .r2)) (s₁.gpr .r3).toNat) (stackArg s₁ 0).toNat
        ((stackArg s₁ 2).toNat / (stackArg s₁ 0).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (stackArg s₁ 0).toNat ((stackArg s₁ 4).toNat / (stackArg s₁ 0).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (s₂.gpr .r1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (State.addr (s₂.gpr .r2)) (s₂.gpr .r3).toNat) (stackArg s₂ 0).toNat
        ((stackArg s₂ 2).toNat / (stackArg s₂ 0).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (stackArg s₂ 0).toNat ((stackArg s₂ 4).toNat / (stackArg s₂ 0).toNat))

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

variable (L : Lay)

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

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (by decide))

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

/-- The stack the calls use misses every writable buffer. -/
theorem stk_in {r : Region} (hr : InBuf L r) : L.STK.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.kb.sub_right hs, h.kv.sub_right hs, h.kc.sub_right hs, h.ko.sub_right hs]

/-- Our stack arguments miss every writable buffer. -/
theorem args_in {r : Region} (hr : InBuf L r) : L.ARGS.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.ba.symm.sub_right hs, h.va.symm.sub_right hs, h.ca.symm.sub_right hs, h.oa.symm.sub_right hs]

/-- The password misses every writable buffer. -/
theorem pw_in {r : Region} (hr : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.pb.sub_right hs, h.pv.sub_right hs, h.pc.sub_right hs, h.po.sub_right hs]

/-- So does the salt. -/
theorem salt_in {r : Region} (hr : InBuf L r) : L.SALT.Disjoint r := by
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
    rw [toNat_addr, hs, Lay.SVA, BitVec.toNat_add, toNat_addr, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 128 * (L.r.toNat + 15)) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [addr_add (by omega), e]

/-- A word of our stack arguments, as `ldr t, [sp, #off]` reads it. -/
theorem arg_addr {k : Nat} (hk : k + 4 ≤ 36) :
    State.addr (L.sp + BitVec.ofNat 32 k) = State.addr L.sp + BitVec.ofNat 64 k :=
  addr_add (by have := h.nA; omega)

end Lay.Ok

/-! ## What the calls cannot change -/

/-- Our stack arguments, as `ldr t, [sp, #off]` reads them. -/
structure Args (L : Lay) (m : Mem) : Prop where
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
structure Saved (L : Lay) (g : Reg → BitVec 32) (m : Mem) : Prop where
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
theorem Args.frame {L : Lay} {m m' : Mem} {rs : List Region} (hk : Args L m)
    (hf : Frame rs m m') (ha : ∀ R ∈ rs, L.ARGS.Disjoint R) : Args L m' := by
  have ka : ∀ d, d + 4 ≤ 36 → m'.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 =
      m.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 := fun d hd =>
    hf.readW (r := L.ARGS) (Offset.contains_base _ (by omega) (by omega))
      (fun R hR => ha R hR) (by decide)
  exact ⟨(ka 0 (by omega)).trans hk.r, (ka 4 (by omega)).trans hk.b, (ka 8 (by omega)).trans hk.blen,
    (ka 12 (by omega)).trans hk.v, (ka 16 (by omega)).trans hk.vlen, (ka 20 (by omega)).trans hk.scr,
    (ka 24 (by omega)).trans hk.slen, (ka 28 (by omega)).trans hk.out, (ka 32 (by omega)).trans hk.ol⟩

/-- So does the save area. -/
theorem Saved.frame {L : Lay} {g : Reg → BitVec 32} {m m' : Mem} {rs : List Region} (hk : Saved L g m)
    (hf : Frame rs m m') (hs : ∀ R ∈ rs, L.SV.Disjoint R) : Saved L g m' := by
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
structure Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.sp
  r5 : t.gpr .r5 = L.b + BitVec.ofNat 32 (L.blen.toNat * 128)
  r6 : t.gpr .r6 = L.r
  r7 : t.gpr .r7 = L.scr
  r8 : t.gpr .r8 = L.pw
  r9 : t.gpr .r9 = L.pwl
  args : Args L t.mem
  saved : Saved L g t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.BB, L.VV, L.SC, L.OUT]

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
    stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, s.sp⟩

theorem lay_args (s : State) : (lay s).ARGS = ⟨stackArgAddr s 0, 36⟩ := by
  simp only [Lay.ARGS, lay, stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptArm.pre s) : (lay s).Ok := by
  obtain ⟨h40, h36, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea := lay_args s
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

variable {L : Lay} (h : L.Ok)
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
    apply BitVec.eq_of_toNat_eq; rw [toNat_addr, hb0]; rfl
  have ex : (State.addr L.sp - BitVec.ofNat 64 40).toNat = L.sp.toNat - 40 := by
    rw [Offset.toNat_sub_ofNat, toNat_addr]; omega
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
structure E (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.sp
  regs : ∀ r, r ≠ .r12 → r ≠ .lr → t.gpr r = g r
  args : Args L t.mem
  frame : Frame [L.SC] m₀ t.mem
  g0 : g .r0 = L.pw
  g1 : g .r1 = L.pwl
  g2 : g .r2 = L.salt
  g3 : g .r3 = L.sl

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem E.inArgs {t : State} (he : E L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 k)) 4 :=
  ⟨L.ARGS, by rw [he.rd, he.wr]; simp, by
    rw [he.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega)⟩

theorem E.inSc {t : State} (he : E L g m₀ t) {k : Nat} (hk : k + 4 ≤ L.slen.toNat * 128) :
    InRegions t.wr (State.addr L.scr + BitVec.ofNat 64 k) 4 :=
  ⟨L.SC, by rw [he.wr]; simp, Offset.contains_base _ hk (by omega)⟩

/-- The save area is apart from the first word of `scratch`, and from our stack arguments. -/
theorem sv_sc0 (hL : L.Ok) : L.SV.Disjoint ⟨State.addr L.scr, 4⟩ :=
  Offset.disjoint_base _ (by omega) (by have := hL.nc; have := hL.slen; omega)

/-- `E` after code that writes only `r12`, `lr` and `scratch`. -/
theorem E.upd {t t' : State} (he : E L g m₀ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r, r ≠ .r12 → r ≠ .lr → t'.gpr r = t.gpr r)
    (hf : Frame [L.SC] t.mem t'.mem) : E L g m₀ t' :=
  ⟨hrd.trans he.rd, hwr.trans he.wr, hsp.trans he.sp, fun r h₁ h₂ => (hg r h₁ h₂).trans (he.regs r h₁ h₂),
    he.args.frame hf (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact hL.ca.symm),
    he.frame.trans hf, he.g0, he.g1, he.g2, he.g3⟩

/-- `save1`: our return address into the first word of `scratch`. -/
theorem save1_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (hlr : t.gpr .lr = g .lr) :
    WP isa (.block save1) t fun t' => E L g m₀ t' ∧ t'.gpr .lr = g .lr ∧ t'.gpr .r12 = L.scr ∧
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
structure Saved8 (L : Lay) (g : Reg → BitVec 32) (m : Mem) : Prop where
  r4 : m.readW (L.SVA + BitVec.ofNat 64 0) 32 = g .r4
  r5 : m.readW (L.SVA + BitVec.ofNat 64 4) 32 = g .r5
  r6 : m.readW (L.SVA + BitVec.ofNat 64 8) 32 = g .r6
  r7 : m.readW (L.SVA + BitVec.ofNat 64 12) 32 = g .r7
  r8 : m.readW (L.SVA + BitVec.ofNat 64 16) 32 = g .r8
  r9 : m.readW (L.SVA + BitVec.ofNat 64 20) 32 = g .r9
  r10 : m.readW (L.SVA + BitVec.ofNat 64 24) 32 = g .r10
  r11 : m.readW (L.SVA + BitVec.ofNat 64 28) 32 = g .r11

theorem sva_k (L : Lay) (k : Nat) :
    L.SVA + BitVec.ofNat 64 k = State.addr L.scr + BitVec.ofNat 64 (128 * (L.r.toNat + 15) + k) := by
  rw [Lay.SVA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sv_con (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) : L.SC.Contains (L.SVA + BitVec.ofNat 64 k) 4 := by
  rw [sva_k]
  exact Offset.contains_base _ (by have := hL.slen; omega) (by have := hL.nc; have := hL.slen; omega)

theorem sv_in (hL : L.Ok) {t : State} (he : E L g m₀ t) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions t.wr (L.SVA + BitVec.ofNat 64 k) 4 :=
  ⟨L.SC, by rw [he.wr]; simp, sv_con hL hk⟩

/-- A store into the save area is within `scratch`. -/
theorem Frame.sv (hL : L.Ok) {m m' : Mem} (hf : Frame [L.SC] m m') {k : Nat} (hk : k + 4 ≤ 36)
    (v : BitVec 32) : Frame [L.SC] m (m'.writeW (L.SVA + BitVec.ofNat 64 k) v) :=
  hf.writeW (List.mem_singleton_self _) _ (sv_con hL hk)

/-- `save2`: our caller's `r4`–`r11` into the save area, whose address is
left in `r12`. -/
theorem save2_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (h12 : t.gpr .r12 = L.scr)
    (h0 : t.mem.readW (State.addr L.scr) 32 = g .lr) :
    WP isa (.block save2) t fun t' => E L g m₀ t' ∧ t'.gpr .r12 = L.svb ∧
      t'.mem.readW (State.addr L.scr) 32 = g .lr ∧ Saved8 L g t'.mem := by
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
  have w0 := sv_in hL he (k := 0) (by omega)
  have w4 := sv_in hL he (k := 4) (by omega)
  have w8 := sv_in hL he (k := 8) (by omega)
  have w12 := sv_in hL he (k := 12) (by omega)
  have w16 := sv_in hL he (k := 16) (by omega)
  have w20 := sv_in hL he (k := 20) (by omega)
  have w24 := sv_in hL he (k := 24) (by omega)
  have w28 := sv_in hL he (k := 28) (by omega)
  apply WP.of_runBlock
  simp only [save2, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Op2.eval, Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l0, a0, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false, h12, enc1920, s0, s4, s8, s12, s16, s20,
    s24, s28, w0, w4, w8, w12, w16, w20, w24, w28]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₁, h₂, ite_false]) ?_,
    trivial, ?_, ?_⟩
  · repeat (first | exact Frame.refl _ _ | refine Frame.sv hL ?_ (by omega) _)
  · simp (disch := decide) only [rd_dis (sv_sc0 hL).symm]; exact h0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := decide) only [rd_off, Mem.readW_writeW_self32] <;>
      exact he.regs _ (by decide) (by decide)

/-- `save3`: our return address into the save area. -/
theorem save3_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (h12 : t.gpr .r12 = L.svb)
    (h0 : t.mem.readW (State.addr L.scr) 32 = g .lr) (h8 : Saved8 L g t.mem) :
    WP isa (.block save3) t fun t' => E L g m₀ t' ∧ Saved L g t'.mem := by
  have l20 := he.inArgs hL (k := 20) (by omega)
  have a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.scr
  have r0 : InRegions (t.rd ++ t.wr) (State.addr L.scr) 4 :=
    ⟨L.SC, by rw [he.rd, he.wr]; simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := hL.slen17; omega⟩
  have s32 := hL.svb_addr (k := 32) (by omega)
  have w32 := sv_in hL he (k := 32) (by omega)
  apply WP.of_runBlock
  simp only [save3, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Nat.reduceLT, ite_true, l20, a20, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, BitVec.add_zero, r0, h0,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, h12, s32, w32]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₂, ite_false])
    (Frame.sv hL (Frame.refl _ _) (by omega) _), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [rd_off, Mem.readW_writeW_self32]
  exacts [h8.r4, h8.r5, h8.r6, h8.r7, h8.r8, h8.r9, h8.r10, h8.r11]

/-! ## The blocks between the calls -/

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, and the stack arguments to push,
`c = 1` and `scratch`. -/
structure PbkArgs (L : Lay) (salt sl out ol : BitVec 32) (t : State) : Prop where
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
theorem pbk1Args_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (hs : Saved L g t.mem) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r4 = L.b ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t' := by
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
    RegUpd.mem_setReg, RegUpd.sp_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, enc1, lsl7,
    sub_b]
  have r0 := (he.regs .r0 (by decide) (by decide)).trans he.g0
  have r1 := (he.regs .r1 (by decide) (by decide)).trans he.g1
  have r2 := (he.regs .r2 (by decide) (by decide)).trans he.g2
  have r3 := (he.regs .r3 (by decide) (by decide)).trans he.g3
  exact ⟨⟨he.rd, he.wr, he.sp, rfl, rfl, rfl, r0, r1, he.args, hs, Frame.mono he.frame (by simp)⟩,
    trivial, trivial, ⟨r0, r1, r2, r3, rfl, rfl, rfl, rfl⟩⟩

theorem Ctx.inArgs {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 k)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, by
    rw [hc.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega)⟩

theorem Ctx.arg {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) {v : BitVec 32}
    (h : t.mem.readW (State.addr L.sp + BitVec.ofNat 64 k) 32 = v) :
    t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 k)) 32 = v := by
  rw [hc.sp, hL.arg_addr hk]; exact h

/-- `Ctx` after code that writes only registers other than `r4`–`r9`. -/
theorem Ctx.regs {t t' : State} (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hg : ∀ r, r = .r5 ∨ r = .r6 ∨ r = .r7 ∨ r = .r8 ∨ r = .r9 → t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by simp)).trans hc.r5,
    (hg _ (by simp)).trans hc.r6, (hg _ (by simp)).trans hc.r7, (hg _ (by simp)).trans hc.r8,
    (hg _ (by simp)).trans hc.r9, by rw [hm]; exact hc.args, by rw [hm]; exact hc.saved,
    by rw [hm]; exact hc.frame⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : BitVec 32) (t : State) : Prop where
  r0 : t.gpr .r0 = cur
  r1 : t.gpr .r1 = L.r
  r2 : t.gpr .r2 = L.v
  r3 : t.gpr .r3 = L.vlen
  r12 : t.gpr .r12 = L.scr
  lr : t.gpr .lr = L.r + 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block romixArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r4 = t.gpr .r4 ∧
      RomixArgs L (t.gpr .r4) t' := by
  have l12 := hc.inArgs hL (k := 12) (by omega)
  have l16 := hc.inArgs hL (k := 16) (by omega)
  have a12 := hc.arg hL (k := 12) (by omega) hc.args.v
  have a16 := hc.arg hL (k := 16) (by omega) hc.args.vlen
  apply WP.of_runBlock
  simp only [romixArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, ite_true, l12, l16, a12, a16, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq,
    ite_false, enc2, hc.r6, hc.r7]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nextBlock_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r4 = t.gpr .r4 + BitVec.ofNat 32 (L.r.toNat * 128) ∧
      t'.z = (t.gpr .r4 + BitVec.ofNat 32 (L.r.toNat * 128) - (L.b + BitVec.ofNat 32 (L.blen.toNat * 128)) == 0) := by
  apply WP.of_runBlock
  simp only [nextBlock, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Nat.reduceLeDiff, and_self,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, hc.r6, lsl7, subFlags]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, trivial, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [hc.r5]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t' := by
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
    RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq, ite_false, enc1, lsl7, hc.r7, hc.r8, hc.r9]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem restore_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block restore) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = t.sp ∧
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
    ⟨L.SC, by rw [hc.rd, hc.wr]; simp, sv_con hL hk⟩
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
  simp only [restore, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq,
    ite_false, enc1920, hc.r6, hc.r7, s0, s4, s8, s12, s16, s20, s24, s28, s32, i0, i4, i8, i12, i16, i20,
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
    let out : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 3), 200 * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 24, 24⟩
    24 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32 ∧ s.rd = [pw, salt, args] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    stk.Disjoint pw ∧ stk.Disjoint salt ∧ stk.Disjoint out ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32 ∧ (stackArg s 3).toNat + 200 * 8 ≤ 2 ^ 32 ∧
    0 < (stackArg s 0).toNat ∧ (stackArg s 2).toNat ≤ (2 ^ 32 - 1) * 32
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac Spec.Hmac.sha256S
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) (stackArg s 0).toNat
      (stackArg s 2).toNat =
      some (Spec.Sha256.bytesAt s'.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3

theorem pbk_pre {s : State} (h : pbkA.pre s) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [pbkA, State.addr] at h
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
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (pbk_pre h)
  exact ⟨t, s', he, ha, pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkA.pre pbkA.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (pbk_pre h₁) (pbk_pre h₂) (pbk_pub hp) e₁ e₂

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

theorem p4_sp : (pushed fr4 s).sp = s.sp - BitVec.ofNat 32 16 := rfl

theorem p4_mem (h : 16 ≤ s.sp.toNat) :
    (pushed fr4 s).mem =
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
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) i = s.gpr fr4[i] := by
  have hn := s.sp.isLt
  have e : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' h
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, p4_sp]
  rw [p4_mem h, addr_add (by omega)]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [rd_off, Mem.readW_writeW_self32, Nat.mul_zero, Nat.mul_one,
      Nat.reduceMul] <;> rfl

theorem p4_a0 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 0 = s.gpr .r10 := p4_arg h (by decide)
theorem p4_a1 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 1 = s.gpr .r11 := p4_arg h (by decide)
theorem p4_a2 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 2 = s.gpr .r12 := p4_arg h (by decide)
theorem p4_a3 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 3 = s.gpr .lr := p4_arg h (by decide)

theorem p4_argAddr {rd wr : List Region} :
    stackArgAddr ((pushed fr4 s).callEntry.withRegions rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 16) := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, p4_sp, Nat.mul_zero]
  rw [BitVec.add_zero]

end

/-- A frame of four words, popped into `r12`, around a call of verified code
that uses at most 24 bytes of stack: the callee runs from the state after
the push, and the frame leaves `After4`. -/
theorem frame4_ok {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hst : armStack c ≤ 24) {s : State} (h40 : 40 ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed fr4 s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) ((pushed fr4 s).rd ++ (pushed fr4 s).wr))
    (hw : Covers wr (pushed fr4 s).wr) {Q : State → Prop}
    (hQ : ∀ s₂ : State, After4 s wr (popped .r12 16 s₂) →
      k.post ((pushed fr4 s).callEntry.withRegions rd wr) (s₂.withRegions rd wr) → Q (popped .r12 16 s₂)) :
    WP isa (.frame (.push fr4) (.call n c) (.pop .r12 16)) s Q := by
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega)
  refine WP.frame (rs := fr4) (r := .r12) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine WP.callF hv hpre hc hw (by rw [p4_sp, h16]; omega) fun s₂ hrd hwr hsp hf hcs hpost => ?_
  refine hQ s₂ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ hpost
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, p4_sp]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    have f₀ := pushed_frameA (rs := fr4) (s := s) (by simp only [List.length_cons, List.length_nil]; omega)
    refine Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      have := belowA_inner (sp := s.sp) (a := 16) (b := 40) (k := 0) (by omega) h40
      simpa using this
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [p4_sp]
        exact belowA_inner (k := 16) (by omega) h40

/-- Two runs of such a frame leak the same, if their stack pointers are the
same and the callee's preconditions and public data hold. -/
theorem frame4_rel {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧
      k.pre ((pushed fr4 s₁).callEntry.withRegions rd wr) ∧
      k.pre ((pushed fr4 s₂).callEntry.withRegions rd wr) ∧
      k.pub ((pushed fr4 s₁).callEntry.withRegions rd wr) ((pushed fr4 s₂).callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) ((pushed fr4 s₁).rd ++ (pushed fr4 s₁).wr) ∧ Covers wr (pushed fr4 s₁).wr ∧
      Covers (rd ++ wr) ((pushed fr4 s₂).rd ++ (pushed fr4 s₂).wr) ∧ Covers wr (pushed fr4 s₂).wr) :
    RelCT isa P (.frame (.push fr4) (.call n c) (.pop .r12 16)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h s₁ s₂ hp).1) (RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_)
  rw [Pbkdf2.Stream.Arm.push_eq (by decide) pa, Pbkdf2.Stream.Arm.push_eq (by decide) pb]
  exact (h s₁ s₂ hp).2

/-! ## The stack below the stack pointer -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

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
  rw [← addr_sub' hL.nS, toNat_addr, sub_toNat' hL.nS]

/-- Our frames' words and the callee's stack are in `STK`, apart. -/
theorem args16_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ L.STK := by
  rw [a16 hL]; exact Offset.sub_base _ (by omega)

theorem cstk_sub (hL : L.Ok) :
    Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩ L.STK := by
  rw [a40 hL]; exact Region.sub_prefix (by omega)

theorem cstk_args (hL : L.Ok) :
    Region.Disjoint ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩
      ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ := by
  rw [a40 hL, a16 hL]
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
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `scratch`'s first 1600 bytes, PBKDF2's working space. -/
abbrev scr1600 (L : Lay) : Region := ⟨State.addr L.scr, 200 * 8⟩

theorem scr_in (hL : L.Ok) : InBuf L (scr1600 L) :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega))))

theorem scr_sv (hL : L.Ok) : (scr1600 L).Disjoint L.SV :=
  (Offset.disjoint_base _ (by omega) (by have := hL.nc; have := hL.slen; omega)).symm

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt sl : BitVec 32) : List Region :=
  [L.PW, ⟨State.addr salt, sl.toNat⟩, ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩]
abbrev pbkWr (L : Lay) (out ol : BitVec 32) : List Region := [⟨State.addr out, ol.toNat⟩, scr1600 L]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt sl out ol : BitVec 32) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨State.addr salt, sl.toNat⟩ R
  ow : InBuf L ⟨State.addr out, ol.toNat⟩
  osv : Region.Disjoint ⟨State.addr out, ol.toNat⟩ L.SV
  so : Region.Disjoint ⟨State.addr salt, sl.toNat⟩ ⟨State.addr out, ol.toNat⟩
  sc : Region.Disjoint ⟨State.addr salt, sl.toNat⟩ (scr1600 L)
  oc : Region.Disjoint ⟨State.addr out, ol.toNat⟩ (scr1600 L)
  ks : L.STK.Disjoint ⟨State.addr salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 32
  no : out.toNat + ol.toNat ≤ 2 ^ 32
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkA.pre ((pushed fr4 t).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hS := hL.nS
  have hA := hL.nA
  have h16 : (L.sp - BitVec.ofNat 32 16).toNat = L.sp.toNat - 16 := sub_toNat' (by omega)
  have sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega
  simp only [pbkA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.withRegions_gpr,
    State.callEntry_sp, p4_sp, p4_argAddr, p4_a0 sp16, p4_a1 sp16, p4_a2 sp16, p4_a3 sp16,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12, ha.lr, h16]
  have sw := scr_in hL
  exact ⟨by omega, by omega, trivial, trivial, hL.pw_in hr.ow, hL.pw_in sw, hr.so, hr.sc, hr.oc,
    ((hL.stk_in hr.ow).sub_left (args16_sub hL)).symm, ((hL.stk_in sw).sub_left (args16_sub hL)).symm,
    hL.kp.sub_left (cstk_sub hL), hr.ks.sub_left (cstk_sub hL), (hL.stk_in hr.ow).sub_left (cstk_sub hL),
    (hL.stk_in sw).sub_left (cstk_sub hL), cstk_args hL, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

/-- A region within a writable buffer is within `wr`. -/
theorem InBuf.wr {r : Region} (h : InBuf L r) {t : State} (hc : Ctx L g m₀ t) :
    ∃ R ∈ t.wr, Within r R := by
  rw [hc.wr]
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩

theorem pbk_cov (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (hr : PbkRegions L salt sl out ol) :
    Covers (pbkRd L salt sl ++ pbkWr L out ol) ((pushed fr4 t).rd ++ (pushed fr4 t).wr) ∧
      Covers (pbkWr L out ol) (pushed fr4 t).wr := by
  have up : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed fr4 t).rd ++ (pushed fr4 t).wr,
      Within r R := fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  have upw : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed fr4 t).wr, Within r R :=
    fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.PW, by rw [pushed_rd, hc.rd]; simp, within_base _ (Nat.le_refl _)⟩
    · obtain ⟨R, hR, hw⟩ := hr.sw
      refine ⟨R, ?_, hw⟩
      rw [pushed_rd, pushed_wr, hc.rd, hc.wr]
      simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · refine ⟨⟨State.addr (t.sp - BitVec.ofNat 32 (4 * fr4.length)), 4 * fr4.length⟩,
        by rw [pushed_wr]; simp, 0, ?_, by simp⟩
      simp only [hc.sp, BitVec.add_zero]; rfl
    · exact up (hr.ow.wr hc)
    · exact up ((scr_in hL).wr hc)
  · simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact upw (hr.ow.wr hc)
    · exact upw ((scr_in hL).wr hc)

/-- The regions a call of PBKDF2 writes miss our stack arguments and the save area. -/
theorem pbk_apart (hL : L.Ok) {salt sl out ol : BitVec 32} (hr : PbkRegions L salt sl out ol) :
    ∀ R ∈ pbkWr L out ol ++ [L.STK], L.ARGS.Disjoint R ∧ L.SV.Disjoint R := by
  simp only [pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro R (rfl | rfl | rfl)
  · exact ⟨hL.args_in hr.ow, hr.osv.symm⟩
  · exact ⟨hL.args_in (scr_in hL), (scr_sv hL).symm⟩
  · exact ⟨(stk_args hL).symm, (stk_sv hL).symm⟩

theorem pbk_call {pbk : Prog isa}
    (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract Arm.abi 24))
    (hst : armStack pbk ≤ 24) (name : String) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    {salt sl out ol : BitVec 32} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (pbkCall name pbk) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r4 = t.gpr .r4 ∧
      Frame (pbkWr L out ol ++ [L.STK]) t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem (State.addr L.pw) L.pwl.toNat)
        (bytesAt t.mem (State.addr salt) sl.toNat) 1 ol.toNat =
        some (bytesAt t'.mem (State.addr out) ol.toNat) := by
  have hS := hL.nS
  obtain ⟨cov, covw⟩ := pbk_cov hL hc hr
  refine frame4_ok (pbk_correct hv) hst (by rw [hc.sp]; exact hS) (pbk_pre' hL hc ha hr) cov covw
    fun s₂ h4 hpost => ?_
  have hf : Frame (pbkWr L out ol ++ [L.STK]) t.mem (popped .r12 16 s₂).mem := by
    have := h4.frame; rwa [hc.sp, stk_eq hL] at this
  have ap := pbk_apart hL hr
  refine ⟨⟨h4.rd.trans hc.rd, h4.wr.trans hc.wr, h4.sp.trans hc.sp,
    (h4.cs .r5 (by decide) (by decide)).trans hc.r5, (h4.cs .r6 (by decide) (by decide)).trans hc.r6,
    (h4.cs .r7 (by decide) (by decide)).trans hc.r7, (h4.cs .r8 (by decide) (by decide)).trans hc.r8,
    (h4.cs .r9 (by decide) (by decide)).trans hc.r9, hc.args.frame hf fun R hR => (ap R hR).1,
    hc.saved.frame hf fun R hR => (ap R hR).2, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩,
    h4.cs .r4 (by decide) (by decide), hf, ?_⟩
  · simp only [pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, hs⟩ := hr.ow.sub
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
    · exact ⟨L.SC, by simp, Within.sub (within_base _ (by have := hL.slen17; omega))⟩
    · exact ⟨L.STK, by simp, fun _ h => h⟩
  · have h := hpost
    have sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega
    simp only [pbkA, Spec.Hmac.sha256S, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      pushed_gpr, p4_a0 sp16, p4_a1 sp16, p4_a2 sp16, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12] at h
    have f₀ := pushed_frameA (rs := fr4) (s := t) (by simp only [List.length_cons, List.length_nil]; omega)
    have d16 : ∀ {r : Region}, L.STK.Disjoint r →
        ∀ R ∈ [(⟨State.addr (t.sp - BitVec.ofNat 32 (4 * fr4.length)), 4 * fr4.length⟩ : Region)],
        r.Disjoint R := fun hd R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      rw [hc.sp]; exact (hd.sub_left (args16_sub hL)).symm
    have e₁ : Spec.Sha256.bytesAt (pushed fr4 t).mem (State.addr L.pw) L.pwl.toNat =
        bytesAt t.mem (State.addr L.pw) L.pwl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hL.kp) (by have := L.pwl.isLt; omega)
    have e₂ : Spec.Sha256.bytesAt (pushed fr4 t).mem (State.addr salt) sl.toNat =
        bytesAt t.mem (State.addr salt) sl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hr.ks) (by have := sl.isLt; omega)
    rw [e₁, e₂] at h
    exact h

end

/-! ## ROMix -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- Block `i` of `b`, as the code computes it, and its address. -/
abbrev blkAt (L : Lay) (i : Nat) : BitVec 32 := L.b + BitVec.ofNat 32 (128 * L.r.toNat * i)
abbrev blkA (L : Lay) (i : Nat) : Addr := State.addr L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem addr_blk (hL : L.Ok) {i : Nat} (hi : i < L.pp) : State.addr (blkAt L i) = blkA L i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  exact addr_add (by omega)

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkA L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkA L i, L.r.toNat * 128⟩, ⟨State.addr L.v, L.vlen.toNat * 128⟩, ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩]

/-- ROMix's stack arguments. -/
abbrev romixRd (L : Lay) : List Region := [⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩]

theorem r2 (hL : L.Ok) : (L.r + 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  rw [BitVec.toNat_add, show (2 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem args8_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩ L.STK := by
  rw [addr_sub' (by have := hL.nS; omega), Offset.sub_ofNat_eq _ (by omega : 8 ≤ 40)]
  exact Offset.sub_base _ (by omega)

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    Proof.Scrypt.roMixArm.pre ((pushed [.r12, .lr] t).callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have hS := hL.nS
  have hA := hL.nA
  have s8 : 8 ≤ t.sp.toNat := by rw [hc.sp]; omega
  have hb := blk_in hL hi
  have hv : InBuf L ⟨State.addr L.v, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))
  have h8 : (L.sp - BitVec.ofNat 32 8).toNat = L.sp.toNat - 8 := sub_toNat' (by omega)
  simp only [Proof.Scrypt.roMixArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.withRegions_gpr, State.callEntry_sp, pushed_sp, p2_argAddr, p2_arg0 s8, p2_arg1,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r12, ha.lr, r2 hL, addr_blk hL hi]
  have kb := Within.sub (within_off (State.addr L.b) (blk_le hL hi))
  have ks := Within.sub (within_base (State.addr L.scr) (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  have := blk_le hL hi; have := hL.nb; have := hL.nv; have := hL.nc; have := hL.slen; have := hL.blen_lt; have := hL.rpos
  have tb : (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * L.r.toNat * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    (hL.stk_in hb).sub_left (args8_sub hL), (hL.stk_in hv).sub_left (args8_sub hL),
    (hL.stk_in hs).sub_left (args8_sub hL), by rw [tb]; omega, by omega, by omega,
    by simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, h8]; omega, hL.rpos,
    hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_cov (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) :
    Covers (romixRd L ++ romixWr L i) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (romixWr L i) (pushed [.r12, .lr] t).wr := by
  have upw : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed [.r12, .lr] t).wr, Within r R :=
    fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  have hw := romix_wsub hL hi
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => upw ((hw r hr).wr hc)⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [romixRd, List.mem_singleton] at hr; subst hr
    refine ⟨⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩,
      by rw [pushed_wr]; simp, 0, ?_, by simp⟩
    simp only [hc.sp, BitVec.add_zero]; rfl
  · obtain ⟨R, hR, hw'⟩ := upw ((hw r hr).wr hc)
    exact ⟨R, List.mem_append_right _ hR, hw'⟩

theorem roMix_stack : armStack Impl.Scrypt.Arm.roMix ≤ 16 := by lit_decide

/-- The stack `frame2_ok` lets a call change is in `STK`. -/
theorem stk_sub {t : State} (hc : Ctx L g m₀ t) : Region.Sub (stk t) L.STK := by
  simp only [stk, hc.sp]
  show Region.Sub ⟨State.addr L.sp - BitVec.ofNat 64 24, 24⟩ ⟨State.addr L.sp - BitVec.ofNat 64 40, 40⟩
  rw [Offset.sub_ofNat_eq _ (by omega : 24 ≤ 40)]
  exact Offset.sub_base _ (by omega)

/-- The regions a call of ROMix writes miss our stack arguments and the save area. -/
theorem romix_apart (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ R ∈ romixWr L i ++ [L.STK], L.ARGS.Disjoint R ∧ L.SV.Disjoint R := by
  have hw := romix_wsub hL hi
  intro R hR
  rcases List.mem_append.mp hR with hR | hR
  · refine ⟨hL.args_in (hw R hR), ?_⟩
    simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hL.bc.symm.sub_left hL.sv_sc).sub_right (Within.sub (within_off _ (blk_le hL hi)))
    · exact hL.vc.symm.sub_left hL.sv_sc
    · exact (Offset.disjoint_base _ (by have := hL.slen; omega) (by have := hL.nc; have := hL.slen; omega))
  · simp only [List.mem_singleton] at hR; subst hR
    exact ⟨(stk_args hL).symm, (stk_sv hL).symm⟩

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r4 = t.gpr .r4 ∧
        Frame (romixWr L i ++ [L.STK]) t.mem t'.mem ∧
        bytesAt t'.mem (blkA L i) (128 * L.r.toNat) =
          Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkA L i) (128 * L.r.toNat)) := by
  have hS := hL.nS
  obtain ⟨cov, covw⟩ := romix_cov hL hc hi
  refine frame2_ok (by decide) (by decide) RoMix.roMix_correct roMix_stack (by rw [hc.sp]; omega)
    (romix_pre hL hc hi ha) cov covw fun s₂ h2 hpost => ?_
  have hf : Frame (romixWr L i ++ [L.STK]) t.mem (popped .r12 8 s₂).mem :=
    Frame.sub h2.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.STK, by simp, stk_sub hc⟩
  have ap := romix_apart hL hi
  refine ⟨⟨h2.rd.trans hc.rd, h2.wr.trans hc.wr, h2.sp.trans hc.sp,
    (h2.cs .r5 (by decide) (by decide)).trans hc.r5, (h2.cs .r6 (by decide) (by decide)).trans hc.r6,
    (h2.cs .r7 (by decide) (by decide)).trans hc.r7, (h2.cs .r8 (by decide) (by decide)).trans hc.r8,
    (h2.cs .r9 (by decide) (by decide)).trans hc.r9, hc.args.frame hf fun R hR => (ap R hR).1,
    hc.saved.frame hf fun R hR => (ap R hR).2, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩,
    h2.cs .r4 (by decide) (by decide), hf, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨R, hR, hs⟩ := (romix_wsub hL hi r hr).sub
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
      addr_blk hL hi] at h
    have f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
      (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega)
    have e : Spec.Scrypt.bytesAt (pushed [.r12, .lr] t).mem (blkA L i) (128 * L.r.toNat) =
        bytesAt t.mem (blkA L i) (128 * L.r.toNat) :=
      Memory.frame_bytesAt f₀ (fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        have hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
            4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
          rw [hc.sp]; exact args8_sub hL
        rw [Nat.mul_comm]
        exact ((hL.stk_in (blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega)
    rw [e] at h
    exact h

end

end VG.Proof.Scrypt.Arm.Whole
