module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Contract
import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Scrypt.Arm.Lit
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
meta import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
meta import VerifiedGarbage.Proof.Scrypt.Whole
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Scrypt.Arm.Lit
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
public import VerifiedGarbage.Impl.Scrypt.Arm.Scrypt
public import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Impl.Scrypt.Arm.Scrypt
meta import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Frame

/-! ### `Scrypt.Arm.Whole.Calls`, which only this module used -/

section

@[expose] public section

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

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega_arith

/-- The save area is in `scratch`. -/
theorem sv_sc : Region.Sub L.SV L.SC := by
  have := h.slen
  exact Offset.sub_base _ (by rw [this]; omega_arith)

/-- The save area as the code computes it. -/
theorem svb_toNat : L.svb.toNat = L.scr.toNat + 128 * (L.r.toNat + 15) := by
  have := h.nc; have := h.slen; have := h.rpos
  obtain e : (L.r <<< 7).toNat = L.r.toNat * 128 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [Lay.svb, BitVec.toNat_add, e, show (1920 : BitVec 32).toNat = 1920 from rfl]
  rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem svb_addr {k : Nat} (hk : k < 36) :
    State.addr (L.svb + BitVec.ofNat 32 k) = L.SVA + BitVec.ofNat 64 k := by
  have := h.nc; have := h.slen; have hs := h.svb_toNat
  obtain e : State.addr L.svb = L.SVA := by
    apply BitVec.eq_of_toNat_eq
    have := L.scr.isLt
    rw [toNat_addr, hs, Lay.SVA, BitVec.toNat_add, toNat_addr, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 128 * (L.r.toNat + 15)) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  rw [addr_add (by omega_arith), e]

/-- A word of our stack arguments, as `ldr t, [sp, #off]` reads it. -/
theorem arg_addr {k : Nat} (hk : k + 4 ≤ 36) :
    State.addr (L.sp + BitVec.ofNat 32 k) = State.addr L.sp + BitVec.ofNat 64 k :=
  addr_add (by have := h.nA; omega_arith)

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
  obtain ka : ∀ d, d + 4 ≤ 36 → m'.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 =
      m.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 := fun d hd =>
    hf.readW (r := L.ARGS) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun R hR => ha R hR) (by decide)
  exact ⟨(ka 0 (by omega_arith)).trans hk.r, (ka 4 (by omega_arith)).trans hk.b, (ka 8 (by omega_arith)).trans hk.blen,
    (ka 12 (by omega_arith)).trans hk.v, (ka 16 (by omega_arith)).trans hk.vlen, (ka 20 (by omega_arith)).trans hk.scr,
    (ka 24 (by omega_arith)).trans hk.slen, (ka 28 (by omega_arith)).trans hk.out, (ka 32 (by omega_arith)).trans hk.ol⟩

/-- So does the save area. -/
theorem Saved.frame {L : Lay} {g : Reg → BitVec 32} {m m' : Mem} {rs : List Region} (hk : Saved L g m)
    (hf : Frame rs m m') (hs : ∀ R ∈ rs, L.SV.Disjoint R) : Saved L g m' := by
  obtain ks : ∀ d, d + 4 ≤ 36 → m'.readW (L.SVA + BitVec.ofNat 64 d) 32 =
      m.readW (L.SVA + BitVec.ofNat 64 d) 32 := fun d hd =>
    hf.readW (r := L.SV) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun R hR => hs R hR) (by decide)
  exact ⟨(ks 0 (by omega_arith)).trans hk.r4, (ks 4 (by omega_arith)).trans hk.r5, (ks 8 (by omega_arith)).trans hk.r6,
    (ks 12 (by omega_arith)).trans hk.r7, (ks 16 (by omega_arith)).trans hk.r8, (ks 20 (by omega_arith)).trans hk.r9,
    (ks 24 (by omega_arith)).trans hk.r10, (ks 28 (by omega_arith)).trans hk.r11, (ks 32 (by omega_arith)).trans hk.lr⟩

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
  obtain ea := lay_args s
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
  obtain hnb := h.nb; have hS := h.nS; have hA := h.nA
  refine Nat.lt_of_not_le fun hge => ?_
  obtain hb0 : L.b.toNat = 0 := by omega_arith
  obtain e : L.blen.toNat * 128 = 2 ^ 32 := by omega_arith
  obtain eb : State.addr L.b = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_addr, hb0]; rfl
  obtain ex : (State.addr L.sp - BitVec.ofNat 64 40).toNat = L.sp.toNat - 40 := by
    rw [Offset.toNat_sub_ofNat, toNat_addr]; omega_arith
  apply h.kb (State.addr L.sp - BitVec.ofNat 64 40)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · have z : ∀ x : BitVec 64, x - State.addr L.b = x := fun x => by rw [eb]; exact BitVec.sub_zero x
    simp only [Region.Contains, z, e, ex]; omega_arith

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 32 := by have := h.blen_lt; have := h.r_le; omega_arith

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
  omega_arith

end Lay.Ok

/-! ## Words at offsets -/

/-- A word read back past a store of another at a different offset. -/
theorem rd_off {P : Addr} {m : Mem} {x y : Nat} {v : BitVec 32} (h : x + 4 ≤ y ∨ y + 4 ≤ x)
    (hx : x + 4 ≤ 64) (hy : y + 4 ≤ 64) :
    (m.writeW (P + BitVec.ofNat 64 y) v).readW (P + BitVec.ofNat 64 x) 32 =
      m.readW (P + BitVec.ofNat 64 x) 32 :=
  Mem.readW_writeW_sep (Offset.sep P h (by omega_arith) (by omega_arith)) (by decide)

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
    rw [he.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega_arith)⟩

theorem E.inSc {t : State} (he : E L g m₀ t) {k : Nat} (hk : k + 4 ≤ L.slen.toNat * 128) :
    InRegions t.wr (State.addr L.scr + BitVec.ofNat 64 k) 4 :=
  ⟨L.SC, by rw [he.wr]; simp, Offset.contains_base _ hk (by omega_arith)⟩

/-- The save area is apart from the first word of `scratch`, and from our stack arguments. -/
theorem sv_sc0 (hL : L.Ok) : L.SV.Disjoint ⟨State.addr L.scr, 4⟩ :=
  Offset.disjoint_base _ (by omega_arith) (by have := hL.nc; have := hL.slen; omega_arith)

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
  obtain l20 := he.inArgs hL (k := 20) (by omega_arith)
  obtain w0 := he.inSc (k := 0) (by have := hL.slen17; omega_arith)
  rw [BitVec.add_zero] at w0
  obtain a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega_arith)]; exact he.args.scr
  apply WP.of_runBlock
  simp only [save1, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Nat.reduceLT, ite_true, l20, a20, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, BitVec.add_zero, w0, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, reduceCtorEq, ite_false, hlr]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ _ => by simp only [RegUpd.gpr_setReg, h₁, ite_false]) ?_,
    trivial, trivial, Mem.readW_writeW_self32 _ _ _⟩
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := hL.slen17; omega_arith)

/-- A word read back past a store into the save area, from outside it. -/
theorem rd_dis {a P : Addr} {m : Mem} {y : Nat} {v : BitVec 32} (hd : Region.Disjoint ⟨a, 4⟩ ⟨P, 36⟩)
    (hy : y + 4 ≤ 36) : (m.writeW (P + BitVec.ofNat 64 y) v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (Region.Disjoint.sep hd (Region.contains_self _ _)
    (Offset.contains_base _ hy (by omega_arith))) (by decide)

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
  exact Offset.contains_base _ (by have := hL.slen; omega_arith) (by have := hL.nc; have := hL.slen; omega_arith)

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
  obtain l0 := he.inArgs hL (k := 0) (by omega_arith)
  obtain a0 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 0)) 32 = L.r := by
    rw [he.sp, hL.arg_addr (by omega_arith)]; exact he.args.r
  obtain s0 := hL.svb_addr (k := 0) (by omega_arith)
  obtain s4 := hL.svb_addr (k := 4) (by omega_arith)
  obtain s8 := hL.svb_addr (k := 8) (by omega_arith)
  obtain s12 := hL.svb_addr (k := 12) (by omega_arith)
  obtain s16 := hL.svb_addr (k := 16) (by omega_arith)
  obtain s20 := hL.svb_addr (k := 20) (by omega_arith)
  obtain s24 := hL.svb_addr (k := 24) (by omega_arith)
  obtain s28 := hL.svb_addr (k := 28) (by omega_arith)
  obtain w0 := sv_in hL he (k := 0) (by omega_arith)
  obtain w4 := sv_in hL he (k := 4) (by omega_arith)
  obtain w8 := sv_in hL he (k := 8) (by omega_arith)
  obtain w12 := sv_in hL he (k := 12) (by omega_arith)
  obtain w16 := sv_in hL he (k := 16) (by omega_arith)
  obtain w20 := sv_in hL he (k := 20) (by omega_arith)
  obtain w24 := sv_in hL he (k := 24) (by omega_arith)
  obtain w28 := sv_in hL he (k := 28) (by omega_arith)
  apply WP.of_runBlock
  simp only [save2, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Op2.eval, Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l0, a0, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false, h12, enc1920, s0, s4, s8, s12, s16, s20,
    s24, s28, w0, w4, w8, w12, w16, w20, w24, w28]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₁, h₂, ite_false]) ?_,
    trivial, ?_, ?_⟩
  · repeat (first | exact Frame.refl _ _ | refine Frame.sv hL ?_ (by omega_arith) _)
  · simp (disch := decide) only [rd_dis (sv_sc0 hL).symm]; exact h0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := decide) only [rd_off, Mem.readW_writeW_self32] <;>
      exact he.regs _ (by decide) (by decide)

/-- `save3`: our return address into the save area. -/
theorem save3_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (h12 : t.gpr .r12 = L.svb)
    (h0 : t.mem.readW (State.addr L.scr) 32 = g .lr) (h8 : Saved8 L g t.mem) :
    WP isa (.block save3) t fun t' => E L g m₀ t' ∧ Saved L g t'.mem := by
  obtain l20 := he.inArgs hL (k := 20) (by omega_arith)
  obtain a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega_arith)]; exact he.args.scr
  obtain r0 : InRegions (t.rd ++ t.wr) (State.addr L.scr) 4 :=
    ⟨L.SC, by rw [he.rd, he.wr]; simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := hL.slen17; omega_arith⟩
  obtain s32 := hL.svb_addr (k := 32) (by omega_arith)
  obtain w32 := sv_in hL he (k := 32) (by omega_arith)
  apply WP.of_runBlock
  simp only [save3, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Nat.reduceLT, ite_true, l20, a20, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, BitVec.add_zero, r0, h0,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, h12, s32, w32]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₂, ite_false])
    (Frame.sv hL (Frame.refl _ _) (by omega_arith) _), ?_⟩
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
  obtain l0 := he.inArgs hL (k := 0) (by omega_arith)
  obtain l4 := he.inArgs hL (k := 4) (by omega_arith)
  obtain l8 := he.inArgs hL (k := 8) (by omega_arith)
  obtain l20 := he.inArgs hL (k := 20) (by omega_arith)
  obtain a0 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 0)) 32 = L.r := by
    rw [he.sp, hL.arg_addr (by omega_arith)]; exact he.args.r
  obtain a4 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 4)) 32 = L.b := by
    rw [he.sp, hL.arg_addr (by omega_arith)]; exact he.args.b
  obtain a8 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 8)) 32 = L.blen := by
    rw [he.sp, hL.arg_addr (by omega_arith)]; exact he.args.blen
  obtain a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega_arith)]; exact he.args.scr
  apply WP.of_runBlock
  simp only [pbk1Args, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l0, l4, l8, l20, a0, a4, a8, a20, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.sp_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, enc1, lsl7,
    sub_b]
  obtain r0 := (he.regs .r0 (by decide) (by decide)).trans he.g0
  obtain r1 := (he.regs .r1 (by decide) (by decide)).trans he.g1
  obtain r2 := (he.regs .r2 (by decide) (by decide)).trans he.g2
  obtain r3 := (he.regs .r3 (by decide) (by decide)).trans he.g3
  exact ⟨⟨he.rd, he.wr, he.sp, rfl, rfl, rfl, r0, r1, he.args, hs, Frame.mono he.frame (by simp)⟩,
    trivial, trivial, ⟨r0, r1, r2, r3, rfl, rfl, rfl, rfl⟩⟩

theorem Ctx.inArgs {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 k)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, by
    rw [hc.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega_arith)⟩

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
  obtain l12 := hc.inArgs hL (k := 12) (by omega_arith)
  obtain l16 := hc.inArgs hL (k := 16) (by omega_arith)
  obtain a12 := hc.arg hL (k := 12) (by omega_arith) hc.args.v
  obtain a16 := hc.arg hL (k := 16) (by omega_arith) hc.args.vlen
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
  obtain l4 := hc.inArgs hL (k := 4) (by omega_arith)
  obtain l8 := hc.inArgs hL (k := 8) (by omega_arith)
  obtain l28 := hc.inArgs hL (k := 28) (by omega_arith)
  obtain l32 := hc.inArgs hL (k := 32) (by omega_arith)
  obtain a4 := hc.arg hL (k := 4) (by omega_arith) hc.args.b
  obtain a8 := hc.arg hL (k := 8) (by omega_arith) hc.args.blen
  obtain a28 := hc.arg hL (k := 28) (by omega_arith) hc.args.out
  obtain a32 := hc.arg hL (k := 32) (by omega_arith) hc.args.ol
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
  obtain s0 := hL.svb_addr (k := 0) (by omega_arith)
  obtain s4 := hL.svb_addr (k := 4) (by omega_arith)
  obtain s8 := hL.svb_addr (k := 8) (by omega_arith)
  obtain s12 := hL.svb_addr (k := 12) (by omega_arith)
  obtain s16 := hL.svb_addr (k := 16) (by omega_arith)
  obtain s20 := hL.svb_addr (k := 20) (by omega_arith)
  obtain s24 := hL.svb_addr (k := 24) (by omega_arith)
  obtain s28 := hL.svb_addr (k := 28) (by omega_arith)
  obtain s32 := hL.svb_addr (k := 32) (by omega_arith)
  obtain i : ∀ k, k + 4 ≤ 36 → InRegions (t.rd ++ t.wr) (L.SVA + BitVec.ofNat 64 k) 4 := fun k hk =>
    ⟨L.SC, by rw [hc.rd, hc.wr]; simp, sv_con hL hk⟩
  obtain i0 := i 0 (by omega_arith)
  obtain i4 := i 4 (by omega_arith)
  obtain i8 := i 8 (by omega_arith)
  obtain i12 := i 12 (by omega_arith)
  obtain i16 := i 16 (by omega_arith)
  obtain i20 := i 20 (by omega_arith)
  obtain i24 := i 24 (by omega_arith)
  obtain i28 := i 28 (by omega_arith)
  obtain i32 := i 32 (by omega_arith)
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
`(Proof.Pbkdf2.Instance.pbkdf2ScratchContract VG.Spec.Hmac.sha256I)`; its caller works with the same contract
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
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24).pre s := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [pbkA, State.addr] at h
  sig_split h
  sig_and_intros
  all_goals try simp only [State.addr]
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega_arith

theorem pbk_post {s s' : State} (h : (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24).post s s') :
    pbkA.post s s' := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkA.pub s₁ s₂) :
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24).pub s₁ s₂ := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact h

variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24))
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
  obtain e : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' h
  show storeWords s.mem (s.sp - BitVec.ofNat 32 16) [s.gpr .r10, s.gpr .r11, s.gpr .r12, s.gpr .lr] = _
  simp only [storeWords]
  rw [BitVec.add_zero, BitVec.add_assoc, BitVec.add_assoc,
    show (4 : BitVec 32) + 4 = BitVec.ofNat 32 8 from rfl,
    show (BitVec.ofNat 32 8 : BitVec 32) + 4 = BitVec.ofNat 32 12 from rfl,
    show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
    addr_add (by omega_arith), addr_add (by omega_arith), addr_add (by omega_arith)]

theorem p4_arg (h : 16 ≤ s.sp.toNat) {rd wr : List Region} {i : Nat} (hi : i < 4) :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) i = s.gpr fr4[i] := by
  have hn := s.sp.isLt
  obtain e : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' h
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, p4_sp]
  rw [p4_mem h, addr_add (by omega_arith)]
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
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
the push, and the frame leaves `After4`, whatever memory `m` that differs from
the callee's only in `belowA s.sp 40` (where the released frame is), and
whatever unknowns `u`, the pop leaves. -/
theorem frame4_ok {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hst : armStack c ≤ 24) {s : State} (h40 : 40 ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed fr4 s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) ((pushed fr4 s).rd ++ (pushed fr4 s).wr))
    (hw : Covers wr (pushed fr4 s).wr) {Q : State → Prop}
    (hQ : ∀ (s₂ : State) (m : Mem) (u : Nat → BitVec 32), Frame [belowA s.sp 40] s₂.mem m →
      After4 s wr { popped .r12 16 s₂ with mem := m, unknowns := u } →
      k.post ((pushed fr4 s).callEntry.withRegions rd wr) (s₂.withRegions rd wr) →
        Q { popped .r12 16 s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.push fr4) (.call n c) (.pop .r12 16)) s Q := by
  obtain h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega_arith)
  refine WP.frame (rs := fr4) (r := .r12) (by decide) (by simp only [List.length_cons, List.length_nil]; omega_arith)
    (by simp only [List.length_cons, List.length_nil]; omega_arith) ?_
  refine WP.callF hv hpre hc hw (by rw [p4_sp, h16]; omega_arith) fun s₂ hrd hwr hsp hf hcs hpost mL uL hfl => ?_
  obtain hflS : Frame [belowA s.sp 40] s₂.mem mL := hfl.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]
    have := belowA_inner (sp := s.sp) (a := 16) (b := 40) (k := 0) (by omega_arith) h40
    simpa using this⟩
  refine hQ s₂ mL uL hflS ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ hpost
  · dsimp only; rw [popped_rd, hrd, pushed_rd]
  · dsimp only; rw [popped_wr, hwr, pushed_wr]; rfl
  · dsimp only; rw [popped_sp, hsp, p4_sp]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    dsimp only; rw [popped_gpr this, hcs r hr hl, pushed_gpr]
  · dsimp only
    obtain f₀ := pushed_frameA (rs := fr4) (s := s) (by simp only [List.length_cons, List.length_nil]; omega_arith)
    refine Frame.trans (Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub hf fun r hr => ?_))
      (Frame.sub hflS fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      have := belowA_inner (sp := s.sp) (a := 16) (b := 40) (k := 0) (by omega_arith) h40
      simpa using this
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [p4_sp]
        exact belowA_inner (k := 16) (by omega_arith) h40

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
  rw [addr_sub' (by have := hL.nS; omega_arith), Offset.sub_ofNat_eq _ (by omega_arith : 16 ≤ 40)]

theorem a40 (hL : L.Ok) :
    State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24 = State.addr L.sp - BitVec.ofNat 64 40 := by
  rw [addr_sub' (by have := hL.nS; omega_arith), BitVec.sub_sub, BitVec.ofNat_add_ofNat]

/-- Our frames' words and the callee's stack are in `STK`, apart. -/
theorem args16_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ L.STK := by
  rw [a16 hL]; exact Offset.sub_base _ (by omega_arith)

theorem cstk_sub (hL : L.Ok) :
    Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩ L.STK := by
  rw [a40 hL]; exact Region.sub_prefix (by omega_arith)

theorem cstk_args (hL : L.Ok) :
    Region.Disjoint ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩
      ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ := by
  rw [a40 hL, a16 hL]
  exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).symm

/-- `STK` is apart from our stack arguments. -/
theorem stk_args (hL : L.Ok) : L.STK.Disjoint L.ARGS := by
  have := hL.nA; have := hL.nS
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  obtain e : x - State.addr L.sp = (x - (State.addr L.sp - BitVec.ofNat 64 40)) - BitVec.ofNat 64 40 := by
    rw [BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [e, Offset.toNat_sub_ofNat] at h₂
  have := (x - (State.addr L.sp - BitVec.ofNat 64 40)).isLt
  omega_arith

/-- `STK` is apart from the save area. -/
theorem stk_sv (hL : L.Ok) : L.STK.Disjoint L.SV := hL.kc.sub_right hL.sv_sc

end

/-! ## PBKDF2 -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `scratch`'s first 1600 bytes, PBKDF2's working space. -/
abbrev scr1600 (L : Lay) : Region := ⟨State.addr L.scr, 200 * 8⟩

theorem scr_in (hL : L.Ok) : InBuf L (scr1600 L) :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega_arith))))

theorem scr_sv (hL : L.Ok) : (scr1600 L).Disjoint L.SV :=
  (Offset.disjoint_base _ (by omega_arith) (by have := hL.nc; have := hL.slen; omega_arith)).symm

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
  obtain h16 : (L.sp - BitVec.ofNat 32 16).toNat = L.sp.toNat - 16 := sub_toNat' (by omega_arith)
  obtain sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega_arith
  simp only [pbkA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.withRegions_gpr,
    State.callEntry_sp, p4_sp, p4_argAddr, p4_a0 sp16, p4_a1 sp16, p4_a2 sp16, p4_a3 sp16,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12, ha.lr, h16]
  obtain sw := scr_in hL
  exact ⟨by omega_arith, by omega_arith, trivial, trivial, hL.pw_in hr.ow, hL.pw_in sw, hr.so, hr.sc, hr.oc,
    ((hL.stk_in hr.ow).sub_left (args16_sub hL)).symm, ((hL.stk_in sw).sub_left (args16_sub hL)).symm,
    hL.kp.sub_left (cstk_sub hL), hr.ks.sub_left (cstk_sub hL), (hL.stk_in hr.ow).sub_left (cstk_sub hL),
    (hL.stk_in sw).sub_left (cstk_sub hL), cstk_args hL, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega_arith, by decide, hr.ol⟩

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
  obtain up : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed fr4 t).rd ++ (pushed fr4 t).wr,
      Within r R := fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  obtain upw : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed fr4 t).wr, Within r R :=
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
    (hv : Verified Arm.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24))
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
    fun s₂ mL uL hfl h4 hpost => ?_
  obtain hf : Frame (pbkWr L out ol ++ [L.STK]) t.mem mL := by
    have := h4.frame; rwa [hc.sp, stk_eq hL] at this
  rw [hc.sp, stk_eq hL] at hfl
  obtain ap := pbk_apart hL hr
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
    · exact ⟨L.SC, by simp, Within.sub (within_base _ (by have := hL.slen17; omega_arith))⟩
    · exact ⟨L.STK, by simp, fun _ h => h⟩
  · have h := hpost
    obtain sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega_arith
    simp only [pbkA, Spec.Hmac.sha256S, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      pushed_gpr, p4_a0 sp16, p4_a1 sp16, p4_a2 sp16, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12] at h
    obtain f₀ := pushed_frameA (rs := fr4) (s := t) (by simp only [List.length_cons, List.length_nil]; omega_arith)
    obtain d16 : ∀ {r : Region}, L.STK.Disjoint r →
        ∀ R ∈ [(⟨State.addr (t.sp - BitVec.ofNat 32 (4 * fr4.length)), 4 * fr4.length⟩ : Region)],
        r.Disjoint R := fun hd R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      rw [hc.sp]; exact (hd.sub_left (args16_sub hL)).symm
    obtain e₁ : Spec.Sha256.bytesAt (pushed fr4 t).mem (State.addr L.pw) L.pwl.toNat =
        bytesAt t.mem (State.addr L.pw) L.pwl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hL.kp) (by have := L.pwl.isLt; omega_arith)
    obtain e₂ : Spec.Sha256.bytesAt (pushed fr4 t).mem (State.addr salt) sl.toNat =
        bytesAt t.mem (State.addr salt) sl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hr.ks) (by have := sl.isLt; omega_arith)
    rw [e₁, e₂] at h
    -- The output is apart from the released frame.
    dsimp only
    rw [Memory.frame_bytesAt hfl (fun q hq => by
      rw [List.mem_singleton.mp hq]; exact (hL.stk_in hr.ow).symm) (by have := hr.no; omega_arith)]
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
  exact addr_add (by omega_arith)

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkA L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkA L i, L.r.toNat * 128⟩, ⟨State.addr L.v, L.vlen.toNat * 128⟩, ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩]

/-- ROMix's stack arguments. -/
abbrev romixRd (L : Lay) : List Region := [⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩]

theorem r2 (hL : L.Ok) : (L.r + 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  rw [BitVec.toNat_add, show (2 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega_arith)]

theorem args8_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩ L.STK := by
  rw [addr_sub' (by have := hL.nS; omega_arith), Offset.sub_ofNat_eq _ (by omega_arith : 8 ≤ 40)]
  exact Offset.sub_base _ (by omega_arith)

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith))))

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    Proof.Scrypt.roMixArm.pre ((pushed [.r12, .lr] t).callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have hS := hL.nS
  have hA := hL.nA
  obtain s8 : 8 ≤ t.sp.toNat := by rw [hc.sp]; omega_arith
  obtain hb := blk_in hL hi
  obtain hv : InBuf L ⟨State.addr L.v, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  obtain hs : InBuf L ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith))))
  obtain h8 : (L.sp - BitVec.ofNat 32 8).toNat = L.sp.toNat - 8 := sub_toNat' (by omega_arith)
  simp only [Proof.Scrypt.roMixArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.withRegions_gpr, State.callEntry_sp, pushed_sp, p2_argAddr, p2_arg0 s8, p2_arg1,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r12, ha.lr, r2 hL, addr_blk hL hi]
  obtain kb := Within.sub (within_off (State.addr L.b) (blk_le hL hi))
  obtain ks := Within.sub (within_base (State.addr L.scr) (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega_arith))
  have := blk_le hL hi; have := hL.nb; have := hL.nv; have := hL.nc; have := hL.slen; have := hL.blen_lt; have := hL.rpos
  obtain tb : (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * L.r.toNat * i) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    (hL.stk_in hb).sub_left (args8_sub hL), (hL.stk_in hv).sub_left (args8_sub hL),
    (hL.stk_in hs).sub_left (args8_sub hL), by rw [tb]; omega_arith, by omega_arith, by omega_arith,
    by simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, h8]; omega_arith, hL.rpos,
    hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_cov (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) :
    Covers (romixRd L ++ romixWr L i) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (romixWr L i) (pushed [.r12, .lr] t).wr := by
  obtain upw : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed [.r12, .lr] t).wr, Within r R :=
    fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  obtain hw := romix_wsub hL hi
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
  rw [Offset.sub_ofNat_eq _ (by omega_arith : 24 ≤ 40)]
  exact Offset.sub_base _ (by omega_arith)

/-- The regions a call of ROMix writes miss our stack arguments and the save area. -/
theorem romix_apart (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ R ∈ romixWr L i ++ [L.STK], L.ARGS.Disjoint R ∧ L.SV.Disjoint R := by
  obtain hw := romix_wsub hL hi
  intro R hR
  rcases List.mem_append.mp hR with hR | hR
  · refine ⟨hL.args_in (hw R hR), ?_⟩
    simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hL.bc.symm.sub_left hL.sv_sc).sub_right (Within.sub (within_off _ (blk_le hL hi)))
    · exact hL.vc.symm.sub_left hL.sv_sc
    · exact (Offset.disjoint_base _ (by have := hL.slen; omega_arith) (by have := hL.nc; have := hL.slen; omega_arith))
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
  refine frame2_ok (by decide) (by decide) RoMix.roMix_correct roMix_stack (by rw [hc.sp]; omega_arith)
    (romix_pre hL hc hi ha) cov covw fun s₂ mL uL hfl h2 hpost => ?_
  obtain hf : Frame (romixWr L i ++ [L.STK]) t.mem mL :=
    Frame.sub h2.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.STK, by simp, stk_sub hc⟩
  obtain ap := romix_apart hL hi
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
    obtain f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
      (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega_arith)
    obtain e : Spec.Scrypt.bytesAt (pushed [.r12, .lr] t).mem (blkA L i) (128 * L.r.toNat) =
        bytesAt t.mem (blkA L i) (128 * L.r.toNat) :=
      Memory.frame_bytesAt f₀ (fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        obtain hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
            4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
          rw [hc.sp]; exact args8_sub hL
        rw [Nat.mul_comm]
        exact ((hL.stk_in (blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega_arith)
    rw [e] at h
    -- The block is apart from the released frame.
    dsimp only
    rw [Memory.frame_bytesAt hfl (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      rw [Nat.mul_comm]
      exact ((hL.stk_in (blk_in hL hi)).sub_left (stk_sub hc)).symm) (by have := hL.r_lt; omega_arith)]
    exact h

end

end VG.Proof.Scrypt.Arm.Whole

end

end

@[expose] public section

section

section

/-!
# scrypt on 32-bit ARM: correctness

As on the other targets (`Proof/Scrypt/AArch64/Whole/Verified.lean`): our
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

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem t32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem (State.addr L.pw) L.pwl.toNat = bytesAt m₀ (State.addr L.pw) L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := L.pwl.isLt; omega_arith)

theorem salt_bytes : bytesAt t.mem (State.addr L.salt) L.sl.toNat = bytesAt m₀ (State.addr L.salt) L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := L.sl.isLt; omega_arith)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
    L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
    (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkA L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.pp * 128 * L.r.toNat) =
      some (bytesAt m (State.addr L.b) (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkA L k, 128 * L.r.toNat⟩ ⟨blkA L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.blen_lt
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
    Region.Sub ⟨blkA L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega_arith)

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Entry -/

/-- The state on entry. -/
theorem entry_E {s : State} (h : Proof.Scrypt.scryptArm.pre s) : E (lay s) s.gpr s.mem s := by
  have hL := lay_ok h
  have a : ∀ k, k + 4 ≤ 36 → s.mem.readW (State.addr (lay s).sp + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [← hL.arg_addr hk]; rfl
  refine ⟨?_, h.2.2.2.1, rfl, fun _ _ _ => rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Frame.refl _ _, rfl, rfl,
    rfl, rfl⟩
  · rw [h.2.2.1, ← lay_args]; rfl
  all_goals (rw [a _ (by omega_arith)]; rfl)

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
theorem scr_sub (hL : L.Ok) : Region.Sub (scr1600 L) L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega_arith))

omit hv hst in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := t32 hb
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, hL.sc.sub_right (scr_sub hL), ?_,
    hL.ks, hL.ns, ?_, ?_⟩
  · rw [e]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [e]; exact (hL.bc.sub_right hL.sv_sc)
  · rw [e]; exact hL.sb
  · rw [e]; exact hL.bc.sub_right (scr_sub hL)
  · rw [e]; exact hL.nb
  · rw [e]; exact hL.ol1

theorem step1_ok (hL : L.Ok) {t₁ : State} (hc₁ : Ctx L g m₀ t₁) (h4 : t₁.gpr .r4 = L.b)
    (ha₁ : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => Ctx L g m₀ t' ∧
      t'.gpr .r4 = L.b ∧ Step1 L m₀ (bytesAt t'.mem (State.addr L.b) (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkA L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hst name hL hc₁ ha₁ (pbk1_regions hL)) fun t₂ ⟨hc₂, h4₂, _, hp⟩ =>
    ⟨hc₂, h4₂.trans h4, ?_, fun k hk => ?_⟩
  · rw [t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact hp
  · rw [t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkA L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkA L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 32 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem z_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (blkAt L (i + 1) - (L.b + BitVec.ofNat 32 (L.blen.toNat * 128)) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 32 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega_arith
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 32 := by rw [hL.len_b]; exact hb
  rw [VG.Proof.MdStream.Arm.sub_beq e₁ e₂]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega_arith) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, h4, hf₂, hr₂⟩ => ⟨hc₂, h4.trans hb.cur, fun k hk => ?_⟩
  by_cases hki : k = i
  · subst hki
    rw [hr₂, hb.blks k hk]
    simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
  · have e₂ : bytesAt t₂.mem (blkA L k) (128 * L.r.toNat) = bytesAt t.mem (blkA L k) (128 * L.r.toNat) :=
      Memory.frame_bytesAt hf₂ (fun r hr => by
        simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact blk_disj hL hk hi hki
        · exact hL.bv.sub_left (blk_sub hL hk)
        · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
            (Within.sub (within_base _ (by have := hL.slen; omega_arith)))
        · exact (hL.kb.symm.sub_left (blk_sub hL hk)))
        (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)
    rw [e₂, hb.blks k hk]
    by_cases hlt : k < i
    · have : k < i + 1 := by omega_arith
      simp only [hlt, this, ite_true]
    · have : ¬ k < i + 1 := by omega_arith
      simp only [hlt, this, ite_false]

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix"
      Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock))) t fun t' =>
        Inv L g m₀ (i + 1) t' ∧ t'.z = decide (i + 1 = L.pp) := by
  refine WP.seq (WP.mono (romixArgs_ok hL h.1) fun t₁ ⟨hc₁, hm₁, h4₁, ha₁⟩ => ?_)
  rw [h.2.cur] at ha₁
  refine WP.seq (WP.mono (call_step hL hi hc₁ ⟨h4₁.trans h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
    fun t₂ ⟨hc₂, hm₂⟩ => ?_)
  refine WP.mono (nextBlock_ok hc₂) fun t₃ ⟨hc₃, hm₃, h4₃, hz₃⟩ =>
    ⟨⟨hc₃, ⟨by rw [h4₃, hm₂.cur, next_eq], by rw [hm₃]; exact hm₂.blks⟩⟩, ?_⟩
  rw [hz₃, hm₂.cur, next_eq, z_eq hL hi]

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) : WP isa romixLoop t (Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    bytesAt t.mem (State.addr L.b) (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hst in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := t32 hb
  have sc : Region.Sub (scr1600 L) L.SC := Within.sub (within_base _ (by have := hL.slen17; omega_arith))
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))),
    hL.co.symm.sub_right hL.sv_sc, ?_, ?_, hL.co.symm.sub_right sc, ?_, ?_, hL.no, hL.olb⟩
  · rw [e]; exact within_base _ (Nat.le_refl _)
  · rw [e]; exact hL.bo
  · rw [e]; exact hL.bc.sub_right sc
  · rw [e]; exact hL.kb
  · rw [e]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t t₁ : State} (h : Inv L g m₀ L.pp t) (hc₁ : Ctx L g m₀ t₁)
    (hm₁ : t₁.mem = t.mem) (ha₁ : PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem (State.addr L.out) L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hst name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [t32 hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

end

/-! ## The whole function -/

/-- scrypt, from the two derivations and the blocks. -/
theorem body_post (hL : L.Ok) {m : Mem} {out : List Byte}
    (h1 : Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128)))
    (hp : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat = some out) :
    Spec.Scrypt.scrypt (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
      L.NN L.r.toNat L.pp L.ol.toNat = some out := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt m (State.addr L.b) (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt` meets `scryptArm` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptArm.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ Proof.Scrypt.scryptArm.post s s' := by
  have hL := lay_ok h
  refine WP.seq (WP.mono (save1_ok hL (entry_E h) rfl) fun t₁ ⟨e₁, _, r₁, w₁⟩ => ?_)
  refine WP.seq (WP.mono (save2_ok hL e₁ r₁ w₁) fun t₂ ⟨e₂, r₂, w₂, s₂⟩ => ?_)
  refine WP.seq (WP.mono (save3_ok hL e₂ r₂ w₂ s₂) fun t₃ ⟨e₃, s₃⟩ => ?_)
  refine WP.seq (WP.mono (pbk1Args_ok hL e₃ s₃) fun t₄ ⟨hc₄, _, h4₄, ha₄⟩ => ?_)
  refine WP.seq (WP.mono (step1_ok hv hst name hL hc₄ h4₄ ha₄) fun t₅ ⟨hc₅, h4₅, h1, hx⟩ => ?_)
  have i0 : Inv (lay s) s.gpr s.mem 0 t₅ := ⟨hc₅, by rw [h4₅, blk0], fun k hk => by
    rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩
  refine WP.seq (WP.mono (loop_ok hL i0) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (pbk2Args_ok hL h₆.1) fun t₇ ⟨hc₇, hm₇, ha₇⟩ => ?_)
  refine WP.seq (WP.mono (step3_ok hv hst name hL h₆ hc₇ hm₇ ha₇) fun t₈ ⟨hc₈, hp⟩ => ?_)
  refine WP.mono (restore_ok hL hc₈) fun t₉ ⟨hr₉, hsp₉, hm₉⟩ => ⟨⟨hr₉, hsp₉.trans hc₈.sp⟩, ?_⟩
  simp only [Proof.Scrypt.scryptArm, hm₉]
  exact body_post hL h1 hp

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
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat) (bytesAt m₁ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat) (bytesAt m₂ (State.addr L.salt) L.sl.toNat)
      L.r.toNat L.pp).flatMap (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₁ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₂ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 32
  g₂ : Reg → BitVec 32
  m₁ : Mem
  m₂ : Mem

/-- What one run has, from its layout, its registers and memory on entry. -/
abbrev Pred := Lay → (Reg → BitVec 32) → Mem → State → Prop

/-- Two runs with the same layout, each satisfying `P`. -/
def Two (P : Pred) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ LeakEq e.L e.m₁ e.m₂ ∧ P e.L e.g₁ e.m₁ a ∧ P e.L e.g₂ e.m₂ b

/-- `Ctx` and `Φ`. -/
abbrev C (Φ : Lay → Mem → State → Prop) : Pred := fun L g m₀ t => Ctx L g m₀ t ∧ Φ L m₀ t

/-- Code whose runs leak the same, and which establishes `Q`. -/
theorem two_wp {c : Prog isa} {P Q : Pred} (hct : RelCT isa (Two P) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa c t (Q L g m₀)) :
    RelCT isa (Two P) c (Two Q) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ s₁ hL c₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ s₂ hL c₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁, y₂⟩

/-- Two states agree on the taint with the stack arguments and `rs` public. -/
theorem agree_L {L : Lay} (hL : L.Ok) {a b : State} (ha : a.sp = L.sp) (hb : b.sp = L.sp)
    (wa : a.wr = [L.BB, L.VV, L.SC, L.OUT]) (wb : b.wr = [L.BB, L.VV, L.SC, L.OUT])
    (ka : Args L a.mem) (kb : Args L b.mem) {rs : List Reg} (hr : ∀ r ∈ rs, a.gpr r = b.gpr r) :
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
    rw [hL.arg_addr (by omega_arith)]
  rw [st a ha i hi, st b hb i hi]
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ka.r.trans kb.r.symm, ka.b.trans kb.b.symm, ka.blen.trans kb.blen.symm, ka.v.trans kb.v.symm,
    ka.vlen.trans kb.vlen.symm, ka.scr.trans kb.scr.symm, ka.slen.trans kb.slen.symm,
    ka.out.trans kb.out.symm, ka.ol.trans kb.ol.symm]

/-- What every `P` of a piece of straight-line code gives the taint analysis. -/
structure Wfp (P : Pred) : Prop where
  sp : ∀ L g m₀ (t : State), P L g m₀ t → t.sp = L.sp
  wr : ∀ L g m₀ (t : State), P L g m₀ t → t.wr = [L.BB, L.VV, L.SC, L.OUT]
  args : ∀ L g m₀ (t : State), P L g m₀ t → Args L t.mem

theorem Wfp.ctx (Φ : Lay → Mem → State → Prop) : Wfp (C Φ) :=
  ⟨fun _ _ _ _ h => h.1.sp, fun _ _ _ _ h => h.1.wr, fun _ _ _ _ h => h.1.args⟩

/-- A block the taint analysis accepts with the stack arguments and `rs` public. -/
theorem two_blk {is : List Instr} {P Q : Pred} (hP : Wfp P) (rs : List Reg)
    (hr : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → P L g₁ m₁ a → P L g₂ m₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (taint.check (argTaint rs 36) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t → WP isa (.block is) t (Q L g m₀)) :
    RelCT isa (Two P) (.block is) (Two Q) :=
  two_wp (RelCT.taint (A := taint) (argTaint rs 36) (fun _ _ ⟨_, hL, _, c₁, c₂⟩ =>
    agree_L hL (hP.sp _ _ _ _ c₁) (hP.sp _ _ _ _ c₂) (hP.wr _ _ _ _ c₁) (hP.wr _ _ _ _ c₂)
      (hP.args _ _ _ _ c₁) (hP.args _ _ _ _ c₂) (hr _ _ _ _ _ _ _ hL c₁ c₂)) h) hw

/-! ## The calls -/

/-- A call in a frame of four words, of verified code whose contract and
public data hold in both runs. -/
theorem two_call4 {n : String} {c : Prog isa} {k : Contract isa} {P Q : Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed fr4 t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed fr4 t).rd ++ (pushed fr4 t).wr) ∧ Covers (wr L) (pushed fr4 t).wr)
    (hpub : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed fr4 a).callEntry.withRegions (rd L) (wr L))
        ((pushed fr4 b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push fr4) (.call n c) (.pop .r12 16)) t (Q L g m₀)) :
    RelCT isa (Two P) (.frame (.push fr4) (.call n c) (.pop .r12 16)) (Two Q) :=
  two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact frame4_rel hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-- The same for a frame of two words. -/
theorem two_call2 {n : String} {c : Prog isa} {k : Contract isa} {P Q : Pred}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      k.pre ((pushed [.r12, .lr] t).callEntry.withRegions (rd L) (wr L)) ∧
      Covers (rd L ++ wr L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (wr L) (pushed [.r12, .lr] t).wr)
    (hpub : ∀ (L : Lay) g₁ g₂ m₁ m₂ (a b : State), L.Ok → LeakEq L m₁ m₂ → P L g₁ m₁ a → P L g₂ m₂ b →
      a.sp = b.sp ∧ k.pub ((pushed [.r12, .lr] a).callEntry.withRegions (rd L) (wr L))
        ((pushed [.r12, .lr] b).callEntry.withRegions (rd L) (wr L)))
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → P L g m₀ t →
      WP isa (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) t (Q L g m₀)) :
    RelCT isa (Two P) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) (Two Q) :=
  two_wp (fun s₁ s₂ _ _ _ _ hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂⟩ := hp
    obtain ⟨hsp, hpb⟩ := hpub _ _ _ _ _ _ _ hL hk c₁ c₂
    obtain ⟨p₁, v₁, w₁⟩ := hpre _ _ _ _ hL c₁
    obtain ⟨p₂, v₂, w₂⟩ := hpre _ _ _ _ hL c₂
    exact frame2_rel (by decide) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ⟨hsp, p₁, p₂, hpb, v₁, w₁, v₂, w₂⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

theorem pbk_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (c₁ : Ctx L g₁ m₁ a) (c₂ : Ctx L g₂ m₂ b) (hL : L.Ok) {salt sl out ol : BitVec 32}
    (a₁ : PbkArgs L salt sl out ol a) (a₂ : PbkArgs L salt sl out ol b) :
    a.sp = b.sp ∧ pbkA.pub ((pushed fr4 a).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      ((pushed fr4 b).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have s1 : 16 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega_arith
  have s2 : 16 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega_arith
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [pbkA, State.withRegions_sp, State.callEntry_sp, p4_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, p4_a0 s1, p4_a1 s1, p4_a2 s1, p4_a3 s1, p4_a0 s2, p4_a1 s2, p4_a2 s2, p4_a3 s2,
    c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r10, a₁.r11, a₁.r12, a₁.lr, a₂.r0, a₂.r1, a₂.r2, a₂.r3,
    a₂.r10, a₂.r11, a₂.r12, a₂.lr, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t) (rd wr : List Region) :
    bytesAt ((pushed [.r12, .lr] t).callEntry.withRegions rd wr).mem (blkA L i) (128 * L.r.toNat) =
      X L m₀ i := by
  have hS := hL.nS
  have f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
    (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega_arith)
  rw [State.withRegions_mem, State.callEntry_mem, Memory.frame_bytesAt f₀ (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
        rw [hc.sp]; exact args8_sub hL
      rw [Nat.mul_comm]
      exact ((hL.stk_in (blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega_arith), hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {a b : State}
    (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ a) (c₂ : Ctx L g₂ m₂ b) {i : Nat} (hi : i < L.pp)
    (b₁ : InvB L m₁ i a) (b₂ : InvB L m₂ i b) (a₁ : RomixArgs L (blkAt L i) a)
    (a₂ : RomixArgs L (blkAt L i) b) :
    a.sp = b.sp ∧ Proof.Scrypt.roMixArm.pub ((pushed [.r12, .lr] a).callEntry.withRegions (romixRd L) (romixWr L i))
      ((pushed [.r12, .lr] b).callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have s1 : 8 ≤ a.sp.toNat := by rw [c₁.sp]; have := hL.nS; omega_arith
  have s2 : 8 ≤ b.sp.toNat := by rw [c₂.sp]; have := hL.nS; omega_arith
  have y₁ := romix_bytes hL c₁ hi b₁ (romixRd L) (romixWr L i)
  have y₂ := romix_bytes hL c₂ hi b₂ (romixRd L) (romixWr L i)
  refine ⟨c₁.sp.trans c₂.sp.symm, ?_⟩
  simp only [Proof.Scrypt.roMixArm, State.withRegions_sp, State.callEntry_sp, pushed_sp, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, p2_arg0 s1, p2_arg1, p2_arg0 s2, c₁.sp, c₂.sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₁.r12, a₁.lr,
    a₂.r0, a₂.r1, a₂.r2, a₂.r3, a₂.r12, a₂.lr, addr_blk hL hi, true_and]
  rw [y₁, y₂]
  exact leak_X hk hi

/-! ## The pieces -/

theorem Wfp.e {P : Pred} (h : ∀ L g m₀ t, P L g m₀ t → E L g m₀ t) : Wfp P :=
  ⟨fun _ _ _ _ hp => (h _ _ _ _ hp).sp, fun _ _ _ _ hp => (h _ _ _ _ hp).wr,
    fun _ _ _ _ hp => (h _ _ _ _ hp).args⟩

abbrev P0 : Pred := fun L g m₀ t => E L g m₀ t ∧ t.gpr .lr = g .lr
abbrev P1 : Pred := fun L g m₀ t => E L g m₀ t ∧ t.gpr .r12 = L.scr ∧ t.mem.readW (State.addr L.scr) 32 = g .lr
abbrev P2 : Pred := fun L g m₀ t =>
  E L g m₀ t ∧ t.gpr .r12 = L.svb ∧ t.mem.readW (State.addr L.scr) 32 = g .lr ∧ Saved8 L g t.mem
abbrev P3 : Pred := fun L g m₀ t => E L g m₀ t ∧ Saved L g t.mem

theorem save1_ct : RelCT isa (Two P0) (.block save1) (Two P1) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hl⟩ => WP.mono (save1_ok hL he hl) fun _ ⟨e, _, r, w⟩ => ⟨e, r, w⟩

theorem save2_ct : RelCT isa (Two P1) (.block save2) (Two P2) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw⟩ => save2_ok hL he hr hw

theorem save3_ct : RelCT isa (Two P2) (.block save3) (Two P3) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [.r12]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_singleton] at h; subst h; exact c₁.2.1.trans c₂.2.1.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hr, hw, h8⟩ => save3_ok hL he hr hw h8

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (C (LoopAt n))) (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock)))
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (Two (C (LoopAt n))) (.block romixArgs) (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t)) :=
    two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hb⟩ =>
        WP.mono (romixArgs_ok hL hc) fun _ ⟨hc', hm, h4, ha⟩ =>
          ⟨hc', h0, hn, ⟨h4.trans hb.cur, by rw [hm]; exact hb.blks⟩, by rw [hb.cur] at ha; exact ha⟩
  have b : RelCT isa (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t)) (.frame (.push [.r12, .lr])
      (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8))
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)) :=
    two_call2 RoMix.roMix_correct RoMix.roMix_ct (fun L => romixRd L) (fun L => romixWr L (L.pp - n))
      (fun L _ _ _ hL ⟨hc, h0, hn, _, ha⟩ => ⟨romix_pre hL hc (i := L.pp - n) (by omega_arith) ha,
        romix_cov hL hc (i := L.pp - n) (by omega_arith)⟩)
      (fun _ _ _ _ _ _ _ hL hk ⟨c₁, h0, hn, b₁, a₁⟩ ⟨c₂, _, _, b₂, a₂⟩ =>
        romix_pub_two hL hk c₁ c₂ (by omega_arith) b₁ b₂ a₁ a₂)
      (fun _ _ _ _ hL ⟨hc, h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega_arith) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)) (.block nextBlock)
      (Two (C fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.z = decide (L.pp - n + 1 = L.pp))) :=
    two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
      fun _ _ _ _ hL ⟨hc, h0, hn, hm⟩ =>
        WP.mono (nextBlock_ok hc) fun _ ⟨hc', hm', h4, hz⟩ =>
          ⟨hc', h0, hn, ⟨by rw [h4, hm.cur, next_eq], by rw [hm']; exact hm.blks⟩,
            by rw [hz, hm.cur, next_eq, z_eq hL (by omega_arith)]⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (Two (C fun L m₀ t => InvB L m₀ 0 t)) romixLoop (Two (C fun L m₀ t => InvB L m₀ L.pp t)) := by
  have ev : ∀ x : State, isa.eval .ne x = some (!x.z) := fun x => VG.Proof.MdStream.Arm.eval_ne x
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := Two (C fun L m₀ t => InvB L m₀ L.pp t))
    (fun n => Two (C (LoopAt n))) (fun n => (body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, ⟨c₁, h0, hn, b₁, z₁⟩, ⟨c₂, -, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, ⟨c₁, show InvB e.L e.m₁ e.L.pp a from hl ▸ b₁⟩,
          ⟨c₂, show InvB e.L e.m₂ e.L.pp b from hl ▸ b₂⟩⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega_arith
        exact ⟨n - 1, by omega_arith, e, hL, hk, ⟨c₁, by omega_arith, by omega_arith, e₁ ▸ b₁⟩,
          ⟨c₂, by omega_arith, by omega_arith, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, ⟨c₁, b₁⟩, ⟨c₂, b₂⟩⟩ => ⟨e.L.pp, e, hL, hk,
    ⟨c₁, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨c₂, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

abbrev Args1 (L : Lay) (_ : Mem) (t : State) : Prop :=
  t.gpr .r4 = L.b ∧ PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t
abbrev Args2 (L : Lay) (_ : Mem) (t : State) : Prop :=
  PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t

theorem pbk1_ct : RelCT isa (Two P3) (.block pbk1Args) (Two (C Args1)) :=
  two_blk (Wfp.e fun _ _ _ _ h => h.1) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨he, hs⟩ => WP.mono (pbk1Args_ok hL he hs) fun _ ⟨hc, _, h4, ha⟩ => ⟨hc, h4, ha⟩

theorem pbk2_ct : RelCT isa (Two (C fun L m₀ t => InvB L m₀ L.pp t)) (.block pbk2Args) (Two (C Args2)) :=
  two_blk (Wfp.ctx _) [] (fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩

theorem restore_ct : RelCT isa (Two (C fun _ _ _ => True)) (.block restore) fun _ _ => True :=
  (two_blk (Q := fun _ _ _ _ => True) (Wfp.ctx _) [.r6, .r7]
    (fun _ _ _ _ _ _ _ _ c₁ c₂ r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact c₁.1.r6.trans c₂.1.r6.symm
      · exact c₁.1.r7.trans c₂.1.r7.symm) (by taint_decide)
    fun _ _ _ _ hL ⟨hc, _⟩ => WP.mono (restore_ok hL hc) fun _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

theorem call1_ct : RelCT isa (Two (C Args1)) (pbkCall name pbk) (Two (C fun L m₀ t => InvB L m₀ 0 t)) :=
  two_call4 (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
    (fun L => pbkWr L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun _ _ _ _ hL ⟨hc, _, ha⟩ => ⟨pbk_pre' hL hc ha (pbk1_regions hL), pbk_cov hL hc (pbk1_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, _, a₁⟩ ⟨c₂, _, a₂⟩ => pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, h4, ha⟩ => WP.mono (step1_ok hv hst name hL hc h4 ha) fun _ ⟨hc', h4', _, hx⟩ =>
      ⟨hc', by rw [h4', blk0], fun k hk => by rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩)

theorem call2_ct : RelCT isa (Two (C Args2)) (pbkCall name pbk) (Two (C fun _ _ _ => True)) :=
  two_call4 (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)))
    (fun L => pbkWr L L.out L.ol)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => ⟨pbk_pre' hL hc ha (pbk2_regions hL), pbk_cov hL hc (pbk2_regions hL)⟩)
    (fun _ _ _ _ _ _ _ hL _ ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ => pbk_pub_two c₁ c₂ hL a₁ a₂)
    (fun _ _ _ _ hL ⟨hc, ha⟩ => WP.mono (pbk_call hv hst name hL hc ha (pbk2_regions hL)) fun _ h =>
      ⟨h.1, trivial⟩)

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptArm.pre Proof.Scrypt.scryptArm.pub (scrypt name pbk) := by
  refine RelCT.constantTime ((save1_ct.seq (save2_ct.seq (save3_ct.seq (pbk1_ct.seq
    ((call1_ct hv hst name).seq (loop_ct.seq (pbk2_ct.seq ((call2_ct hv hst name).seq restore_ct)))))))).mono
    ?_ fun _ _ _ => trivial)
  rintro s₁ s₂ ⟨h₁, h₂, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp, hlk⟩
  have e : lay s₂ = lay s₁ := by
    simp only [lay, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, hsp]
  refine ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, ⟨entry_E h₁, rfl⟩,
    ⟨e ▸ entry_E h₂, rfl⟩⟩
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
  mem a := bif Nat.beq a.toNat 0x9000 then 1 else bif Nat.beq a.toNat 0x9005 then 0x30 else bif Nat.beq a.toNat 0x9008 then 1
    else bif Nat.beq a.toNat 0x900D then 0x40 else bif Nat.beq a.toNat 0x9010 then 2 else bif Nat.beq a.toNat 0x9015 then 0x50
    else bif Nat.beq a.toNat 0x9018 then 17 else bif Nat.beq a.toNat 0x901D then 0x60 else bif Nat.beq a.toNat 0x9020 then 1 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x9000, 36⟩]
  wr := [⟨0x3000, 128⟩, ⟨0x4000, 256⟩, ⟨0x5000, 2176⟩, ⟨0x6000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptArm.Implies (Spec.Scrypt.scryptContract Arm.abi 40) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 a0 a1 a2 a3 a4 a5 a6 a7
        exact ⟨h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq, satState] [satState]
          using satState }

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified Arm.target (scrypt name pbk) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := scrypt_ok hv hst name h
    exact ⟨t, s', he, hp⟩) (scrypt_ct hv hst name) scrypt_implies

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
    Impl.Pbkdf2.Stream.Arm.Hash.callInit, armStack, armStack_zero hi, armStack_zero hu, armStack_zero hf,
    List.length_cons, List.length_nil, Nat.max_le]
  omega_arith

/-- The code of `vg_pbkdf2_hmac_sha256_scratch`. -/
abbrev pbkC : Prog isa := Proof.Pbkdf2.Whole.Arm.sha256F.pbkdf2

theorem pbk_stack : armStack pbkC ≤ 24 :=
  pbkdf2_stack Proof.Pbkdf2.Stream.Arm.sha256OK.initNF Proof.Pbkdf2.Stream.Arm.sha256OK.updNF
    Proof.Pbkdf2.Stream.Arm.sha256OK.finNF Proof.Pbkdf2.Whole.Arm.sha256OKF.hiSt
    Proof.Pbkdf2.Whole.Arm.sha256OKF.hfSt Proof.Pbkdf2.Whole.Arm.sha256OKF.itSt

/-- `vg_scrypt`. -/
theorem scrypt_verified :
    Verified Arm.target (scrypt "vg_pbkdf2_hmac_sha256_scratch" pbkC) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  scrypt_verified_of Proof.Pbkdf2.Whole.Arm.sha256 pbk_stack _

end VG.Proof.Scrypt.Arm.Whole
