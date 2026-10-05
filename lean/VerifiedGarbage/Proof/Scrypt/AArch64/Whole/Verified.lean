import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Scrypt.AArch64.Scrypt
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Scrypt.AArch64.RoMixCT
import VerifiedGarbage.Proof.Scrypt.AArch64.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCalls
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Steps`. -/
section

section

/-!
# scrypt on AArch64: where everything is

As on x86-64 (`Proof/Scrypt/X86_64/Whole/Layout.lean`): the contract the proof
is written against (`scryptAArch64`), the function's buffers and the 96 bytes
of stack below the stack pointer, from `B` up (`Lay`): the 16 bytes the calls
use, the 64-byte frame (from `B + 16`: the next block, then the password, its
length, `r`, `b`, `blen` and `v`), then the frame holding our return address
(`B + 80`). Our stack arguments are at `B + 96`. `Ctx` is what holds between
the frames' pushes and pops, and `call_ok` runs a call of verified code in
such a state.
-/

namespace VG.Proof.Scrypt

open VG.AArch64 in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. AArch64 contract for
`vg_scrypt(password = x0, password_len = x1, salt = x2, salt_len = x3, r = x4,
b = x5, blen = x6, v = x7, vlen, scratch, slen, out, out_len)`, the last five
on the stack, with 96 bytes of stack below the stack pointer. -/
def scryptAArch64 : Contract AArch64.isa where
  pre s :=
    let vlen := stackArg s 0
    let sc := stackArg s 1
    let slen := stackArg s 2
    let out := stackArg s 3
    let ol := stackArg s 4
    let r := (s.gpr .x4).toNat
    let pwR : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let saltR : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let bR : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat * 128⟩
    let vR : Region := ⟨s.gpr .x7, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 96, 96⟩
    96 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 64 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .x6).toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r ((s.gpr .x6).toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .x4).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ((stackArg s 0).toNat / r) r
      ((s.gpr .x6).toNat / r) (stackArg s 4).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 3) (stackArg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat) (s₁.gpr .x4).toNat
        ((s₁.gpr .x6).toNat / (s₁.gpr .x4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .x4).toNat ((stackArg s₁ 0).toNat / (s₁.gpr .x4).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat) (s₂.gpr .x4).toNat
        ((s₂.gpr .x6).toNat / (s₂.gpr .x4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .x4).toNat ((stackArg s₂ 0).toNat / (s₂.gpr .x4).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64

/-- The arguments, and the lowest byte of the stack used (`sp - 96` on
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

variable (L : VG.Proof.Scrypt.AArch64.Whole.Lay)

abbrev PW : Region := ⟨L.pw, L.pwl.toNat⟩
abbrev SALT : Region := ⟨L.salt, L.sl.toNat⟩
abbrev BB : Region := ⟨L.b, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨L.v, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨L.scr, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨L.out, L.ol.toNat⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 96, 40⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 96⟩
/-- The frames: our words, and our return address. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 64⟩
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 80, 16⟩

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
  nB : L.B.toNat + 136 ≤ 2 ^ 64
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

theorem Within.sub {r R : Region} (h : VG.Proof.Scrypt.AArch64.Whole.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    VG.Proof.Scrypt.AArch64.Whole.Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : VG.Proof.Scrypt.AArch64.Whole.Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.AArch64.Whole.Lay} (h : L.Ok)
include h

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_buf {d n : Nat} (h₁ : d + n ≤ 96) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hr
  · exact (h.kv.sub_left hs).sub_right hr
  · exact (h.kc.sub_left hs).sub_right hr
  · exact (h.ko.sub_left hs).sub_right hr

/-- A range in our stack arguments is disjoint from one in a writable buffer. -/
theorem args_buf {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 136) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hr
  · exact (h.va.symm.sub_left hs).sub_right hr
  · exact (h.ca.symm.sub_left hs).sub_right hr
  · exact (h.oa.symm.sub_left hs).sub_right hr

end Lay.Ok

/-! ## What the calls cannot change -/

/-- The words in the frames and our stack arguments that stay as they are
between the frames' pushes and pops, with our return address `lr`. -/
structure Kept (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (lr : BitVec 64) (m : Mem) : Prop where
  pw : m.readW (L.B + BitVec.ofNat 64 24) 64 = L.pw
  pwl : m.readW (L.B + BitVec.ofNat 64 32) 64 = L.pwl
  r : m.readW (L.B + BitVec.ofNat 64 40) 64 = L.r
  b : m.readW (L.B + BitVec.ofNat 64 48) 64 = L.b
  blen : m.readW (L.B + BitVec.ofNat 64 56) 64 = L.blen
  v : m.readW (L.B + BitVec.ofNat 64 64) 64 = L.v
  lr : m.readW (L.B + BitVec.ofNat 64 80) 64 = lr
  vlen : m.readW (L.B + BitVec.ofNat 64 96) 64 = L.vlen
  scr : m.readW (L.B + BitVec.ofNat 64 104) 64 = L.scr
  out : m.readW (L.B + BitVec.ofNat 64 120) 64 = L.out
  ol : m.readW (L.B + BitVec.ofNat 64 128) 64 = L.ol

/-- The kept words survive changes to memory that miss them. -/
theorem Kept.frame {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {lr : BitVec 64} {m m' : Mem} {rs : List Region} (hk : VG.Proof.Scrypt.AArch64.Whole.Kept L lr m)
    (hf : Frame rs m m')
    (hd : ∀ d, (24 ≤ d ∧ d + 8 ≤ 96) ∨ (96 ≤ d ∧ d + 8 ≤ 136) → ∀ R ∈ rs,
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R) : VG.Proof.Scrypt.AArch64.Whole.Kept L lr m' := by
  have k : ∀ d, (24 ≤ d ∧ d + 8 ≤ 96) ∨ (96 ≤ d ∧ d + 8 ≤ 136) →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 24 (by omega)).trans hk.pw, (k 32 (by omega)).trans hk.pwl, (k 40 (by omega)).trans hk.r,
    (k 48 (by omega)).trans hk.b, (k 56 (by omega)).trans hk.blen, (k 64 (by omega)).trans hk.v,
    (k 80 (by omega)).trans hk.lr, (k 96 (by omega)).trans hk.vlen, (k 104 (by omega)).trans hk.scr,
    (k 120 (by omega)).trans hk.out, (k 128 (by omega)).trans hk.ol⟩

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops: `g` and `vv` are the
registers on entry, `m₀` the memory. -/
structure Ctx (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  kept : VG.Proof.Scrypt.AArch64.Whole.Kept L (g .x30) t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : VG.Proof.Scrypt.AArch64.Whole.Lay) : List Region := [L.PW, L.SALT, L.ARGS, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-- A writable region is within one of the writable buffers. -/
def InBuf (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (r : Region) : Prop :=
  VG.Proof.Scrypt.AArch64.Whole.Within r L.BB ∨ VG.Proof.Scrypt.AArch64.Whole.Within r L.VV ∨ VG.Proof.Scrypt.AArch64.Whole.Within r L.SC ∨ VG.Proof.Scrypt.AArch64.Whole.Within r L.OUT

theorem InBuf.sub {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {r : Region} (h : VG.Proof.Scrypt.AArch64.Whole.InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

theorem covers {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, VG.Proof.Scrypt.AArch64.Whole.Within r R) (hwsub : ∀ r ∈ wr, VG.Proof.Scrypt.AArch64.Whole.InBuf L r) :
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

/-- The stack a call from `sp = B + 16` uses, if it pushes at most one frame. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 16) :
    Region.Sub (below (B + BitVec.ofNat 64 16) m) ⟨B, 16⟩ := by
  have : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (16 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 16) (a := m) (b := 16) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-- A call of verified code (see `WP.callFV`), which pushes at most one frame
and is given regions within ours to read, and within the writable buffers to
write: afterwards `Ctx` holds again, memory changed only within what it
writes and the 16 bytes below `sp`, and the callee's postcondition holds. -/
theorem call_ok {L : VG.Proof.Scrypt.AArch64.Whole.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, VG.Proof.Scrypt.AArch64.Whole.Within r R) (hwsub : ∀ r ∈ wr, VG.Proof.Scrypt.AArch64.Whole.InBuf L r)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := VG.Proof.Scrypt.AArch64.Whole.covers hc hsub hwsub
  refine WP.callFV hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.sp]
      exact VG.Proof.Scrypt.AArch64.Whole.below_call_sub _ (by omega)
  have hnB := hL.nB
  -- The regions the call may change miss the kept words.
  have hdisj : ∀ d, (24 ≤ d ∧ d + 8 ≤ 96) ∨ (96 ≤ d ∧ d + 8 ≤ 136) → ∀ R ∈ wr ++ [⟨L.B, 16⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R := by
    intro d hdd R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨R', hR', hs⟩ := (hwsub R hR).sub
      rcases hdd with hdd | hdd
      · exact hL.stk_buf (by omega) hR' hs
      · exact hL.args_buf (by omega) (by omega) hR' hs
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'), fun r hr => (hvs r hr).trans (hc.vs r hr),
    hc.kept.frame hf' hdisj, hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hpost
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨R', hR', hs⟩ := (hwsub r hr).sub
    rcases hR' with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Region.sub_prefix (by omega)⟩

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Scrypt.AArch64.Whole.Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    s.sp - BitVec.ofNat 64 96⟩

theorem lay_top (s : State) : (VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 96 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 96 = stackArgAddr s 0 := by
  simp only [VG.Proof.Scrypt.AArch64.Whole.lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptAArch64.pre s) : (VG.Proof.Scrypt.AArch64.Whole.lay s).Ok := by
  obtain ⟨h96, h40, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea : (VG.Proof.Scrypt.AArch64.Whole.lay s).ARGS = ⟨stackArgAddr s 0, 40⟩ := by simp only [Lay.ARGS, VG.Proof.Scrypt.AArch64.Whole.lay_args]
  have nB : (VG.Proof.Scrypt.AArch64.Whole.lay s).B.toNat + 136 ≤ 2 ^ 64 := by
    simp only [VG.Proof.Scrypt.AArch64.Whole.lay]
    rw [Offset.toNat_sub_ofNat s.sp 96]
    omega
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, nB, rpos, bmod, vmod, hval, olb, slen⟩

end VG.Proof.Scrypt.AArch64.Whole

end

/-!
# scrypt on AArch64: the blocks between the calls

The parameters as numbers (`Lay.Ok`), the frames' entry (`entry_ok`), and what
each block between the calls does: it keeps `Ctx`, and sets up the next call's
arguments (`PbkArgs`, `RomixArgs`) or the next block.
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)

/-! ## Arithmetic -/

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem lsl7 (x : BitVec 64) : x <<< 7 = BitVec.ofNat 64 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.AArch64.Whole.Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

/-- `b` is not the whole address space, since the stack is not in it. -/
theorem blen_lt : L.blen.toNat * 128 < 2 ^ 64 :=
  VG.Proof.Scrypt.AArch64.Whole.toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 96; omega)

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 64 := by have := h.blen_lt; have := h.r_le; omega

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

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

end Lay.Ok

/-! ## In the frames -/

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

namespace Ctx

variable {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
  (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t)
include hc

theorem inFr {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 80) : InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 80) : InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inArgs (hL : L.Ok) {d : Nat} (h₁ : 96 ≤ d) (h₂ : d + 8 ≤ 136) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

/-- Code that writes only registers other than the callee-saved ones and
the vector registers. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'),
    fun r hr => by rw [hv]; exact hc.vs r hr, by rw [hm]; exact hc.kept, by rw [hm]; exact hc.frame⟩

/-- Code that also writes the frame's first word. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem) : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'), fun r hr => by rw [hv]; exact hc.vs r hr,
    hc.kept.frame hf fun d hd R hR => ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

/-- The registers a block writes, other than the callee-saved ones. -/
macro "scrypt_cs_tac" : tactic => `(tactic| (
  intro r hr _
  revert hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]))

/-! ## The blocks -/

section
variable {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, `c = 1` and `scratch`. -/
structure PbkArgs (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  x0 : t.gpr .x0 = L.pw
  x1 : t.gpr .x1 = L.pwl
  x2 : t.gpr .x2 = salt
  x3 : t.gpr .x3 = sl
  x4 : t.gpr .x4 = 1
  x5 : t.gpr .x5 = out
  x6 : t.gpr .x6 = ol
  x7 : t.gpr .x7 = L.scr

/-- The registers on entry to the frame's body, once our arguments are saved. -/
structure Entry (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.pw
  x1 : t.gpr .x1 = L.pwl
  x2 : t.gpr .x2 = L.salt
  x3 : t.gpr .x3 = L.sl
  x5 : t.gpr .x5 = L.b
  x6 : t.gpr .x6 = L.blen

theorem pbk1Args_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) (he : VG.Proof.Scrypt.AArch64.Whole.Entry L t) :
    WP isa (.block pbk1Args) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ t'.mem = t.mem ∧
      VG.Proof.Scrypt.AArch64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' := by
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pbk1Args, runBlock_cons, runStep_some, runBlock_nil, VG.AArch64.exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, VG.Proof.Scrypt.AArch64.Whole.add_add,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, l104, VG.Proof.Scrypt.AArch64.Whole.read8, hc.kept.scr,
    Option.some.injEq, exists_eq_left', BitVec.shiftLeft_zero]
  refine ⟨hc.regs rfl rfl rfl rfl rfl (by scrypt_cs_tac), trivial, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, rfl⟩
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  exacts [he.x0, he.x1, he.x2, he.x3, he.x5, by rw [he.x6, VG.Proof.Scrypt.AArch64.Whole.lsl7 _]]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem cur0_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) :
    WP isa (.block cur0) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = L.b ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have w16 := hc.inFrW (d := 16) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [cur0, runBlock_cons, runStep_some, runBlock_nil, VG.AArch64.exec, addr, State.load, State.store,
    State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, VG.Proof.Scrypt.AArch64.Whole.add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT,
    and_self, l48, w16, VG.Proof.Scrypt.AArch64.Whole.read8, hc.kept.b, VG.Proof.Scrypt.AArch64.Whole.write8, Option.some.injEq, exists_eq_left']
  have f : Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 16) L.b) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.store hL rfl rfl hc.sp.symm rfl (by scrypt_cs_tac) f, Mem.readW_writeW_self64 _ _ _, f⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (cur : Addr) (t : State) : Prop where
  x0 : t.gpr .x0 = cur
  x1 : t.gpr .x1 = L.r
  x2 : t.gpr .x2 = L.v
  x3 : t.gpr .x3 = L.vlen
  x4 : t.gpr .x4 = L.scr
  x5 : t.gpr .x5 = L.r + BitVec.ofNat 64 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Scrypt.AArch64.Whole.RomixArgs L cur t' := by
  have l16 := hc.inFr (d := 16) (by omega) (by omega)
  have l40 := hc.inFr (d := 40) (by omega) (by omega)
  have l64 := hc.inFr (d := 64) (by omega) (by omega)
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [romixArgs, runBlock_cons, runStep_some, runBlock_nil, VG.AArch64.exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, VG.Proof.Scrypt.AArch64.Whole.add_add,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, l16, l40, l64, l96, l104,
    VG.Proof.Scrypt.AArch64.Whole.read8, hcur, hc.kept.r, hc.kept.v, hc.kept.vlen, hc.kept.scr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by scrypt_cs_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.gpr .x11 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
  have l16 := hc.inFr (d := 16) (by omega) (by omega)
  have w16 := hc.inFrW (d := 16) (by omega) (by omega)
  have l40 := hc.inFr (d := 40) (by omega) (by omega)
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l56 := hc.inFr (d := 56) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [nextBlock, runBlock_cons, runStep_some, runBlock_nil, VG.AArch64.exec, addr, State.load, State.store,
    State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, VG.Proof.Scrypt.AArch64.Whole.add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT,
    and_self, l16, w16, l40, l48, l56, VG.Proof.Scrypt.AArch64.Whole.read8, hcur, hc.kept.r, hc.kept.b, hc.kept.blen, VG.Proof.Scrypt.AArch64.Whole.write8, VG.Proof.Scrypt.AArch64.Whole.lsl7,
    Option.some.injEq, exists_eq_left']
  have f : Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem
      (t.mem.writeW (L.B + BitVec.ofNat 64 16) (cur + BitVec.ofNat 64 (L.r.toNat * 128))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.store hL rfl rfl hc.sp.symm rfl (by scrypt_cs_tac) f, f, Mem.readW_writeW_self64 _ _ _, trivial⟩

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) :
    WP isa (.block pbk2Args) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ t'.mem = t.mem ∧
      VG.Proof.Scrypt.AArch64.Whole.PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' := by
  have l24 := hc.inFr (d := 24) (by omega) (by omega)
  have l32 := hc.inFr (d := 32) (by omega) (by omega)
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l56 := hc.inFr (d := 56) (by omega) (by omega)
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  have l128 := hc.inArgs hL (d := 128) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pbk2Args, runBlock_cons, runStep_some, runBlock_nil, VG.AArch64.exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, VG.Proof.Scrypt.AArch64.Whole.add_add,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, l24, l32, l48, l56, l104, l120,
    l128, VG.Proof.Scrypt.AArch64.Whole.read8, hc.kept.pw, hc.kept.pwl, hc.kept.b, hc.kept.blen, hc.kept.scr, hc.kept.out, hc.kept.ol,
    VG.Proof.Scrypt.AArch64.Whole.lsl7, BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by scrypt_cs_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-! ## Entering the frames -/

/-- Six words stored in the frame. -/
theorem six_ok (B : Addr) (m : Mem) (a b c d e f : BitVec 64) :
    let m' := (((((m.writeW (B + BitVec.ofNat 64 24) a).writeW (B + BitVec.ofNat 64 32) b).writeW
      (B + BitVec.ofNat 64 40) c).writeW (B + BitVec.ofNat 64 48) d).writeW (B + BitVec.ofNat 64 56) e).writeW
      (B + BitVec.ofNat 64 64) f
    Frame [⟨B + BitVec.ofNat 64 24, 48⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 24) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 32) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 40) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 48) 64 = d ∧ m'.readW (B + BitVec.ofNat 64 56) 64 = e ∧
      m'.readW (B + BitVec.ofNat 64 64) 64 = f := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 136 → y + 8 ≤ 136 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 24 ≤ x → x + 8 ≤ 72 →
      (⟨B + BitVec.ofNat 64 24, 48⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 24 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 32 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 40 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 48 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 56 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 64 (by omega) (by omega)), ?_, ?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 24 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 48 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 32 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 32 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 32 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 32 48 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 32 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 40 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 40 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 40 48 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 48 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 48 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 56 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated 64 (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (VG.Proof.Scrypt.AArch64.Whole.entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (VG.Proof.Scrypt.AArch64.Whole.entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (VG.Proof.Scrypt.AArch64.Whole.entered s).v = s.v := rfl

theorem entered_sp (s : State) : (VG.Proof.Scrypt.AArch64.Whole.entered s).sp = (VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 16 := by
  show s.sp - 16 - BitVec.ofNat 64 64 = s.sp - BitVec.ofNat 64 96 + BitVec.ofNat 64 16
  bv_omega

theorem lr_slot (s : State) : s.sp - 16 = (VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 80 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 96 + BitVec.ofNat 64 80
  bv_omega

theorem entered_wr (s : State) :
    (VG.Proof.Scrypt.AArch64.Whole.entered s).wr = (VG.Proof.Scrypt.AArch64.Whole.lay s).FR :: (VG.Proof.Scrypt.AArch64.Whole.lay s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 64, 64⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 64 = (VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 16 from VG.Proof.Scrypt.AArch64.Whole.entered_sp s, VG.Proof.Scrypt.AArch64.Whole.lr_slot]

theorem entered_mem (s : State) :
    (VG.Proof.Scrypt.AArch64.Whole.entered s).mem = s.mem.writeW ((VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 80) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [VG.Proof.Scrypt.AArch64.Whole.lr_slot, VG.Proof.Scrypt.AArch64.Whole.write8]

theorem arg_slot (s : State) (i : Nat) (hi : i < 5) :
    stackArgAddr s i = (VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 (96 + 8 * i) := by
  simp only [stackArgAddr, VG.Proof.Scrypt.AArch64.Whole.lay]
  have : 8 * i < 2 ^ 64 := by omega
  bv_omega

theorem entry_ok {s : State} (h : Proof.Scrypt.scryptAArch64.pre s) :
    WP isa (.block saveArgs) (VG.Proof.Scrypt.AArch64.Whole.entered s) fun t => VG.Proof.Scrypt.AArch64.Whole.Ctx (VG.Proof.Scrypt.AArch64.Whole.lay s) s.gpr s.v s.mem t ∧ VG.Proof.Scrypt.AArch64.Whole.Entry (VG.Proof.Scrypt.AArch64.Whole.lay s) t := by
  have hL := VG.Proof.Scrypt.AArch64.Whole.lay_ok h
  have hnB := hL.nB
  have hw : ∀ d, 16 ≤ d → d + 8 ≤ 80 → InRegions (VG.Proof.Scrypt.AArch64.Whole.entered s).wr ((VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨(VG.Proof.Scrypt.AArch64.Whole.lay s).FR, by rw [VG.Proof.Scrypt.AArch64.Whole.entered_wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have w24 := hw 24 (by omega) (by omega)
  have w32 := hw 32 (by omega) (by omega)
  have w40 := hw 40 (by omega) (by omega)
  have w48 := hw 48 (by omega) (by omega)
  have w56 := hw 56 (by omega) (by omega)
  have w64 := hw 64 (by omega) (by omega)
  apply WP.of_runBlock
  simp only [saveArgs, runBlock_cons, runStep_some, runBlock_nil, VG.AArch64.exec, addr, State.store, State.read,
    Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false, ite_true, VG.Proof.Scrypt.AArch64.Whole.entered_sp,
    VG.Proof.Scrypt.AArch64.Whole.add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w24, w32, w40, w48, w56,
    w64, VG.Proof.Scrypt.AArch64.Whole.write8, Option.some.injEq, exists_eq_left', BitVec.add_zero, VG.Proof.Scrypt.AArch64.Whole.entered_gpr]
  obtain ⟨f, k24, k32, k40, k48, k56, k64⟩ := VG.Proof.Scrypt.AArch64.Whole.six_ok (VG.Proof.Scrypt.AArch64.Whole.lay s).B (VG.Proof.Scrypt.AArch64.Whole.entered s).mem (s.gpr .x0) (s.gpr .x1)
    (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  rw [VG.Proof.Scrypt.AArch64.Whole.entered_mem] at f k24 k32 k40 k48 k56 k64
  have keepF : ∀ d, ((VG.Proof.Scrypt.AArch64.Whole.lay s).B.toNat + d + 8 ≤ 2 ^ 64) → (72 ≤ d) →
      Region.Disjoint ⟨(VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 d, 8⟩ ⟨(VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 24, 48⟩ :=
    fun d h₁ h₂ => Offset.disjoint _ (by omega) (by omega) (by omega)
  have lr : ∀ m : Mem, Frame [⟨(VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 24, 48⟩]
      (s.mem.writeW ((VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 80) (s.gpr .x30)) m →
      m.readW ((VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 80) 64 = s.gpr .x30 := fun m hf => by
    rw [hf.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact keepF 80 (by omega) (by omega)) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  have arg : ∀ i, i < 5 → ∀ m : Mem, Frame [⟨(VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 24, 48⟩]
      (s.mem.writeW ((VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 80) (s.gpr .x30)) m →
      m.readW ((VG.Proof.Scrypt.AArch64.Whole.lay s).B + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s i := fun i hi m hf => by
    rw [hf.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact keepF _ (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), stackArg,
      VG.Proof.Scrypt.AArch64.Whole.arg_slot s i hi]
  rw [VG.Proof.Scrypt.AArch64.Whole.entered_mem]
  refine ⟨⟨?_, ?_, rfl, ?_, fun _ _ => by simp only [RegUpd.v_write, VG.Proof.Scrypt.AArch64.Whole.entered_v], ⟨k24, k32, k40, k48, k56, k64, lr _ f, arg 0 (by omega) _ f,
    arg 1 (by omega) _ f, arg 3 (by omega) _ f, arg 4 (by omega) _ f⟩, ?_⟩, ?_⟩
  · simp only [VG.Proof.Scrypt.AArch64.Whole.entered_rd]
    rw [h.2.2.1, ← VG.Proof.Scrypt.AArch64.Whole.lay_args]; rfl
  · rw [VG.Proof.Scrypt.AArch64.Whole.entered_wr, h.2.2.2.1]; rfl
  · intro r hr hr'
    rw [RegUpd.gpr_write_of_ne _ _ _ (by
      intro e; subst e; simp [preserved] at hr), VG.Proof.Scrypt.AArch64.Whole.entered_gpr]
  · refine Frame.trans (Frame.writeW (Frame.refl _ _) (r := (VG.Proof.Scrypt.AArch64.Whole.lay s).STK) (by simp) _
      (Offset.contains_base _ (by omega) (by omega))) (Frame.sub f fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(VG.Proof.Scrypt.AArch64.Whole.lay s).STK, by simp, Offset.sub_base _ (by omega)⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, VG.Proof.Scrypt.AArch64.Whole.entered_gpr] <;> rfl

end

end VG.Proof.Scrypt.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Correct`. -/
section

section

section

/-!
# scrypt on AArch64: PBKDF2-HMAC-SHA256 as a callee

`vg_pbkdf2_hmac_sha256_scratch` (any implementation of it) is verified against the
shared contract `VG.Spec.Hmac.sha256I.pbkdf2ScratchContract`; its caller works with
the same contract spelt out (`pbkG`, the contract its proof is written
against): `pbk_correct` and `pbk_ct` are its correctness and constant time
under `pbkG`, from its `Verified` proof.
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (pbkG)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (stk)

/-- `pbkdf2`'s contract, spelt out. -/
abbrev pbkK : Contract isa := pbkG Spec.Hmac.sha256S 200

theorem pbk_pre {s : State} (h : pbkK.pre s) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    AArch64.abi, AArch64.argRegs]
  simp only [VG.Proof.Scrypt.AArch64.Whole.pbkK, pbkG, Spec.Hmac.sha256S] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

theorem pbk_post {s s' : State} (h : (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16).post s s') :
    pbkK.post s s' := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    AArch64.abi, AArch64.argRegs] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkK.pub s₁ s₂) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16).pub s₁ s₂ := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    AArch64.abi, AArch64.argRegs]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h9, h1, h2, h3, h4, h5, h6, h7, h8⟩

variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16))
include hv

theorem pbk_correct (s : State) (h : pbkK.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (VG.Proof.Scrypt.AArch64.Whole.pbk_pre h)
  exact ⟨t, s', he, ha, VG.Proof.Scrypt.AArch64.Whole.pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (VG.Proof.Scrypt.AArch64.Whole.pbk_pre h₁) (VG.Proof.Scrypt.AArch64.Whole.pbk_pre h₂) (VG.Proof.Scrypt.AArch64.Whole.pbk_pub hp) e₁ e₂

end VG.Proof.Scrypt.AArch64.Whole

end

/-!
# scrypt on AArch64: the calls

What a call of `vg_pbkdf2_hmac_sha256_scratch` (`pbk_call`) and of `vg_scrypt_romix`
(`romix_call`) from the frames does, from their arguments (`PbkArgs`,
`RomixArgs`): each keeps `Ctx`, and changes memory only in what it writes and
the stack below the frames. `pbk_pre'` and `romix_pre` are their
preconditions, which the proof of constant time uses too.
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Md.AArch64 (pbkG)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (stk)

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

theorem Ctx.ce_sp {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).sp = L.B + BitVec.ofNat 64 16 := by
  rw [State.withRegions_sp, State.callEntry_sp, hc.sp]

theorem sub16 (B : Addr) : B + BitVec.ofNat 64 16 - 16 = B := BitVec.add_sub_cancel _ _

namespace Lay.Ok

variable (hL : L.Ok)
include hL

/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : VG.Proof.Scrypt.AArch64.Whole.InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs]

theorem stk_in {d n : Nat} (h₁ : d + n ≤ 96) {r : Region} (h : VG.Proof.Scrypt.AArch64.Whole.InBuf L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  exact hL.stk_buf h₁ hR hs

/-- The 16 bytes the calls use miss every writable buffer. -/
theorem low_in {r : Region} (h : VG.Proof.Scrypt.AArch64.Whole.InBuf L r) : Region.Disjoint ⟨L.B, 16⟩ r := by
  have := hL.stk_in (d := 0) (n := 16) (by omega) h
  simpa using this

theorem scr_in : VG.Proof.Scrypt.AArch64.Whole.InBuf L ⟨L.scr, 200 * 8⟩ :=
  .inr (.inr (.inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen17; omega))))

end Lay.Ok

/-! ## PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (salt : Addr) (sl : BitVec 64) : List Region := [L.PW, ⟨salt, sl.toNat⟩]
abbrev pbkWr (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (out : Addr) (ol : BitVec 64) : List Region :=
  [⟨out, ol.toNat⟩, ⟨L.scr, 200 * 8⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) : Prop where
  sw : ∃ R ∈ L.regions, VG.Proof.Scrypt.AArch64.Whole.Within ⟨salt, sl.toNat⟩ R
  ow : VG.Proof.Scrypt.AArch64.Whole.InBuf L ⟨out, ol.toNat⟩
  so : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨out, ol.toNat⟩
  sc : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨L.scr, 200 * 8⟩
  oc : Region.Disjoint ⟨out, ol.toNat⟩ ⟨L.scr, 200 * 8⟩
  ks : L.STK.Disjoint ⟨salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 64
  no : out.toNat + ol.toNat ≤ 2 ^ 64
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : VG.Proof.Scrypt.AArch64.Whole.PbkArgs L salt sl out ol t) (hr : VG.Proof.Scrypt.AArch64.Whole.PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (VG.Proof.Scrypt.AArch64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.AArch64.Whole.pbkWr L out ol)) := by
  have hnB := hL.nB
  have t16 : (L.B + BitVec.ofNat 64 16).toNat = L.B.toNat + 16 := toNat_add_ofNat _ (by omega)
  have sw : VG.Proof.Scrypt.AArch64.Whole.InBuf L ⟨L.scr, 200 * 8⟩ := hL.scr_in
  simp only [VG.Proof.Scrypt.AArch64.Whole.pbkK, pbkG, stk, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr,
    hc.ce_sp, VG.Proof.Scrypt.AArch64.Whole.sub16, t16, VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs), ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7]
  exact ⟨by omega, trivial, trivial, hL.pw_buf hr.ow, hL.pw_buf sw, hr.so, hr.sc, hr.oc,
    by simpa using hL.kp.sub_left (Offset.sub_base L.B (d := 0) (n := 16) (k := 96) (by omega)),
    hr.ks.sub_left (by simpa using Offset.sub_base L.B (d := 0) (n := 16) (k := 96) (by omega)),
    hL.low_in hr.ow, hL.low_in sw, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : VG.Proof.Scrypt.AArch64.Whole.PbkRegions L salt sl out ol) :
    ∀ r ∈ VG.Proof.Scrypt.AArch64.Whole.pbkRd L salt sl ++ VG.Proof.Scrypt.AArch64.Whole.pbkWr L out ol, ∃ R ∈ L.regions, VG.Proof.Scrypt.AArch64.Whole.Within r R := by
  have hs := hr.sw
  simp only [VG.Proof.Scrypt.AArch64.Whole.pbkRd, VG.Proof.Scrypt.AArch64.Whole.pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, VG.Proof.Scrypt.AArch64.Whole.within_base _ (by omega)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen17; omega)⟩

theorem pbk_wsub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : VG.Proof.Scrypt.AArch64.Whole.PbkRegions L salt sl out ol) : ∀ r ∈ VG.Proof.Scrypt.AArch64.Whole.pbkWr L out ol, VG.Proof.Scrypt.AArch64.Whole.InBuf L r := by
  simp only [VG.Proof.Scrypt.AArch64.Whole.pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hr.ow
  · exact hL.scr_in

theorem pbk_call (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16))
    (hd : pbk.aarch64Depth ≤ 1) (name : String) (hL : L.Ok) {t : State}
    (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : VG.Proof.Scrypt.AArch64.Whole.PbkArgs L salt sl out ol t) (hr : VG.Proof.Scrypt.AArch64.Whole.PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.scr, 200 * 8⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  refine VG.Proof.Scrypt.AArch64.Whole.call_ok hL (VG.Proof.Scrypt.AArch64.Whole.pbk_correct hv) hd hc (VG.Proof.Scrypt.AArch64.Whole.pbk_pre' hL hc ha hr) (VG.Proof.Scrypt.AArch64.Whole.pbk_sub hL hr) (VG.Proof.Scrypt.AArch64.Whole.pbk_wsub hL hr)
    fun s' hc' hf hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [VG.Proof.Scrypt.AArch64.Whole.pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_mem, State.callEntry_mem,
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), ha.x0, ha.x1, ha.x2, ha.x3,
    ha.x4, ha.x5, ha.x6] at h
  exact h

end

/-! ## ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (i : Nat) : List Region :=
  [⟨VG.Proof.Scrypt.AArch64.Whole.blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, (L.r.toNat + 2) * 128⟩]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : VG.Proof.Scrypt.AArch64.Whole.InBuf L ⟨VG.Proof.Scrypt.AArch64.Whole.blkAt L i, L.r.toNat * 128⟩ :=
  .inl (VG.Proof.Scrypt.AArch64.Whole.within_off _ (VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi))

theorem r2 (hL : L.Ok) : (L.r + BitVec.ofNat 64 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  exact toNat_add_ofNat _ (by omega)

theorem romix_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.AArch64.Whole.RomixArgs L (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) t) :
    Proof.Scrypt.roMixAArch64.pre (t.callEntry.withRegions [] (VG.Proof.Scrypt.AArch64.Whole.romixWr L i)) := by
  have hnB := hL.nB
  have hb := VG.Proof.Scrypt.AArch64.Whole.blk_in hL hi
  have hv : VG.Proof.Scrypt.AArch64.Whole.InBuf L ⟨L.v, L.vlen.toNat * 128⟩ := .inr (.inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _)))
  have hs : VG.Proof.Scrypt.AArch64.Whole.InBuf L ⟨L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen; omega))))
  have tb : (VG.Proof.Scrypt.AArch64.Whole.blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    have := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi; have := hL.nb; have := hL.rpos
    exact toNat_add_ofNat _ (by omega)
  have t16 : (L.B + BitVec.ofNat 64 16).toNat = L.B.toNat + 16 := toNat_add_ofNat _ (by omega)
  simp only [Proof.Scrypt.roMixAArch64, State.withRegions_rd, State.withRegions_wr, hc.ce_sp, VG.Proof.Scrypt.AArch64.Whole.sub16, t16,
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, VG.Proof.Scrypt.AArch64.Whole.r2 hL]
  have kb := Within.sub (VG.Proof.Scrypt.AArch64.Whole.within_off L.b (VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi))
  have ks := Within.sub (VG.Proof.Scrypt.AArch64.Whole.within_base L.scr (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    by omega, hL.low_in hb, hL.low_in hv, hL.low_in hs,
    by rw [tb]; have := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi; have := hL.nb; omega, hL.nv,
    by have := hL.nc; have := hL.slen; omega, hL.rpos, hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ ([] : List Region) ++ VG.Proof.Scrypt.AArch64.Whole.romixWr L i, ∃ R ∈ L.regions, VG.Proof.Scrypt.AArch64.Whole.Within r R := by
  simp only [VG.Proof.Scrypt.AArch64.Whole.romixWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.BB, by simp, VG.Proof.Scrypt.AArch64.Whole.within_off _ (VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen; omega)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ VG.Proof.Scrypt.AArch64.Whole.romixWr L i, VG.Proof.Scrypt.AArch64.Whole.InBuf L r := by
  simp only [VG.Proof.Scrypt.AArch64.Whole.romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.Proof.Scrypt.AArch64.Whole.blk_in hL hi
  · exact .inr (.inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen; omega))))

theorem roMix_depth : Impl.Scrypt.AArch64.roMix.aarch64Depth ≤ 1 := by lit_decide

theorem romix_call (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.AArch64.Whole.RomixArgs L (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      Frame (VG.Proof.Scrypt.AArch64.Whole.romixWr L i ++ [⟨L.B, 16⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) (128 * L.r.toNat)) := by
  refine VG.Proof.Scrypt.AArch64.Whole.call_ok hL RoMix.roMix_correct VG.Proof.Scrypt.AArch64.Whole.roMix_depth hc (VG.Proof.Scrypt.AArch64.Whole.romix_pre hL hc hi ha)
    (VG.Proof.Scrypt.AArch64.Whole.romix_sub hL hi) (VG.Proof.Scrypt.AArch64.Whole.romix_wsub hL hi) fun s' hc' hf hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [Proof.Scrypt.roMixAArch64, State.withRegions_mem, State.callEntry_mem,
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), ha.x0, ha.x1, ha.x3] at h
  exact h

end

end VG.Proof.Scrypt.AArch64.Whole

end

/-!
# scrypt on AArch64: correctness

As on x86-64 (`Proof/Scrypt/X86_64/Whole/Correct.lean`): step 1 leaves the
blocks `X k` of `PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`);
the loop replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`);
step 3 derives the key from them (`step3_ok`). `scrypt_ok` puts the frames
around it, for any implementation `pbk` of PBKDF2 verified against its shared
contract.
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

variable {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem L.pw L.pwl.toNat = bytesAt m₀ L.pw L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega)

theorem salt_bytes : bytesAt t.mem L.salt L.sl.toNat = bytesAt m₀ L.salt L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
    (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : VG.Proof.Scrypt.AArch64.Whole.Step1 L m₀ (bytesAt m L.b (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : VG.Proof.Scrypt.AArch64.Whole.X L m₀ k = bytesAt m (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
      (L.pp * 128 * L.r.toNat) = some (bytesAt m L.b (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  rw [VG.Proof.Scrypt.AArch64.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨VG.Proof.Scrypt.AArch64.Whole.blkAt L k, 128 * L.r.toNat⟩ ⟨VG.Proof.Scrypt.AArch64.Whole.blkAt L i, L.r.toNat * 128⟩ := by
  have h₁ := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hk
  have h₂ := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi
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
    Region.Sub ⟨VG.Proof.Scrypt.AArch64.Whole.blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hk
  exact Offset.sub_base _ (by omega)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr, 200 * 8⟩ L.SC :=
  Within.sub (VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen17; omega))

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

omit hv hd in
theorem pbk1_regions (hL : L.Ok) :
    VG.Proof.Scrypt.AArch64.Whole.PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact .inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _))
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact hL.sb
  · exact hL.sc.sub_right (VG.Proof.Scrypt.AArch64.Whole.scr_sub hL)
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]
    exact hL.bc.sub_right (VG.Proof.Scrypt.AArch64.Whole.scr_sub hL)
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact hL.nb
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t)
    (ha : VG.Proof.Scrypt.AArch64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      VG.Proof.Scrypt.AArch64.Whole.Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.AArch64.Whole.X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk_call hv hd name hL hc ha (VG.Proof.Scrypt.AArch64.Whole.pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (VG.Proof.Scrypt.AArch64.Whole.X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) (he : VG.Proof.Scrypt.AArch64.Whole.Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      VG.Proof.Scrypt.AArch64.Whole.Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.AArch64.Whole.X L m₀ k :=
  WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk1Args_ok hL hc he) fun _ ⟨hc₁, _, ha₁⟩ => VG.Proof.Scrypt.AArch64.Whole.pbk1_call_ok hv hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = VG.Proof.Scrypt.AArch64.Whole.blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.AArch64.Whole.X L m₀ k) else VG.Proof.Scrypt.AArch64.Whole.X L m₀ k

abbrev Inv (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (i : Nat) (t : State) :
    Prop :=
  VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t ∧ VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = VG.Proof.Scrypt.AArch64.Whole.blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.AArch64.Whole.X L m₀ k) else VG.Proof.Scrypt.AArch64.Whole.X L m₀ k

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : VG.Proof.Scrypt.AArch64.Whole.Lay) : VG.Proof.Scrypt.AArch64.Whole.blkAt L 0 = L.b := by
  simp only [VG.Proof.Scrypt.AArch64.Whole.blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-- A block of `b` misses the frame's first word. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Disjoint ⟨VG.Proof.Scrypt.AArch64.Whole.blkAt L k, 128 * L.r.toNat⟩ ⟨L.B + BitVec.ofNat 64 16, 8⟩ :=
  (hL.kb.symm.sub_left (VG.Proof.Scrypt.AArch64.Whole.blk_sub hL hk)).sub_right (Offset.sub_base _ (by omega))

theorem start_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.AArch64.Whole.X L m₀ k) :
    WP isa (.block cur0) t (VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀ 0) :=
  WP.mono (VG.Proof.Scrypt.AArch64.Whole.cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', hb.trans (VG.Proof.Scrypt.AArch64.Whole.blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Scrypt.AArch64.Whole.blk_fr hL hk)
      (by have := hL.blen_lt; have := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hk; omega)⟩

theorem next_eq (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (i : Nat) :
    VG.Proof.Scrypt.AArch64.Whole.blkAt L i + BitVec.ofNat 64 (L.r.toNat * 128) = VG.Proof.Scrypt.AArch64.Whole.blkAt L (i + 1) := by
  simp only [VG.Proof.Scrypt.AArch64.Whole.blkAt]
  rw [VG.Proof.Scrypt.AArch64.Whole.add_add, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

/-- The bytes of `b` left after block `i`, as the loop's condition reads them. -/
theorem left_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - VG.Proof.Scrypt.AArch64.Whole.blkAt L (i + 1) != 0) = decide (i + 1 ≠ L.pp) := by
  have h₁ := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [VG.Proof.Scrypt.AArch64.Whole.blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 64 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [bne, Offset.ofNat_sub_ofNat_beq e₂ e₁, decide_not]
  refine congrArg (!·) (decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h).symm

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t)
    (hb : VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ i t) (ha : VG.Proof.Scrypt.AArch64.Whole.RomixArgs L (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix) t fun t' =>
      VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ VG.Proof.Scrypt.AArch64.Whole.Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (VG.Proof.Scrypt.AArch64.Whole.romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [VG.Proof.Scrypt.AArch64.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega) (VG.Proof.Scrypt.AArch64.Whole.blk_in hL hi)
    · exact hL.stk_in (by omega) (.inr (.inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega) (.inr (.inr (.inl (VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen; omega)))))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [VG.Proof.Scrypt.AArch64.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact VG.Proof.Scrypt.AArch64.Whole.blk_disj hL hk hi hki
          · exact hL.bv.sub_left (VG.Proof.Scrypt.AArch64.Whole.blk_sub hL hk)
          · exact (hL.bc.sub_left (VG.Proof.Scrypt.AArch64.Whole.blk_sub hL hk)).sub_right
              (Within.sub (VG.Proof.Scrypt.AArch64.Whole.within_base _ (by have := hL.slen; omega)))
          · exact (hL.kb.symm.sub_left (VG.Proof.Scrypt.AArch64.Whole.blk_sub hL hk)).sub_right (Region.sub_prefix (by omega)))
          (by have := hL.blen_lt; have := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hk; omega)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega
        simp only [hlt, this, ite_false]

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t)
    (hm : VG.Proof.Scrypt.AArch64.Whole.Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ (i + 1) t' ∧
      (t'.gpr .x11 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.mono (VG.Proof.Scrypt.AArch64.Whole.nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hx₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, VG.Proof.Scrypt.AArch64.Whole.next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Scrypt.AArch64.Whole.blk_fr hL hk)
        (by have := hL.blen_lt; have := VG.Proof.Scrypt.AArch64.Whole.blk_le hL hk; omega)⟩,
      by rw [hx₃, VG.Proof.Scrypt.AArch64.Whole.next_eq, VG.Proof.Scrypt.AArch64.Whole.left_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix)
      (.block nextBlock))) t fun t' =>
        VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀ (i + 1) t' ∧ (t'.gpr .x11 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.romixArgs_ok hL h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.call_step hL hi hc₁ ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => WP.mono (VG.Proof.Scrypt.AArch64.Whole.next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀ 0 t) :
    WP isa romixLoop t (VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀) (fun _ hi _ h => VG.Proof.Scrypt.AArch64.Whole.body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

omit hv hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀ L.pp t) :
    bytesAt t.mem L.b (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.AArch64.Whole.X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hd in
theorem pbk2_regions (hL : L.Ok) :
    VG.Proof.Scrypt.AArch64.Whole.PbkRegions L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (VG.Proof.Scrypt.AArch64.Whole.scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact VG.Proof.Scrypt.AArch64.Whole.within_base _ (Nat.le_refl _)
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact hL.bo
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact hL.bc.sub_right (VG.Proof.Scrypt.AArch64.Whole.scr_sub hL)
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact hL.kb
  · rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.AArch64.Whole.Inv L g vv m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.AArch64.Whole.X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk2Args_ok hL h.1) fun t₁ ⟨hc₁, hm₁, ha₁⟩ => ?_)
  refine WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk_call hv hd name hL hc₁ ha₁ (VG.Proof.Scrypt.AArch64.Whole.pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [VG.Proof.Scrypt.AArch64.toNat_ofNat_lt hb, hc₁.pw_bytes hL, hm₁, VG.Proof.Scrypt.AArch64.Whole.final_bytes' hL h] at hp
  exact hp

/-- The inner frame's body, once our arguments are saved. -/
theorem rest_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t) (he : VG.Proof.Scrypt.AArch64.Whole.Entry L t) :
    WP isa (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop (pbkCall name pbk pbk2Args))))
      t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.step1_ok hv hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.mono (VG.Proof.Scrypt.AArch64.Whole.step3_ok hv hd name hL h₃) fun t₄ ⟨hc₄, hp⟩ => ⟨hc₄, ?_⟩
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem L.b (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [VG.Proof.Scrypt.AArch64.Whole.X_of hL h1 hk, Whole.chunk_bytesAt _ _ (VG.Proof.Scrypt.AArch64.Whole.blk_le' hL hk)]

end

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

/-- `vg_scrypt` meets `scryptAArch64` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptAArch64.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ Proof.Scrypt.scryptAArch64.post s s' := by
  have hL := VG.Proof.Scrypt.AArch64.Whole.lay_ok h
  have h96 := h.1
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 64 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 64 ≤ s.sp.toNat - 16
    omega
  · show WP isa (scryptBody name pbk) (VG.Proof.Scrypt.AArch64.Whole.entered s) _
    refine WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.Whole.entry_ok h) fun t ⟨hc, he⟩ => ?_)
    refine WP.mono (VG.Proof.Scrypt.AArch64.Whole.rest_ok hv hd name hL hc he) fun u ⟨hu, ho⟩ => ?_
    have lr : u.mem.read (u.sp + BitVec.ofNat 64 64) 8 = s.gpr .x30 := by
      rw [hu.sp, VG.Proof.Scrypt.AArch64.Whole.add_add, VG.Proof.Scrypt.AArch64.Whole.read8]; exact hu.kept.lr
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ho⟩
    · show ((freed 64 u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 64) 8)).gpr r = _
      rw [lr, RegUpd.gpr_write]
      by_cases h30 : r = .x30
      · subst r; simp only [ite_true, BitVec.setWidth_eq]
      · simp only [h30, ite_false]
        exact hu.cs r hr h30
    · show u.sp + BitVec.ofNat 64 64 + BitVec.ofNat 64 16 = s.sp
      rw [hu.sp, VG.Proof.Scrypt.AArch64.Whole.add_add, VG.Proof.Scrypt.AArch64.Whole.add_add]
      exact VG.Proof.Scrypt.AArch64.Whole.lay_top s
    · show (((freed 64 u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 64) 8)).v r).extractLsb' 0 64 = _
      rw [RegUpd.v_write]
      exact hu.vs r hr

end

end VG.Proof.Scrypt.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Verified`. -/
section

section

/-!
# scrypt on AArch64: constant time, up to the indices `j`

As on x86-64 (`Proof/Scrypt/X86_64/Whole/CT.lean`): two runs whose public data
agree have the same layout, so between the frames' pushes and pops they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs), whatever their secrets, and the indices of all the scryptROMix
calls agree (`LeakEq`). The blocks address only the stack, from `sp` (the
taint analysis); each call is of constant-time code whose public data agree
(`RelCT.call`); the loop's branch agrees since both runs count the same
blocks. The frames leak only `sp` (`frame_ct`, `alloc_ct`).
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {m₁ m₂ : Mem} (h : VG.Proof.Scrypt.AArch64.Whole.LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.AArch64.Whole.X L m₁ k) = roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.AArch64.Whole.X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  simp only [VG.Proof.Scrypt.AArch64.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : VG.Proof.Scrypt.AArch64.Whole.Lay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  v₁ : VReg → BitVec 128
  v₂ : VReg → BitVec 128
  m₁ : Mem
  m₂ : Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : VG.Proof.Scrypt.AArch64.Whole.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : VG.Proof.Scrypt.AArch64.Whole.Env, e.L.Ok ∧ VG.Proof.Scrypt.AArch64.Whole.LeakEq e.L e.m₁ e.m₂ ∧ VG.Proof.Scrypt.AArch64.Whole.Ctx e.L e.g₁ e.v₁ e.m₁ a ∧ VG.Proof.Scrypt.AArch64.Whole.Ctx e.L e.g₂ e.v₂ e.m₂ b ∧
    Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Scrypt.AArch64.Whole.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Scrypt.AArch64.Whole.Lay) g vv m₀ (t : State), L.Ok → VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two Φ) c (VG.Proof.Scrypt.AArch64.Whole.Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem sp_two {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128}
    {m₁ m₂ : Mem} (c₁ : VG.Proof.Scrypt.AArch64.Whole.Ctx L g₁ v₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.AArch64.Whole.Ctx L g₂ v₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- A block whose addresses depend only on `sp`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : VG.Proof.Scrypt.AArch64.Whole.Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs []) (.block is) hc).isSome = true)
    (hw : ∀ (L : VG.Proof.Scrypt.AArch64.Whole.Lay) g vv m₀ (t : State), L.Ok → VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two Φ) (.block is) (VG.Proof.Scrypt.AArch64.Whole.Two Ψ) :=
  VG.Proof.Scrypt.AArch64.Whole.two_wp (RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => ⟨VG.Proof.Scrypt.AArch64.Whole.sp_two c₁ c₂, fun _ hr => False.elim (by simp at hr)⟩) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : VG.Proof.Scrypt.AArch64.Whole.Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Scrypt.AArch64.Whole.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Scrypt.AArch64.Whole.Lay) g vv m₀ (t : State), L.Ok → VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : VG.Proof.Scrypt.AArch64.Whole.Lay) t₁ t₂ g₁ g₂ v₁ v₂ m₁ m₂, L.Ok → VG.Proof.Scrypt.AArch64.Whole.LeakEq L m₁ m₂ → VG.Proof.Scrypt.AArch64.Whole.Ctx L g₁ v₁ m₁ t₁ →
      VG.Proof.Scrypt.AArch64.Whole.Ctx L g₂ v₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : VG.Proof.Scrypt.AArch64.Whole.Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, VG.Proof.Scrypt.AArch64.Whole.Within r R)
    (hwsub : ∀ (L : VG.Proof.Scrypt.AArch64.Whole.Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, VG.Proof.Scrypt.AArch64.Whole.InBuf L r)
    (hw : ∀ (L : VG.Proof.Scrypt.AArch64.Whole.Lay) g vv m₀ (t : State), L.Ok → VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => VG.Proof.Scrypt.AArch64.Whole.Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two Φ) (.call n c) (VG.Proof.Scrypt.AArch64.Whole.Two Ψ) :=
  VG.Proof.Scrypt.AArch64.Whole.two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
    have w₁ := VG.Proof.Scrypt.AArch64.Whole.covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)
    have w₂ := VG.Proof.Scrypt.AArch64.Whole.covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)
    exact RelCT.call (n := n) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
          hpub _ _ _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, w₁.1, w₁.2, w₂.1, w₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-! ## The calls -/

theorem pbk_pub_two {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    {t₁ t₂ : State} (c₁ : VG.Proof.Scrypt.AArch64.Whole.Ctx L g₁ v₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.AArch64.Whole.Ctx L g₂ v₂ m₂ t₂) {salt : Addr} {sl : BitVec 64}
    {out : Addr} {ol : BitVec 64} (a₁ : VG.Proof.Scrypt.AArch64.Whole.PbkArgs L salt sl out ol t₁) (a₂ : VG.Proof.Scrypt.AArch64.Whole.PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (VG.Proof.Scrypt.AArch64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.AArch64.Whole.pbkWr L out ol))
      (t₂.callEntry.withRegions (VG.Proof.Scrypt.AArch64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.AArch64.Whole.pbkWr L out ol)) := by
  simp only [VG.Proof.Scrypt.AArch64.Whole.pbkK, Proof.Pbkdf2.Md.AArch64.pbkG, VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs), a₁.x0, a₁.x1, a₁.x2, a₁.x3, a₁.x4, a₁.x5, a₁.x6,
    a₁.x7, a₂.x0, a₂.x1, a₂.x2, a₂.x3, a₂.x4, a₂.x5, a₂.x6, a₂.x7, c₁.ce_sp, c₂.ce_sp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {m₀ : Mem} {t : State} {i : Nat} (hi : i < L.pp) (hb : VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ i t) (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) (128 * L.r.toNat) = VG.Proof.Scrypt.AArch64.Whole.X L m₀ i := by
  rw [State.withRegions_mem, State.callEntry_mem, hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : VG.Proof.Scrypt.AArch64.Whole.Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128}
    {m₁ m₂ : Mem} {t₁ t₂ : State} (hk : VG.Proof.Scrypt.AArch64.Whole.LeakEq L m₁ m₂) (c₁ : VG.Proof.Scrypt.AArch64.Whole.Ctx L g₁ v₁ m₁ t₁)
    (c₂ : VG.Proof.Scrypt.AArch64.Whole.Ctx L g₂ v₂ m₂ t₂) {i : Nat} (hi : i < L.pp) (b₁ : VG.Proof.Scrypt.AArch64.Whole.InvB L m₁ i t₁) (b₂ : VG.Proof.Scrypt.AArch64.Whole.InvB L m₂ i t₂)
    (a₁ : VG.Proof.Scrypt.AArch64.Whole.RomixArgs L (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) t₁) (a₂ : VG.Proof.Scrypt.AArch64.Whole.RomixArgs L (VG.Proof.Scrypt.AArch64.Whole.blkAt L i) t₂) :
    Proof.Scrypt.roMixAArch64.pub (t₁.callEntry.withRegions [] (VG.Proof.Scrypt.AArch64.Whole.romixWr L i))
      (t₂.callEntry.withRegions [] (VG.Proof.Scrypt.AArch64.Whole.romixWr L i)) := by
  simp only [Proof.Scrypt.roMixAArch64, VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    VG.Proof.Scrypt.AArch64.Whole.gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), a₁.x0, a₁.x1, a₁.x2, a₁.x3, a₁.x4, a₁.x5, a₂.x0,
    a₂.x1, a₂.x2, a₂.x3, a₂.x4, a₂.x5, c₁.ce_sp, c₂.ce_sp, true_and,
    VG.Proof.Scrypt.AArch64.Whole.romix_bytes hi b₁, VG.Proof.Scrypt.AArch64.Whole.romix_bytes hi b₂]
  exact VG.Proof.Scrypt.AArch64.Whole.leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : VG.Proof.Scrypt.AArch64.Whole.Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two (VG.Proof.Scrypt.AArch64.Whole.LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.AArch64.roMix) (.block nextBlock)))
      (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .x11 != 0) = decide (L.pp - n + 1 ≠ L.pp)) := by
  have a : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two (VG.Proof.Scrypt.AArch64.Whole.LoopAt n)) (.block romixArgs) (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ (L.pp - n) t ∧ VG.Proof.Scrypt.AArch64.Whole.RomixArgs L (VG.Proof.Scrypt.AArch64.Whole.blkAt L (L.pp - n)) t) :=
    VG.Proof.Scrypt.AArch64.Whole.two_blk (by taint_decide) fun _ _ _ _ _ hL hc ⟨h0, hn, hb⟩ =>
      WP.mono (VG.Proof.Scrypt.AArch64.Whole.romixArgs_ok hL hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ (L.pp - n) t ∧
      VG.Proof.Scrypt.AArch64.Whole.RomixArgs L (VG.Proof.Scrypt.AArch64.Whole.blkAt L (L.pp - n)) t) (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix)
      (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.AArch64.Whole.Mid L m₀ (L.pp - n) t) :=
    VG.Proof.Scrypt.AArch64.Whole.two_call RoMix.roMix_correct RoMix.roMix_ct (fun _ => []) (fun L => VG.Proof.Scrypt.AArch64.Whole.romixWr L (L.pp - n))
      (fun _ _ _ _ _ hL hc ⟨h0, hn, _, ha⟩ => VG.Proof.Scrypt.AArch64.Whole.romix_pre hL hc (by omega) ha)
      (fun _ _ _ _ _ _ _ _ _ _ hk c₁ c₂ ⟨h0, hn, b₁, a₁⟩ ⟨_, _, b₂, a₂⟩ =>
        VG.Proof.Scrypt.AArch64.Whole.romix_pub_two hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ hL ⟨h0, hn, _⟩ => VG.Proof.Scrypt.AArch64.Whole.romix_sub hL (by omega))
      (fun _ _ _ hL ⟨h0, hn, _⟩ => VG.Proof.Scrypt.AArch64.Whole.romix_wsub hL (by omega))
      (fun _ _ _ _ _ hL hc ⟨h0, hn, hb, ha⟩ =>
        WP.mono (VG.Proof.Scrypt.AArch64.Whole.call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.AArch64.Whole.Mid L m₀ (L.pp - n) t) (.block nextBlock)
      (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .x11 != 0) = decide (L.pp - n + 1 ≠ L.pp)) :=
    VG.Proof.Scrypt.AArch64.Whole.two_blk (by taint_decide) fun _ _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      WP.mono (VG.Proof.Scrypt.AArch64.Whole.next_step hL (by omega) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', h0, hn, hb, hz⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ 0 t) romixLoop (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval (.nonzero .x .x11) x = some (x.gpr .x11 != 0) := fun x =>
    Proof.MdStream.AArch64.eval_nonzero x .x11
  have h := fun n => RelCT.loop (M := isa) (c := .nonzero .x .x11)
    (Q := VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ L.pp t)
    (fun n => VG.Proof.Scrypt.AArch64.Whole.Two (VG.Proof.Scrypt.AArch64.Whole.LoopAt n)) (fun n => (VG.Proof.Scrypt.AArch64.Whole.body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨h0, hn, b₁, z₁⟩, ⟨-, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show VG.Proof.Scrypt.AArch64.Whole.InvB e.L _ e.L.pp a from hl ▸ b₁,
          show VG.Proof.Scrypt.AArch64.Whole.InvB e.L _ e.L.pp b from hl ▸ b₂⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, c₁, c₂, ⟨by omega, by omega, e₁ ▸ b₁⟩,
          ⟨by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, b₁, b₂⟩ => ⟨e.L.pp, e, hL, hk, c₁, c₂,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (a b : State) : Prop :=
  ∃ s₁ s₂, Proof.Scrypt.scryptAArch64.pre s₁ ∧ Proof.Scrypt.scryptAArch64.pre s₂ ∧
    Proof.Scrypt.scryptAArch64.pub s₁ s₂ ∧ a = VG.Proof.Scrypt.AArch64.Whole.entered s₁ ∧ b = VG.Proof.Scrypt.AArch64.Whole.entered s₂

theorem save_ct : RelCT isa VG.Proof.Scrypt.AArch64.Whole.Entered (.block saveArgs) (VG.Proof.Scrypt.AArch64.Whole.Two fun L _ t => VG.Proof.Scrypt.AArch64.Whole.Entry L t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp, hlk⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (VG.Proof.Scrypt.AArch64.Whole.entered s₁).sp = (VG.Proof.Scrypt.AArch64.Whole.entered s₂).sp; rw [VG.Proof.Scrypt.AArch64.Whole.entered_sp, VG.Proof.Scrypt.AArch64.Whole.entered_sp]; simp only [VG.Proof.Scrypt.AArch64.Whole.lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := VG.Proof.Scrypt.AArch64.Whole.entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := VG.Proof.Scrypt.AArch64.Whole.entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : VG.Proof.Scrypt.AArch64.Whole.lay s₂ = VG.Proof.Scrypt.AArch64.Whole.lay s₁ := by
    simp only [VG.Proof.Scrypt.AArch64.Whole.lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp]
  refine ⟨ht, ⟨VG.Proof.Scrypt.AArch64.Whole.lay s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, VG.Proof.Scrypt.AArch64.Whole.lay_ok h₁, ?_, y₁.1, e ▸ y₂.1, y₁.2,
    e ▸ y₂.2⟩
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h6, ← a0] at hlk
  exact hlk

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

theorem rest_ct : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L _ t => VG.Proof.Scrypt.AArch64.Whole.Entry L t)
    (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop (pbkCall name pbk pbk2Args))))
    fun _ _ => True := by
  have p1a : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L _ t => VG.Proof.Scrypt.AArch64.Whole.Entry L t) (.block pbk1Args)
      (VG.Proof.Scrypt.AArch64.Whole.Two fun L _ t => VG.Proof.Scrypt.AArch64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    VG.Proof.Scrypt.AArch64.Whole.two_blk (by taint_decide) fun _ _ _ _ _ hL hc he =>
      WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk1Args_ok hL hc he) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L _ t => VG.Proof.Scrypt.AArch64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.AArch64.Whole.X L m₀ k) :=
    VG.Proof.Scrypt.AArch64.Whole.two_call (VG.Proof.Scrypt.AArch64.Whole.pbk_correct hv) (VG.Proof.Scrypt.AArch64.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.AArch64.Whole.pbkRd L L.salt L.sl)
      (fun L => VG.Proof.Scrypt.AArch64.Whole.pbkWr L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ _ hL hc ha => VG.Proof.Scrypt.AArch64.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.AArch64.Whole.pbk1_regions hL))
      (fun _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => VG.Proof.Scrypt.AArch64.Whole.pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => VG.Proof.Scrypt.AArch64.Whole.pbk_sub hL (VG.Proof.Scrypt.AArch64.Whole.pbk1_regions hL)) (fun _ _ _ hL _ => VG.Proof.Scrypt.AArch64.Whole.pbk_wsub hL (VG.Proof.Scrypt.AArch64.Whole.pbk1_regions hL))
      (fun _ _ _ _ _ hL hc ha =>
        WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk1_call_ok hv hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.AArch64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.AArch64.Whole.X L m₀ k)
      (.block cur0) (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ 0 t) :=
    VG.Proof.Scrypt.AArch64.Whole.two_blk (by taint_decide) fun _ _ _ _ _ hL hc hx => VG.Proof.Scrypt.AArch64.Whole.start_ok hL hc hx
  have p2a : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.AArch64.Whole.InvB L m₀ L.pp t) (.block pbk2Args)
      (VG.Proof.Scrypt.AArch64.Whole.Two fun L _ t => VG.Proof.Scrypt.AArch64.Whole.PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    VG.Proof.Scrypt.AArch64.Whole.two_blk (by taint_decide) fun _ _ _ _ _ hL hc _ =>
      WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (VG.Proof.Scrypt.AArch64.Whole.Two fun L _ t => VG.Proof.Scrypt.AArch64.Whole.PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (VG.Proof.Scrypt.AArch64.Whole.Two fun _ _ _ => True) :=
    VG.Proof.Scrypt.AArch64.Whole.two_call (VG.Proof.Scrypt.AArch64.Whole.pbk_correct hv) (VG.Proof.Scrypt.AArch64.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.AArch64.Whole.pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => VG.Proof.Scrypt.AArch64.Whole.pbkWr L L.out L.ol)
      (fun _ _ _ _ _ hL hc ha => VG.Proof.Scrypt.AArch64.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.AArch64.Whole.pbk2_regions hL))
      (fun _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => VG.Proof.Scrypt.AArch64.Whole.pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => VG.Proof.Scrypt.AArch64.Whole.pbk_sub hL (VG.Proof.Scrypt.AArch64.Whole.pbk2_regions hL)) (fun _ _ _ hL _ => VG.Proof.Scrypt.AArch64.Whole.pbk_wsub hL (VG.Proof.Scrypt.AArch64.Whole.pbk2_regions hL))
      (fun _ _ _ _ _ hL hc ha =>
        WP.mono (VG.Proof.Scrypt.AArch64.Whole.pbk_call hv hd name hL hc ha (VG.Proof.Scrypt.AArch64.Whole.pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  exact ((p1a.seq p1c).seq (c0.seq (loop_ct.seq (p2a.seq p2c)))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptAArch64.pre Proof.Scrypt.scryptAArch64.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (RelCT.alloc (R := fun _ _ => True) ?_))
  refine (save_ct.seq (VG.Proof.Scrypt.AArch64.Whole.rest_ct hv hd name)).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end

end VG.Proof.Scrypt.AArch64.Whole

end

/-!
# scrypt on AArch64: the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract whose frames nest at most once, is verified against
`Spec.Scrypt.scryptContract` for the 96 bytes of stack its frames and calls
use (`scrypt_verified_of`); and so is the one calling the PBKDF2 made with an
implementation `c` of SHA-256's compression function (`scrypt_verified`).
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
words at `0x90000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x20000 | .x4 => 1 | .x5 => 0x30000 | .x6 => 1 | .x7 => 0x40000
    | _ => 0
  sp := 0x90000
  mem a := if a = 0x90000 then 2 else if a = 0x9000A then 5 else if a = 0x90010 then 17
    else if a = 0x9001A then 6 else if a = 0x90020 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90000, 40⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptAArch64.Implies (Spec.Scrypt.scryptContract AArch64.abi 96) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 h4 h5 h6 h7 a0 a1 a2 a3
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, AArch64.abi, AArch64.argRegs,
          _root_.List.range, _root_.List.range.loop, List.append_eq, VG.Proof.Scrypt.AArch64.Whole.satState] [satState] using VG.Proof.Scrypt.AArch64.Whole.satState }

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified AArch64.target (scrypt name pbk) (Spec.Scrypt.scryptContract AArch64.abi 96) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := VG.Proof.Scrypt.AArch64.Whole.scrypt_ok hv hd name h
    exact ⟨t, s', he, hp⟩) (VG.Proof.Scrypt.AArch64.Whole.scrypt_ct hv hd name) VG.Proof.Scrypt.AArch64.Whole.scrypt_implies

end

/-! ## With PBKDF2 made with an implementation of SHA-256's compression function -/

open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (hmacInit_fdepth hmacFin_fdepth iterate_fdepth)

/-- How deeply frames nest in `pbkdf2`. -/
theorem pbkdf2_fdepth {H : Hash} (hi : H.initC.aarch64Depth ≤ 1) (hu : H.updC.aarch64Depth ≤ 1)
    (hf : H.finC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) : H.pbkdf2.aarch64Depth ≤ 1 := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Code.aarch64Depth, Nat.max_le, Nat.zero_le, and_true, true_and]
  exact ⟨⟨hi, hu, hf⟩, ⟨hmacInit_fdepth hi hc, hu⟩, hu, hmacFin_fdepth hf hc, iterate_fdepth hc⟩

variable (c : Proof.Sha256.AArch64.Compress)

/-- PBKDF2-HMAC-SHA256 made with `c`. -/
abbrev pbkOf : Prog isa := (Proof.Pbkdf2.Md.AArch64.Sha256.hash c).pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2ScratchApi.name ++ c.suffix

theorem pbk_verified :
    Verified AArch64.target (VG.Proof.Scrypt.AArch64.Whole.pbkOf c) (Spec.Hmac.sha256I.pbkdf2ScratchContract AArch64.abi 16) :=
  (Proof.Pbkdf2.Md.AArch64.Sha256.variant c).pbkdf2

theorem pbk_depth : (VG.Proof.Scrypt.AArch64.Whole.pbkOf c).aarch64Depth ≤ 1 :=
  VG.Proof.Scrypt.AArch64.Whole.pbkdf2_fdepth (Proof.Pbkdf2.Md.AArch64.Sha256.streamOK c).initDepth
    (Proof.Pbkdf2.Md.AArch64.Sha256.streamOK c).updDepth (Proof.Pbkdf2.Md.AArch64.Sha256.streamOK c).finDepth
    c.noFrames

/-- `vg_scrypt` made with `c`. -/
theorem scrypt_verified :
    Verified AArch64.target (scrypt (VG.Proof.Scrypt.AArch64.Whole.pbkName c) (VG.Proof.Scrypt.AArch64.Whole.pbkOf c)) (Spec.Scrypt.scryptContract AArch64.abi 96) :=
  VG.Proof.Scrypt.AArch64.Whole.scrypt_verified_of (VG.Proof.Scrypt.AArch64.Whole.pbk_verified c) (VG.Proof.Scrypt.AArch64.Whole.pbk_depth c) (VG.Proof.Scrypt.AArch64.Whole.pbkName c)

end VG.Proof.Scrypt.AArch64.Whole

end
