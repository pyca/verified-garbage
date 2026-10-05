import VerifiedGarbage.Impl.Scrypt.X86_64.Scrypt
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixCT
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Layout`. -/
section

/-!
# scrypt on x86-64: where everything is

The contract the proof is written against (`scryptX86_64`), the function's
buffers and the 88 bytes of stack below its return address, from `B` up
(`Lay`): the 32 bytes the calls use, then the frame (56 bytes, from `B + 32`:
PBKDF2's two stack arguments, the next block, then the password, its length,
`r` and `b`). Our own stack arguments are at `B + 96`. `Ctx` is what holds
between the frame's push and pop: the permissions, `rsp`, the callee-saved
registers, the words the calls cannot change (`Kept`), and that memory changed
only in the writable buffers and the stack. `call_ok` runs a call of verified
code in such a state.
-/

namespace VG.Proof.Scrypt

open VG.X86_64 in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. x86-64 contract for
`vg_scrypt(password = rdi, password_len = rsi, salt = rdx, salt_len = rcx,
r = r8, b = r9, blen, v, vlen, scratch, slen, out, out_len)`, the last seven
on the stack, with 88 bytes of stack below the return address. -/
def scryptX86_64 : Contract X86_64.isa where
  pre s :=
    let blen := stackArg s 0
    let v := stackArg s 1
    let vlen := stackArg s 2
    let sc := stackArg s 3
    let slen := stackArg s 4
    let out := stackArg s 5
    let ol := stackArg s 6
    let r := (s.gpr .r8).toNat
    let pwR : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let saltR : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let bR : Region := ⟨s.gpr .r9, blen.toNat * 128⟩
    let vR : Region := ⟨v, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 56⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 88, 88⟩
    88 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    ret.Disjoint pwR ∧ ret.Disjoint saltR ∧ ret.Disjoint bR ∧ ret.Disjoint vR ∧ ret.Disjoint scR ∧
    ret.Disjoint outR ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + blen.toNat * 128 ≤ 2 ^ 64 ∧ v.toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ blen.toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r (blen.toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .r8).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((stackArg s 2).toNat / r) r
      ((stackArg s 0).toNat / r) (stackArg s 6).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 5) (stackArg s 6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
    stackArg s₁ 6 = stackArg s₂ 6 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat) (s₁.gpr .r8).toNat
        ((stackArg s₁ 0).toNat / (s₁.gpr .r8).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .r8).toNat ((stackArg s₁ 2).toNat / (s₁.gpr .r8).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat) (s₂.gpr .r8).toNat
        ((stackArg s₂ 0).toNat / (s₂.gpr .r8).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .r8).toNat ((stackArg s₂ 2).toNat / (s₂.gpr .r8).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64

/-- The arguments and the lowest byte of the stack used (`rsp - 88` on entry). -/
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

variable (L : VG.Proof.Scrypt.X86_64.Whole.Lay)

abbrev PW : Region := ⟨L.pw, L.pwl.toNat⟩
abbrev SALT : Region := ⟨L.salt, L.sl.toNat⟩
abbrev BB : Region := ⟨L.b, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨L.v, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨L.scr, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨L.out, L.ol.toNat⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 96, 56⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 88⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 32, 56⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 88, 8⟩

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
  np : L.pw.toNat + L.pwl.toNat ≤ 2 ^ 64
  ns : L.salt.toNat + L.sl.toNat ≤ 2 ^ 64
  nb : L.b.toNat + L.blen.toNat * 128 ≤ 2 ^ 64
  nv : L.v.toNat + L.vlen.toNat * 128 ≤ 2 ^ 64
  nc : L.scr.toNat + L.slen.toNat * 128 ≤ 2 ^ 64
  no : L.out.toNat + L.ol.toNat ≤ 2 ^ 64
  nB : L.B.toNat + 152 ≤ 2 ^ 64
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

theorem Within.sub {r R : Region} (h : VG.Proof.Scrypt.X86_64.Whole.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    VG.Proof.Scrypt.X86_64.Whole.Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : VG.Proof.Scrypt.X86_64.Whole.Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem within_fr (B : Addr) {d n : Nat} (h₁ : 32 ≤ d) (h₂ : d + n ≤ 88) :
    VG.Proof.Scrypt.X86_64.Whole.Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 32, 56⟩ :=
  ⟨d - 32, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.X86_64.Whole.Lay} (h : L.Ok)
include h

/-- The stack and the stack arguments do not wrap around. -/
theorem nB' : L.B.toNat + 152 ≤ 2 ^ 64 := h.nB

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_buf {d n : Nat} (h₁ : d + n ≤ 88) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hr
  · exact (h.kv.sub_left hs).sub_right hr
  · exact (h.kc.sub_left hs).sub_right hr
  · exact (h.ko.sub_left hs).sub_right hr

/-- A range in our stack arguments is disjoint from one in a writable buffer. -/
theorem args_buf {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 152) {R : Region}
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

/-- The words in the frame and our stack arguments that stay as they are
between the frame's push and pop. -/
structure Kept (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (m : Mem) : Prop where
  pw : m.readW (L.B + BitVec.ofNat 64 56) 64 = L.pw
  pwl : m.readW (L.B + BitVec.ofNat 64 64) 64 = L.pwl
  r : m.readW (L.B + BitVec.ofNat 64 72) 64 = L.r
  b : m.readW (L.B + BitVec.ofNat 64 80) 64 = L.b
  blen : m.readW (L.B + BitVec.ofNat 64 96) 64 = L.blen
  v : m.readW (L.B + BitVec.ofNat 64 104) 64 = L.v
  vlen : m.readW (L.B + BitVec.ofNat 64 112) 64 = L.vlen
  scr : m.readW (L.B + BitVec.ofNat 64 120) 64 = L.scr
  out : m.readW (L.B + BitVec.ofNat 64 136) 64 = L.out
  ol : m.readW (L.B + BitVec.ofNat 64 144) 64 = L.ol

/-- The kept words survive changes to memory that miss them. -/
theorem Kept.frame {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {m m' : Mem} {rs : List Region} (hk : VG.Proof.Scrypt.X86_64.Whole.Kept L m) (hf : Frame rs m m')
    (hd : ∀ d, (56 ≤ d ∧ d + 8 ≤ 88) ∨ (96 ≤ d ∧ d + 8 ≤ 152) → ∀ R ∈ rs,
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R) : VG.Proof.Scrypt.X86_64.Whole.Kept L m' := by
  have k : ∀ d, (56 ≤ d ∧ d + 8 ≤ 88) ∨ (96 ≤ d ∧ d + 8 ≤ 152) →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 56 (by omega)).trans hk.pw, (k 64 (by omega)).trans hk.pwl, (k 72 (by omega)).trans hk.r,
    (k 80 (by omega)).trans hk.b, (k 96 (by omega)).trans hk.blen, (k 104 (by omega)).trans hk.v,
    (k 112 (by omega)).trans hk.vlen, (k 120 (by omega)).trans hk.scr,
    (k 136 (by omega)).trans hk.out, (k 144 (by omega)).trans hk.ol⟩

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. (No instruction loads MXCSR: see `abiPreserved_of_exec`.) -/
structure Ctx (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 32
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  kept : VG.Proof.Scrypt.X86_64.Whole.Kept L t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- `B + 32 - 8 = B + 24`. -/
theorem sub8 (B : Addr) : B + BitVec.ofNat 64 32 - 8 = B + BitVec.ofNat 64 24 := by
  bv_omega

/-- The stack a call from `rsp = B + 32` uses, if it nests calls at most four deep. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 32) :
    Region.Sub (below (B + BitVec.ofNat 64 32) m) ⟨B, 32⟩ := by
  have : B + BitVec.ofNat 64 32 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (32 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 32) (a := m) (b := 32) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 32 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : VG.Proof.Scrypt.X86_64.Whole.Lay) : List Region := [L.PW, L.SALT, L.ARGS, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-- A writable region is within one of the writable buffers. -/
def InBuf (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (r : Region) : Prop :=
  VG.Proof.Scrypt.X86_64.Whole.Within r L.BB ∨ VG.Proof.Scrypt.X86_64.Whole.Within r L.VV ∨ VG.Proof.Scrypt.X86_64.Whole.Within r L.SC ∨ VG.Proof.Scrypt.X86_64.Whole.Within r L.OUT

theorem InBuf.sub {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {r : Region} (h : VG.Proof.Scrypt.X86_64.Whole.InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

theorem covers {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {g : Reg → BitVec 64} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86_64.Whole.Within r R) (hwsub : ∀ r ∈ wr, VG.Proof.Scrypt.X86_64.Whole.InBuf L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call of verified code (see `WP.call`), which nests calls at most three
times more and is given regions within ours to read, and within the
writable buffers to write: afterwards `Ctx` holds again, memory changed only
within what it writes and the 32 bytes below `rsp`, and the callee's
postcondition holds. -/
theorem call_ok {L : VG.Proof.Scrypt.X86_64.Whole.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 3) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86_64.Whole.Within r R) (hwsub : ∀ r ∈ wr, VG.Proof.Scrypt.X86_64.Whole.InBuf L r)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ s' → Frame (wr ++ [⟨L.B, 32⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := VG.Proof.Scrypt.X86_64.Whole.covers hc hsub hwsub
  refine WP.call hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost => ?_
  have hf' : Frame (wr ++ [⟨L.B, 32⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact VG.Proof.Scrypt.X86_64.Whole.below_call_sub _ (by omega)
  have hnB := hL.nB
  -- The regions the call may change miss the kept words.
  have hdisj : ∀ d, (56 ≤ d ∧ d + 8 ≤ 88) ∨ (96 ≤ d ∧ d + 8 ≤ 152) → ∀ R ∈ wr ++ [⟨L.B, 32⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R := by
    intro d hdd R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨R', hR', hs⟩ := (hwsub R hR).sub
      rcases hdd with hdd | hdd
      · exact hL.stk_buf (by omega) hR' hs
      · exact hL.args_buf (by omega) (by omega) hR' hs
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hc.kept.frame hf' hdisj, hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨R', hR', hs⟩ := (hwsub r hr).sub
      rcases hR' with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 32) (k := 88) (by omega)
      simpa using this

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Scrypt.X86_64.Whole.Lay :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, stackArg s 0, stackArg s 1,
    stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    s.gpr .rsp - BitVec.ofNat 64 88⟩

theorem lay_ret (s : State) : (VG.Proof.Scrypt.X86_64.Whole.lay s).B + BitVec.ofNat 64 88 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (VG.Proof.Scrypt.X86_64.Whole.lay s).B + BitVec.ofNat 64 96 = stackArgAddr s 0 := by
  simp only [VG.Proof.Scrypt.X86_64.Whole.lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptX86_64.pre s) : (VG.Proof.Scrypt.X86_64.Whole.lay s).Ok := by
  obtain ⟨h88, h64, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    rp, rs, rb, rv, rc, ro, kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval,
    olb, slen⟩ := h
  have e : (VG.Proof.Scrypt.X86_64.Whole.lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, VG.Proof.Scrypt.X86_64.Whole.lay_ret]
  have ea : (VG.Proof.Scrypt.X86_64.Whole.lay s).ARGS = ⟨stackArgAddr s 0, 56⟩ := by simp only [Lay.ARGS, VG.Proof.Scrypt.X86_64.Whole.lay_args]
  have nB : (VG.Proof.Scrypt.X86_64.Whole.lay s).B.toNat + 152 ≤ 2 ^ 64 := by
    simp only [VG.Proof.Scrypt.X86_64.Whole.lay]
    rw [Offset.toNat_sub_ofNat (s.gpr .rsp) 88]
    omega
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    e ▸ rp, e ▸ rs, e ▸ rb, e ▸ rv, e ▸ rc, e ▸ ro, kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, nB,
    rpos, bmod, vmod, hval, olb, slen⟩

/-! ## The frame's push -/

/-- The registers the frame's push stores. -/
abbrev pushRs : List Reg := [.r9, .r8, .rsi, .rdi, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 7) = sp - BitVec.ofNat 64 88 + BitVec.ofNat 64 32 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 4) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 88 + BitVec.ofNat 64 (80 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem arg_slot (s : State) (i : Nat) (hi : i < 7) :
    stackArgAddr s i = (VG.Proof.Scrypt.X86_64.Whole.lay s).B + BitVec.ofNat 64 (96 + 8 * i) := by
  simp only [stackArgAddr, VG.Proof.Scrypt.X86_64.Whole.lay]
  have : 8 * (i + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : Proof.Scrypt.scryptX86_64.pre s) :
    VG.Proof.Scrypt.X86_64.Whole.Ctx (VG.Proof.Scrypt.X86_64.Whole.lay s) s.gpr s.mem (pushed VG.Proof.Scrypt.X86_64.Whole.pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 7 ≤ _; have := h.1; omega
  have hL := VG.Proof.Scrypt.X86_64.Whole.lay_ok h
  have hnB := hL.nB
  obtain ⟨hf, hw⟩ := pushRegs_mem s VG.Proof.Scrypt.X86_64.Whole.pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 4), (pushed VG.Proof.Scrypt.X86_64.Whole.pushRs s).mem.readW ((VG.Proof.Scrypt.X86_64.Whole.lay s).B + BitVec.ofNat 64 (80 - 8 * j)) 64 =
      s.gpr (VG.Proof.Scrypt.X86_64.Whole.pushRs[j]'(by show j < 7; omega)) := fun j hj => by
    rw [← hw j (by show j < 7; omega)]; simp only [VG.Proof.Scrypt.X86_64.Whole.lay]; rw [VG.Proof.Scrypt.X86_64.Whole.push_slot _ j hj]; rfl
  have hfr : (⟨s.gpr .rsp - BitVec.ofNat 64 (8 * pushRs.length), 8 * pushRs.length⟩ : Region) =
      (VG.Proof.Scrypt.X86_64.Whole.lay s).FR := by
    simp only [List.length_cons, List.length_nil, Lay.FR, VG.Proof.Scrypt.X86_64.Whole.lay]; rw [VG.Proof.Scrypt.X86_64.Whole.push_base]
  rw [hfr] at hf
  have ha : ∀ i, i < 7 → (pushed VG.Proof.Scrypt.X86_64.Whole.pushRs s).mem.readW ((VG.Proof.Scrypt.X86_64.Whole.lay s).B + BitVec.ofNat 64 (96 + 8 * i)) 64 =
      stackArg s i := fun i hi => by
    rw [stackArg, VG.Proof.Scrypt.X86_64.Whole.arg_slot s i hi]
    refine hf.readW (Region.contains_self _ _) (fun R hR => ?_) (by decide)
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨by rw [pushed_rd, h.2.2.1, ← VG.Proof.Scrypt.X86_64.Whole.lay_args]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    ⟨hw' 3 (by omega), hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega),
      ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 5 (by omega),
      ha 6 (by omega)⟩, ?_⟩
  · rw [pushed_wr, hfr, h.2.2.2.1]; rfl
  · rw [pushed_rsp]; simp only [List.length_cons, List.length_nil, VG.Proof.Scrypt.X86_64.Whole.lay]; rw [VG.Proof.Scrypt.X86_64.Whole.push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(VG.Proof.Scrypt.X86_64.Whole.lay s).STK, by simp, Offset.sub_base _ (by omega)⟩

end VG.Proof.Scrypt.X86_64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Steps`. -/
section

/-!
# scrypt on x86-64: the blocks between the calls

The parameters as numbers (`Lay.Ok`), and what each block between the calls
does: it keeps `Ctx`, and sets up the next call's arguments (`PbkArgs`,
`RomixArgs`) or the next block.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt)

/-! ## Arithmetic -/

/-- Rotating right by 57 multiplies by 128 a number less than `2^57`. -/
theorem ror57 (x : BitVec 64) (h : x.toNat < 2 ^ 57) :
    x.rotateRight 57 = BitVec.ofNat 64 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show 57 % 64 = 57 from rfl, Nat.div_eq_of_lt h, Nat.zero_or]

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

namespace Lay.Ok

variable {L : VG.Proof.Scrypt.X86_64.Whole.Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem vlen_eq : L.vlen.toNat = L.r.toNat * L.NN := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.vmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1
theorem NN_pos : 0 < L.NN := by have := h.valid.1; omega

/-- `b` is not the whole address space, since the stack is not in it. -/
theorem blen_lt : L.blen.toNat * 128 < 2 ^ 64 :=
  VG.Proof.Scrypt.X86_64.Whole.toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 88; omega)
theorem vlen_lt : L.vlen.toNat * 128 < 2 ^ 64 :=
  VG.Proof.Scrypt.X86_64.Whole.toNat_le_of_disjoint h.kv.symm (by show (0 : Nat) < 88; omega)

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem blen57 : L.blen.toNat < 2 ^ 57 := by have := h.blen_lt; omega
theorem r57 : L.r.toNat < 2 ^ 57 := by have := h.blen57; have := h.r_le; omega

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

/-! ## In the frame -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_sp (t : State) (d : Nat) : t.ea (VG.Impl.Scrypt.X86_64.sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [VG.Proof.Scrypt.X86_64.Whole.ofInt_nat]

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem cs_keep {t : State} {d : Reg} (v : BitVec 64) (hd : d ∉ calleeSaved) :
    ∀ r ∈ calleeSaved, (t.setReg d v).gpr r = t.gpr r :=
  fun _ hr => RegUpd.gpr_setReg_of_ne _ _ (fun e => hd (e ▸ hr))

namespace Ctx

variable {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t)
include hc

theorem inFr {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 88) : InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 88) : InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inArgs (hL : L.Ok) {d : Nat} (h₁ : 96 ≤ d) (h₂ : d + 8 ≤ 152) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

/-- Code that writes only caller-saved registers. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hm]; exact hc.kept,
    by rw [hm]; exact hc.frame⟩

/-- Code that writes only caller-saved registers and the frame's first three words. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem) : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun d hd R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

/-- The registers the frame's body may write, and that `scrypt_cs_tac` steps through. -/
macro "scrypt_cs_tac" : tactic => `(tactic| (
  intro r hr
  revert hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))


/-! ## The blocks -/

section
variable {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, `c = 1`, and on the stack `ol`
and `scratch`. -/
structure PbkArgs (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  rdi : t.gpr .rdi = L.pw
  rsi : t.gpr .rsi = L.pwl
  rdx : t.gpr .rdx = salt
  rcx : t.gpr .rcx = sl
  r8 : t.gpr .r8 = (1 : BitVec 32).setWidth 64
  r9 : t.gpr .r9 = out
  a0 : t.mem.readW (L.B + BitVec.ofNat 64 32) 64 = ol
  a1 : t.mem.readW (L.B + BitVec.ofNat 64 40) 64 = L.scr

/-- The registers on entry to the frame's body. -/
structure Entry (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (t : State) : Prop where
  rdi : t.gpr .rdi = L.pw
  rsi : t.gpr .rsi = L.pwl
  rdx : t.gpr .rdx = L.salt
  rcx : t.gpr .rcx = L.sl
  r9 : t.gpr .r9 = L.b

theorem w32 (B : Addr) (m : Mem) (a c : BitVec 64) :
    let m' := (m.writeW (B + BitVec.ofNat 64 32) a).writeW (B + BitVec.ofNat 64 40) c
    Frame [⟨B + BitVec.ofNat 64 32, 24⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 32) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 40) 64 = c := by
  refine ⟨((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by omega) (by omega) (by omega)), ?_, Mem.readW_writeW_self64 _ _ _⟩
  rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64]

theorem pbk1Args_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) (he : VG.Proof.Scrypt.X86_64.Whole.Entry L t) :
    WP isa (.block pbk1Args) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      VG.Proof.Scrypt.X86_64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem := by
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  have w32' := hc.inFrW (d := 32) (by omega) (by omega)
  have w40 := hc.inFrW (d := 40) (by omega) (by omega)
  have r := VG.Proof.Scrypt.X86_64.Whole.ror57 _ (hL.blen57)
  apply WP.of_runBlock
  simp only [pbk1Args, times128, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc,
    readSrc32, State.load64, State.store64, State.setReg32, VG.Proof.Scrypt.X86_64.Whole.ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.mem_setFlags, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Scrypt.X86_64.Whole.add_add,
    Nat.reduceAdd, l96, l120, w32', w40, hc.kept.blen, hc.kept.scr, r, Option.some.injEq,
    exists_eq_left', show (1 ≤ 57 ∧ 57 ≤ 63) = True from by decide]
  obtain ⟨f, a0, a1⟩ := VG.Proof.Scrypt.X86_64.Whole.w32 L.B t.mem (BitVec.ofNat 64 (L.blen.toNat * 128)) L.scr
  refine ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, ⟨?_, ?_, ?_, ?_, rfl, ?_, a0, a1⟩, f⟩
  all_goals simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, ite_false]
  exacts [he.rdi, he.rsi, he.rdx, he.rcx, he.r9]

theorem cur0_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) :
    WP isa (.block cur0) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = L.b ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem := by
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have w48 := hc.inFrW (d := 48) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [cur0, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    State.store64, VG.Proof.Scrypt.X86_64.Whole.ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Scrypt.X86_64.Whole.add_add, Nat.reduceAdd, l80, w48,
    hc.kept.b, Option.some.injEq, exists_eq_left']
  have f : Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 48) L.b) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  exact ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, Mem.readW_writeW_self64 _ _ _, f⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (cur : Addr) (t : State) : Prop where
  rdi : t.gpr .rdi = cur
  rsi : t.gpr .rsi = L.r
  rdx : t.gpr .rdx = L.v
  rcx : t.gpr .rcx = L.vlen
  r8 : t.gpr .r8 = L.scr
  r9 : t.gpr .r9 = L.r + (2 : BitVec 32).signExtend 64

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Scrypt.X86_64.Whole.RomixArgs L cur t' := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l72 := hc.inFr (d := 72) (by omega) (by omega)
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  have l112 := hc.inArgs hL (d := 112) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [romixArgs, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, VG.Proof.Scrypt.X86_64.Whole.ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Scrypt.X86_64.Whole.add_add,
    Nat.reduceAdd, l48, l72, l104, l112, l120, hcur, hc.kept.r, hc.kept.v, hc.kept.vlen,
    hc.kept.scr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl (by scrypt_cs_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.zf = some (cur + BitVec.ofNat 64 (L.r.toNat * 128) -
        (BitVec.ofNat 64 (L.blen.toNat * 128) + L.b) == 0) := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have w48 := hc.inFrW (d := 48) (by omega) (by omega)
  have l72 := hc.inFr (d := 72) (by omega) (by omega)
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have r₁ := VG.Proof.Scrypt.X86_64.Whole.ror57 _ (hL.r57)
  have r₂ := VG.Proof.Scrypt.X86_64.Whole.ror57 _ (hL.blen57)
  apply WP.of_runBlock
  simp only [nextBlock, times128, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift,
    readSrc, State.load64, State.store64, VG.Proof.Scrypt.X86_64.Whole.ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.zf_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp,
    VG.Proof.Scrypt.X86_64.Whole.add_add, Nat.reduceAdd, l48, w48, l72, l80, l96, hcur, hc.kept.r, hc.kept.blen, hc.kept.b, r₁, r₂,
    Option.some.injEq, exists_eq_left', show (1 ≤ 57 ∧ 57 ≤ 63) = True from by decide]
  have f : Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem
      (t.mem.writeW (L.B + BitVec.ofNat 64 48) (cur + BitVec.ofNat 64 (L.r.toNat * 128))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  exact ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, f, Mem.readW_writeW_self64 _ _ _, trivial⟩

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) :
    WP isa (.block pbk2Args) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      VG.Proof.Scrypt.X86_64.Whole.PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem := by
  have l56 := hc.inFr (d := 56) (by omega) (by omega)
  have l64 := hc.inFr (d := 64) (by omega) (by omega)
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  have l136 := hc.inArgs hL (d := 136) (by omega) (by omega)
  have l144 := hc.inArgs hL (d := 144) (by omega) (by omega)
  have w32' := hc.inFrW (d := 32) (by omega) (by omega)
  have w40 := hc.inFrW (d := 40) (by omega) (by omega)
  have r := VG.Proof.Scrypt.X86_64.Whole.ror57 _ (hL.blen57)
  apply WP.of_runBlock
  simp only [pbk2Args, times128, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc,
    readSrc32, State.load64, State.store64, State.setReg32, VG.Proof.Scrypt.X86_64.Whole.ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.mem_setFlags, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, VG.Proof.Scrypt.X86_64.Whole.add_add,
    Nat.reduceAdd, l56, l64, l80, l96, l120, l136, l144, w32', w40, hc.kept.pw, hc.kept.pwl, hc.kept.b,
    hc.kept.blen, hc.kept.scr, hc.kept.out, hc.kept.ol, r, Option.some.injEq, exists_eq_left',
    show (1 ≤ 57 ∧ 57 ≤ 63) = True from by decide]
  obtain ⟨f, a0, a1⟩ := VG.Proof.Scrypt.X86_64.Whole.w32 L.B t.mem L.ol L.scr
  refine ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, ⟨?_, ?_, ?_, ?_, rfl, ?_, a0, a1⟩, f⟩
  all_goals simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, ite_false, ite_true]

end

end VG.Proof.Scrypt.X86_64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Calls`. -/
section

section

/-!
# scrypt on x86-64: PBKDF2-HMAC-SHA256 as a callee

`vg_pbkdf2_hmac_sha256_scratch` (any implementation of it) is verified against the
shared contract `VG.Spec.Hmac.sha256I.pbkdf2ScratchContract`; its caller works with
the same contract spelt out (`pbkG`, the contract its proof is written
against): `pbk_correct` and `pbk_ct` are its correctness and constant time
under `pbkG`, from its `Verified` proof.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (pbkG)

/-- `pbkdf2`'s contract, spelt out. -/
abbrev pbkK : Contract isa := pbkG Spec.Hmac.sha256S 200

theorem map_range2 {α : Type} (f : Nat → α) : List.map f (List.range 2) = [f 0, f 1] := rfl

theorem pbk_pre {s : State} (h : pbkK.pre s) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, VG.Proof.Scrypt.X86_64.Whole.map_range2, List.append_eq]
  sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, VG.Proof.Scrypt.X86_64.Whole.map_range2, List.append_eq]
  simp only [VG.Proof.Scrypt.X86_64.Whole.pbkK, pbkG, Spec.Hmac.sha256S] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

theorem pbk_post {s s' : State} (h : (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24).post s s') :
    pbkK.post s s' := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, VG.Proof.Scrypt.X86_64.Whole.map_range2, List.append_eq] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkK.pub s₁ s₂) :
    (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24).pub s₁ s₂ := by
  simp only [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    X86_64.abi, X86_64.argRegs, VG.Proof.Scrypt.X86_64.Whole.map_range2, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h9, h1, h2, h3, h4, h5, h6, h7, h8⟩

variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
include hv

theorem pbk_correct (s : State) (h : pbkK.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (VG.Proof.Scrypt.X86_64.Whole.pbk_pre h)
  exact ⟨t, s', he, ha, VG.Proof.Scrypt.X86_64.Whole.pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (VG.Proof.Scrypt.X86_64.Whole.pbk_pre h₁) (VG.Proof.Scrypt.X86_64.Whole.pbk_pre h₂) (VG.Proof.Scrypt.X86_64.Whole.pbk_pub hp) e₁ e₂

end VG.Proof.Scrypt.X86_64.Whole

end

/-!
# scrypt on x86-64: the calls

What a call of `vg_pbkdf2_hmac_sha256_scratch` (`pbk_call`) and of `vg_scrypt_romix`
(`romix_call`) from the frame does, from their arguments (`PbkArgs`,
`RomixArgs`): each keeps `Ctx`, and changes memory only in what it writes and
the stack below the frame. `pbk_pre` and `romix_pre` are their preconditions,
which the proof of constant time uses too.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Md.X86_64 (pbkG)

/-! ## Calls from the frame -/

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- Byte `i` of a region the return address of a call misses, on entry to the callee. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- The bytes of a region the return address of a call misses, on entry to the callee. -/
theorem ce_bytesAt (t : State) {p : Addr} {n : Nat} (hd : (below (t.gpr .rsp) 8).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt t.callEntry.mem p n = bytesAt t.mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => VG.Proof.Scrypt.X86_64.Whole.ce_byte t (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

section
variable {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {g : Reg → BitVec 64} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t)
include hc

/-- The return address of a call from the frame. -/
theorem ret : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 24, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 32 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [show L.B + BitVec.ofNat 64 32 - BitVec.ofNat 64 8 = L.B + BitVec.ofNat 64 24 from VG.Proof.Scrypt.X86_64.Whole.sub8 L.B]

theorem ce_rsp (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = L.B + BitVec.ofNat 64 24 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp, VG.Proof.Scrypt.X86_64.Whole.sub8]

/-- A word in the frame above the return address, on entry to the callee. -/
theorem ce_word (hL : L.Ok) (rd wr : List Region) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 88) :
    (t.callEntry.withRegions rd wr).mem.readW (L.B + BitVec.ofNat 64 d) 64 =
      t.mem.readW (L.B + BitVec.ofNat 64 d) 64 := by
  have := hL.nB
  rw [State.withRegions_mem, State.callEntry_mem, hc.rsp, VG.Proof.Scrypt.X86_64.Whole.sub8]
  exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

end Ctx

namespace Lay.Ok

variable (hL : L.Ok)
include hL

/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : VG.Proof.Scrypt.X86_64.Whole.InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs]

theorem stk_pw {d n : Nat} (h₁ : d + n ≤ 88) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.PW :=
  hL.kp.sub_left (Offset.sub_base _ h₁)

theorem stk_in {d n : Nat} (h₁ : d + n ≤ 88) {r : Region} (h : VG.Proof.Scrypt.X86_64.Whole.InBuf L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  exact hL.stk_buf h₁ hR hs

theorem scr_in : VG.Proof.Scrypt.X86_64.Whole.InBuf L ⟨L.scr, 200 * 8⟩ :=
  .inr (.inr (.inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen17; omega))))

end Lay.Ok

/-! ## PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (salt : Addr) (sl : BitVec 64) : List Region :=
  [L.PW, ⟨salt, sl.toNat⟩, ⟨L.B + BitVec.ofNat 64 32, 16⟩]
abbrev pbkWr (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (out : Addr) (ol : BitVec 64) : List Region :=
  [⟨out, ol.toNat⟩, ⟨L.scr, 200 * 8⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) : Prop where
  sw : ∃ R ∈ L.regions, VG.Proof.Scrypt.X86_64.Whole.Within ⟨salt, sl.toNat⟩ R
  ow : VG.Proof.Scrypt.X86_64.Whole.InBuf L ⟨out, ol.toNat⟩
  so : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨out, ol.toNat⟩
  sc : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨L.scr, 200 * 8⟩
  oc : Region.Disjoint ⟨out, ol.toNat⟩ ⟨L.scr, 200 * 8⟩
  ks : L.STK.Disjoint ⟨salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 64
  no : out.toNat + ol.toNat ≤ 2 ^ 64
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_e0 (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : VG.Proof.Scrypt.X86_64.Whole.PbkArgs L salt sl out ol t) (rd wr : List Region) :
    stackArg (t.callEntry.withRegions rd wr) 0 = ol := by
  rw [stackArg, stackArgAddr, hc.ce_rsp, VG.Proof.Scrypt.X86_64.Whole.add_add, hc.ce_word hL _ _ (by omega) (by omega), ha.a0]

theorem pbk_e1 (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : VG.Proof.Scrypt.X86_64.Whole.PbkArgs L salt sl out ol t) (rd wr : List Region) :
    stackArg (t.callEntry.withRegions rd wr) 1 = L.scr := by
  rw [stackArg, stackArgAddr, hc.ce_rsp, VG.Proof.Scrypt.X86_64.Whole.add_add, hc.ce_word hL _ _ (by omega) (by omega), ha.a1]

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : VG.Proof.Scrypt.X86_64.Whole.PbkArgs L salt sl out ol t) (hr : VG.Proof.Scrypt.X86_64.Whole.PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (VG.Proof.Scrypt.X86_64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol)) := by
  have hnB := hL.nB
  have e0 := VG.Proof.Scrypt.X86_64.Whole.pbk_e0 hL hc ha (VG.Proof.Scrypt.X86_64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol)
  have e1 := VG.Proof.Scrypt.X86_64.Whole.pbk_e1 hL hc ha (VG.Proof.Scrypt.X86_64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol)
  have ea : stackArgAddr (t.callEntry.withRegions (VG.Proof.Scrypt.X86_64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol)) 0 =
      L.B + BitVec.ofNat 64 32 := by
    rw [stackArgAddr, hc.ce_rsp, VG.Proof.Scrypt.X86_64.Whole.add_add]
  have es : L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 24 = L.B := BitVec.add_sub_cancel _ _
  have t24 : (L.B + BitVec.ofNat 64 24).toNat = L.B.toNat + 24 := toNat_add_ofNat _ (by omega)
  have hs := hr.sw
  simp only [VG.Proof.Scrypt.X86_64.Whole.pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr, e0, e1, ea,
    hc.ce_rsp, es, t24, VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), ha.rdi, ha.rsi,
    ha.rdx, ha.rcx, ha.r8, ha.r9]
  have sw : VG.Proof.Scrypt.X86_64.Whole.InBuf L ⟨L.scr, 200 * 8⟩ := hL.scr_in
  refine ⟨by omega, by omega, trivial, trivial, hL.pw_buf hr.ow, hL.pw_buf sw, hr.so, hr.sc, hr.oc,
    (hL.stk_in (d := 32) (n := 16) (by omega) hr.ow).symm,
    (hL.stk_in (d := 32) (n := 16) (by omega) sw).symm,
    hL.stk_pw (by omega), hr.ks.sub_left (Offset.sub_base _ (by omega)),
    hL.stk_in (by omega) hr.ow, hL.stk_in (by omega) sw, Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_pw (d := 0) (n := 24) (by omega),
    hr.ks.sub_left (by simpa using Offset.sub_base L.B (d := 0) (n := 24) (k := 88) (by omega)),
    by simpa using hL.stk_in (d := 0) (n := 24) (by omega) hr.ow,
    by simpa using hL.stk_in (d := 0) (n := 24) (by omega) sw,
    Offset.base_disjoint _ (by omega) (by omega), hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : VG.Proof.Scrypt.X86_64.Whole.PbkRegions L salt sl out ol) :
    ∀ r ∈ VG.Proof.Scrypt.X86_64.Whole.pbkRd L salt sl ++ VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86_64.Whole.Within r R := by
  have hnB := hL.nB
  have hs := hr.sw
  simp only [VG.Proof.Scrypt.X86_64.Whole.pbkRd, VG.Proof.Scrypt.X86_64.Whole.pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, VG.Proof.Scrypt.X86_64.Whole.within_base _ (by omega)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · exact ⟨L.FR, by simp, VG.Proof.Scrypt.X86_64.Whole.within_fr _ (by omega) (by omega)⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen17; omega)⟩

theorem pbk_wsub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : VG.Proof.Scrypt.X86_64.Whole.PbkRegions L salt sl out ol) : ∀ r ∈ VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol, VG.Proof.Scrypt.X86_64.Whole.InBuf L r := by
  simp only [VG.Proof.Scrypt.X86_64.Whole.pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hr.ow
  · exact hL.scr_in

theorem pbk_call (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
    (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String) (hL : L.Ok) {t : State}
    (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : VG.Proof.Scrypt.X86_64.Whole.PbkArgs L salt sl out ol t) (hr : VG.Proof.Scrypt.X86_64.Whole.PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.scr, 200 * 8⟩, ⟨L.B, 32⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  have hnB := hL.nB
  refine VG.Proof.Scrypt.X86_64.Whole.call_ok hL (VG.Proof.Scrypt.X86_64.Whole.pbk_correct hv) hsp hd hc (VG.Proof.Scrypt.X86_64.Whole.pbk_pre' hL hc ha hr) (VG.Proof.Scrypt.X86_64.Whole.pbk_sub hL hr) (VG.Proof.Scrypt.X86_64.Whole.pbk_wsub hL hr)
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  · have h := hpost
    simp only [VG.Proof.Scrypt.X86_64.Whole.pbkK, pbkG, Spec.Hmac.sha256S, State.withRegions_mem, hm, VG.Proof.Scrypt.X86_64.Whole.pbk_e0 hL hc ha,
      VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
      VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp),
      VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), ha.rdi, ha.rsi,
      ha.rdx, ha.rcx, ha.r8, ha.r9, RegUpd.setWidth_setWidth_32] at h
    have e₁ : Spec.Sha256.bytesAt t.callEntry.mem L.pw L.pwl.toNat = bytesAt t.mem L.pw L.pwl.toNat :=
      VG.Proof.Scrypt.X86_64.Whole.ce_bytesAt t (by rw [hc.ret]; exact hL.stk_pw (by omega)) (by have := hL.np; omega)
    have e₂ : Spec.Sha256.bytesAt t.callEntry.mem salt sl.toNat = bytesAt t.mem salt sl.toNat :=
      VG.Proof.Scrypt.X86_64.Whole.ce_bytesAt t (by rw [hc.ret]; exact hr.ks.sub_left (Offset.sub_base _ (by omega)))
        (by have := hr.ns; omega)
    rw [e₁, e₂] at h
    exact h

end

/-! ## ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (i : Nat) : List Region :=
  [⟨VG.Proof.Scrypt.X86_64.Whole.blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, (L.r.toNat + 2) * 128⟩]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) : 128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : VG.Proof.Scrypt.X86_64.Whole.InBuf L ⟨VG.Proof.Scrypt.X86_64.Whole.blkAt L i, L.r.toNat * 128⟩ :=
  .inl (VG.Proof.Scrypt.X86_64.Whole.within_off _ (VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi))

theorem r2 (hL : L.Ok) : (L.r + (2 : BitVec 32).signExtend 64).toNat = L.r.toNat + 2 := by
  have := hL.r57
  rw [show (2 : BitVec 32).signExtend 64 = BitVec.ofNat 64 2 from by decide,
    toNat_add_ofNat _ (by omega)]

theorem sub16 (B : Addr) : B + BitVec.ofNat 64 24 - 16 = B + BitVec.ofNat 64 8 := by bv_omega

theorem romix_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.X86_64.Whole.RomixArgs L (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) t) :
    Proof.Scrypt.roMixX86_64.pre (t.callEntry.withRegions [] (VG.Proof.Scrypt.X86_64.Whole.romixWr L i)) := by
  have hnB := hL.nB
  have hb := VG.Proof.Scrypt.X86_64.Whole.blk_in hL hi
  have hv : VG.Proof.Scrypt.X86_64.Whole.InBuf L ⟨L.v, L.vlen.toNat * 128⟩ := .inr (.inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _)))
  have hs : VG.Proof.Scrypt.X86_64.Whole.InBuf L ⟨L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen; omega))))
  have tb : (VG.Proof.Scrypt.X86_64.Whole.blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi; have := hL.nb; have := hL.rpos
    exact toNat_add_ofNat _ (by omega)
  simp only [Proof.Scrypt.roMixX86_64, State.withRegions_rd, State.withRegions_wr, hc.ce_rsp, VG.Proof.Scrypt.X86_64.Whole.sub16,
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), ha.rdi, ha.rsi,
    ha.rdx, ha.rcx, ha.r8, ha.r9, VG.Proof.Scrypt.X86_64.Whole.r2 hL]
  have kb := Within.sub (VG.Proof.Scrypt.X86_64.Whole.within_off L.b (VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi))
  have ks := Within.sub (VG.Proof.Scrypt.X86_64.Whole.within_base L.scr (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  refine ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    hL.stk_in (by omega) hb, hL.stk_in (by omega) hv, hL.stk_in (by omega) hs, hL.stk_in (by omega) hb,
    hL.stk_in (by omega) hv, hL.stk_in (by omega) hs,
    by rw [tb]; have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi; have := hL.nb; omega, hL.nv,
    by have := hL.nc; have := hL.slen; omega, hL.rpos, hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem roMix_nosp : NoSp Impl.Scrypt.X86_64.roMix := by
  have : ((instrs Impl.Scrypt.X86_64.roMix).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem roMix_depth : Impl.Scrypt.X86_64.roMix.depth ≤ 3 := by lit_decide

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ ([] : List Region) ++ VG.Proof.Scrypt.X86_64.Whole.romixWr L i, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86_64.Whole.Within r R := by
  simp only [VG.Proof.Scrypt.X86_64.Whole.romixWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.BB, by simp, VG.Proof.Scrypt.X86_64.Whole.within_off _ (VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen; omega)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ VG.Proof.Scrypt.X86_64.Whole.romixWr L i, VG.Proof.Scrypt.X86_64.Whole.InBuf L r := by
  simp only [VG.Proof.Scrypt.X86_64.Whole.romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.Proof.Scrypt.X86_64.Whole.blk_in hL hi
  · exact .inr (.inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen; omega))))

theorem romix_call (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : VG.Proof.Scrypt.X86_64.Whole.RomixArgs L (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      Frame (VG.Proof.Scrypt.X86_64.Whole.romixWr L i ++ [⟨L.B, 32⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) (128 * L.r.toNat)) := by
  have hb := VG.Proof.Scrypt.X86_64.Whole.blk_in hL hi
  refine VG.Proof.Scrypt.X86_64.Whole.call_ok hL RoMix.roMix_correct VG.Proof.Scrypt.X86_64.Whole.roMix_nosp VG.Proof.Scrypt.X86_64.Whole.roMix_depth hc (VG.Proof.Scrypt.X86_64.Whole.romix_pre hL hc hi ha)
    (VG.Proof.Scrypt.X86_64.Whole.romix_sub hL hi) (VG.Proof.Scrypt.X86_64.Whole.romix_wsub hL hi) fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', hf, ?_⟩
  · have h := hpost
    simp only [Proof.Scrypt.roMixX86_64, State.withRegions_mem, hm,
      VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp),
      VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), ha.rdi, ha.rsi, ha.rcx] at h
    rw [VG.Proof.Scrypt.X86_64.Whole.ce_bytesAt t (by rw [hc.ret]; exact hL.stk_in (by omega) (by simpa [Nat.mul_comm] using hb))
      (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi; omega)] at h
    exact h

end

end VG.Proof.Scrypt.X86_64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Verified`. -/
section

section

/-!
# scrypt on x86-64: correctness

Step 1 leaves the blocks `X k` of `PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in
`b` (`step1_ok`); the loop replaces them by their scryptROMix one at a time
(`Inv`, `loop_ok`); step 3 derives the key from them (`step3_ok`). `scrypt_ok`
puts the frame around it, for any implementation `pbk` of PBKDF2 verified
against its shared contract.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

variable {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) (hL : L.Ok)
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
def X (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
    (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : VG.Proof.Scrypt.X86_64.Whole.Step1 L m₀ (bytesAt m L.b (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : VG.Proof.Scrypt.X86_64.Whole.X L m₀ k = bytesAt m (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
      (L.pp * 128 * L.r.toNat) = some (bytesAt m L.b (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  rw [VG.Proof.Scrypt.X86_64.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.Whole.blkAt L k, 128 * L.r.toNat⟩ ⟨VG.Proof.Scrypt.X86_64.Whole.blkAt L i, L.r.toNat * 128⟩ := by
  have h₁ := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hk
  have h₂ := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi
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
    Region.Sub ⟨VG.Proof.Scrypt.X86_64.Whole.blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hk
  exact Offset.sub_base _ (by omega)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr, 200 * 8⟩ L.SC :=
  Within.sub (VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen17; omega))

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

omit hv hsp hd in
theorem pbk1_regions (hL : L.Ok) :
    VG.Proof.Scrypt.X86_64.Whole.PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [toNat_ofNat_lt hb]; exact .inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _))
  · rw [toNat_ofNat_lt hb]; exact hL.sb
  · exact hL.sc.sub_right (VG.Proof.Scrypt.X86_64.Whole.scr_sub hL)
  · rw [toNat_ofNat_lt hb]
    exact hL.bc.sub_right (VG.Proof.Scrypt.X86_64.Whole.scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.nb
  · rw [toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t)
    (ha : VG.Proof.Scrypt.X86_64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      VG.Proof.Scrypt.X86_64.Whole.Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.X86_64.Whole.X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk_call hv hsp hd name hL hc ha (VG.Proof.Scrypt.X86_64.Whole.pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (VG.Proof.Scrypt.X86_64.Whole.X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) (he : VG.Proof.Scrypt.X86_64.Whole.Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      VG.Proof.Scrypt.X86_64.Whole.Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.X86_64.Whole.X L m₀ k :=
  WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk1Args_ok hL hc he) fun _ ⟨hc₁, ha₁, _⟩ => VG.Proof.Scrypt.X86_64.Whole.pbk1_call_ok hv hsp hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = VG.Proof.Scrypt.X86_64.Whole.blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86_64.Whole.X L m₀ k) else VG.Proof.Scrypt.X86_64.Whole.X L m₀ k

abbrev Inv (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (g : Reg → BitVec 64) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t ∧ VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = VG.Proof.Scrypt.X86_64.Whole.blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86_64.Whole.X L m₀ k) else VG.Proof.Scrypt.X86_64.Whole.X L m₀ k

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : VG.Proof.Scrypt.X86_64.Whole.Lay) : VG.Proof.Scrypt.X86_64.Whole.blkAt L 0 = L.b := by
  simp only [VG.Proof.Scrypt.X86_64.Whole.blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-- A block of `b` misses the frame's first three words. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.Whole.blkAt L k, 128 * L.r.toNat⟩ ⟨L.B + BitVec.ofNat 64 32, 24⟩ :=
  (hL.kb.symm.sub_left (VG.Proof.Scrypt.X86_64.Whole.blk_sub hL hk)).sub_right (Offset.sub_base _ (by omega))

theorem start_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.X86_64.Whole.X L m₀ k) :
    WP isa (.block cur0) t (VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀ 0) :=
  WP.mono (VG.Proof.Scrypt.X86_64.Whole.cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', hb.trans (VG.Proof.Scrypt.X86_64.Whole.blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Scrypt.X86_64.Whole.blk_fr hL hk)
      (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hk; omega)⟩

theorem next_eq (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (i : Nat) :
    VG.Proof.Scrypt.X86_64.Whole.blkAt L i + BitVec.ofNat 64 (L.r.toNat * 128) = VG.Proof.Scrypt.X86_64.Whole.blkAt L (i + 1) := by
  simp only [VG.Proof.Scrypt.X86_64.Whole.blkAt]
  rw [VG.Proof.Scrypt.X86_64.Whole.add_add, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem zf_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (VG.Proof.Scrypt.X86_64.Whole.blkAt L (i + 1) - (BitVec.ofNat 64 (L.blen.toNat * 128) + L.b) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  rw [BitVec.add_comm (BitVec.ofNat 64 _) L.b]
  simp only [VG.Proof.Scrypt.X86_64.Whole.blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 64 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [Offset.ofNat_sub_ofNat_beq e₁ e₂]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t)
    (hb : VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ i t) (ha : VG.Proof.Scrypt.X86_64.Whole.RomixArgs L (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧ VG.Proof.Scrypt.X86_64.Whole.Mid L m₀ i t' := by
  refine WP.mono (VG.Proof.Scrypt.X86_64.Whole.romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [VG.Proof.Scrypt.X86_64.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega) (VG.Proof.Scrypt.X86_64.Whole.blk_in hL hi)
    · exact hL.stk_in (by omega) (.inr (.inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega) (.inr (.inr (.inl (VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen; omega)))))
    · exact Offset.disjoint_base _ (by omega) (by have := hL.nB; omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [VG.Proof.Scrypt.X86_64.Whole.romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact VG.Proof.Scrypt.X86_64.Whole.blk_disj hL hk hi hki
          · exact hL.bv.sub_left (VG.Proof.Scrypt.X86_64.Whole.blk_sub hL hk)
          · exact (hL.bc.sub_left (VG.Proof.Scrypt.X86_64.Whole.blk_sub hL hk)).sub_right
              (Within.sub (VG.Proof.Scrypt.X86_64.Whole.within_base _ (by have := hL.slen; omega)))
          · exact (hL.kb.symm.sub_left (VG.Proof.Scrypt.X86_64.Whole.blk_sub hL hk)).sub_right (Region.sub_prefix (by omega)))
          (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hk; omega)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega
        simp only [hlt, this, ite_false]

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t)
    (hm : VG.Proof.Scrypt.X86_64.Whole.Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧ VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ (i + 1) t' ∧
      t'.zf = some (decide (i + 1 = L.pp)) :=
  WP.mono (VG.Proof.Scrypt.X86_64.Whole.nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hz₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, VG.Proof.Scrypt.X86_64.Whole.next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Scrypt.X86_64.Whole.blk_fr hL hk)
        (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hk; omega)⟩,
      by rw [hz₃, VG.Proof.Scrypt.X86_64.Whole.next_eq, VG.Proof.Scrypt.X86_64.Whole.zf_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix)
      (.block nextBlock))) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀ (i + 1) t' ∧ t'.zf = some (decide (i + 1 = L.pp)) :=
  WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.Whole.romixArgs_ok hL h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.Whole.call_step hL hi hc₁ ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁) fun t₂ ⟨hc₂, hm₂⟩ =>
      WP.mono (VG.Proof.Scrypt.X86_64.Whole.next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀ 0 t) : WP isa romixLoop t (VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀) (fun _ hi _ h => VG.Proof.Scrypt.X86_64.Whole.body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

omit hv hsp hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀ L.pp t) :
    bytesAt t.mem L.b (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86_64.Whole.X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hsp hd in
theorem pbk2_regions (hL : L.Ok) :
    VG.Proof.Scrypt.X86_64.Whole.PbkRegions L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (VG.Proof.Scrypt.X86_64.Whole.scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_ofNat_lt hb]; exact VG.Proof.Scrypt.X86_64.Whole.within_base _ (Nat.le_refl _)
  · rw [toNat_ofNat_lt hb]; exact hL.bo
  · rw [toNat_ofNat_lt hb]; exact hL.bc.sub_right (VG.Proof.Scrypt.X86_64.Whole.scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.kb
  · rw [toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : VG.Proof.Scrypt.X86_64.Whole.Inv L g m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (VG.Proof.Scrypt.X86_64.Whole.X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk2Args_ok hL h.1) fun t₁ ⟨hc₁, ha₁, hf₁⟩ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk_call hv hsp hd name hL hc₁ ha₁ (VG.Proof.Scrypt.X86_64.Whole.pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  · have e : bytesAt t₁.mem L.b (L.blen.toNat * 128) = bytesAt t.mem L.b (L.blen.toNat * 128) :=
      Memory.frame_bytesAt hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.kb.symm.sub_right (Offset.sub_base _ (by omega)))
        (by omega)
    rw [toNat_ofNat_lt hb, hc₁.pw_bytes hL, e, VG.Proof.Scrypt.X86_64.Whole.final_bytes' hL h] at hp
    exact hp

/-- The frame's body. -/
theorem body_scrypt_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) (he : VG.Proof.Scrypt.X86_64.Whole.Entry L t) :
    WP isa (scryptBody name pbk) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.Whole.step1_ok hv hsp hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.Whole.start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.Whole.loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86_64.Whole.step3_ok hv hsp hd name hL h₃) fun t₄ ⟨hc₄, hp⟩ => ⟨hc₄, ?_⟩
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem L.b (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [VG.Proof.Scrypt.X86_64.Whole.X_of hL h1 hk, Whole.chunk_bytesAt _ _ (VG.Proof.Scrypt.X86_64.Whole.blk_le' hL hk)]

end

/-! ## The whole function -/

theorem push_entry (s : State) : VG.Proof.Scrypt.X86_64.Whole.Entry (VG.Proof.Scrypt.X86_64.Whole.lay s) (pushed VG.Proof.Scrypt.X86_64.Whole.pushRs s) :=
  ⟨pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide),
    pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide)⟩

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * 7) = B + BitVec.ofNat 64 88 := by
  rw [VG.Proof.Scrypt.X86_64.Whole.add_add]

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)


section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

/-- `vg_scrypt` meets `scryptX86_64` and the calling convention but for MXCSR. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptX86_64.pre s) :
    WP isa (scrypt name pbk) s fun s' => gprPreserved s s' ∧ Proof.Scrypt.scryptX86_64.post s s' := by
  have hL := VG.Proof.Scrypt.X86_64.Whole.lay_ok h
  have hc := VG.Proof.Scrypt.X86_64.Whole.push_ctx h
  have he := VG.Proof.Scrypt.X86_64.Whole.push_entry s
  refine WP.frame (rs := VG.Proof.Scrypt.X86_64.Whole.pushRs) (by decide) (by decide) (by decide)
    (by show 8 * 7 ≤ _; have := h.1; omega)
    (WP.mono (VG.Proof.Scrypt.X86_64.Whole.body_scrypt_ok hv hsp hd name hL hc he) fun u ⟨hu, ho⟩ =>
      ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 7 from rfl, VG.Proof.Scrypt.X86_64.Whole.pop_rsp, VG.Proof.Scrypt.X86_64.Whole.lay_ret]
    refine ⟨fun r hr => ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (VG.Proof.Scrypt.X86_64.Whole.ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      have hnB := hL.nB
      refine hu.frame.readW (r := (VG.Proof.Scrypt.X86_64.Whole.lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, VG.Proof.Scrypt.X86_64.Whole.lay_ret]; exact Region.contains_self _ _
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl | rfl | rfl)
        exacts [hL.rb, hL.rv, hL.rc, hL.ro, Offset.disjoint_base _ (by omega) (by omega)]
  · simp only [Proof.Scrypt.scryptX86_64, popped_mem]
    exact ho

/-- `vg_scrypt` meets `scryptX86_64` and the calling convention, if no
instruction (of it or the functions it calls) loads MXCSR. -/
theorem scrypt_correct (hmx : (scrypt name pbk).allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (h : Proof.Scrypt.scryptX86_64.pre s) :
    ∃ t s', Exec isa (scrypt name pbk) s t s' ∧ abiPreserved s s' ∧ Proof.Scrypt.scryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.Scrypt.X86_64.Whole.scrypt_ok hv hsp hd name h
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩

end

end VG.Proof.Scrypt.X86_64.Whole

end

section

/-!
# scrypt on x86-64: constant time, up to the indices `j`

Two runs whose public data agree have the same layout, so between the frame's
push and pop they are related by `Two`: both satisfy `Ctx` with that layout
(and `Φ`, what the next piece needs), whatever their secrets, and the indices
of all the scryptROMix calls agree (`LeakEq`, from the contract's leakage).
The blocks address only the stack, from `rsp` (the taint analysis); each call
is of constant-time code whose public data agree (`RelCT.callEx`): for PBKDF2
its pointers and lengths, for scryptROMix also the indices of its block, which
`LeakEq` gives (`leak_X`); the loop's branch agrees since both runs count the
same blocks.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {m₁ m₂ : Mem} (h : VG.Proof.Scrypt.X86_64.Whole.LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.X86_64.Whole.X L m₁ k) = roMixIndices L.r.toNat L.NN (VG.Proof.Scrypt.X86_64.Whole.X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  simp only [VG.Proof.Scrypt.X86_64.Whole.X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env := VG.Proof.Scrypt.X86_64.Whole.Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : VG.Proof.Scrypt.X86_64.Whole.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : VG.Proof.Scrypt.X86_64.Whole.Env, e.1.Ok ∧ VG.Proof.Scrypt.X86_64.Whole.LeakEq e.1 e.2.2.2.1 e.2.2.2.2 ∧ VG.Proof.Scrypt.X86_64.Whole.Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    VG.Proof.Scrypt.X86_64.Whole.Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Scrypt.X86_64.Whole.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Scrypt.X86_64.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two Φ) c (VG.Proof.Scrypt.X86_64.Whole.Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem rsp_two {L : VG.Proof.Scrypt.X86_64.Whole.Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : VG.Proof.Scrypt.X86_64.Whole.Ctx L g₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.X86_64.Whole.Ctx L g₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

/-- A block whose addresses depend only on `rsp`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : VG.Proof.Scrypt.X86_64.Whole.Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : VG.Proof.Scrypt.X86_64.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two Φ) (.block is) (VG.Proof.Scrypt.X86_64.Whole.Two Ψ) :=
  VG.Proof.Scrypt.X86_64.Whole.two_wp (RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Scrypt.X86_64.Whole.rsp_two c₁ c₂) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : VG.Proof.Scrypt.X86_64.Whole.Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Scrypt.X86_64.Whole.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Scrypt.X86_64.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : VG.Proof.Scrypt.X86_64.Whole.Lay) t₁ t₂ g₁ g₂ m₁ m₂, L.Ok → VG.Proof.Scrypt.X86_64.Whole.LeakEq L m₁ m₂ → VG.Proof.Scrypt.X86_64.Whole.Ctx L g₁ m₁ t₁ → VG.Proof.Scrypt.X86_64.Whole.Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : VG.Proof.Scrypt.X86_64.Whole.Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, VG.Proof.Scrypt.X86_64.Whole.Within r R)
    (hwsub : ∀ (L : VG.Proof.Scrypt.X86_64.Whole.Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, VG.Proof.Scrypt.X86_64.Whole.InBuf L r)
    (hw : ∀ (L : VG.Proof.Scrypt.X86_64.Whole.Lay) g m₀ (t : State), L.Ok → VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two Φ) (.call n c) (VG.Proof.Scrypt.X86_64.Whole.Two Ψ) :=
  VG.Proof.Scrypt.X86_64.Whole.two_wp (RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, hk, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ hL c₁ f₁, hpre _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, (VG.Proof.Scrypt.X86_64.Whole.covers c₁ (hsub L _ _ hL f₁) (hwsub L _ _ hL f₁)).1,
      (VG.Proof.Scrypt.X86_64.Whole.covers c₁ (hsub L _ _ hL f₁) (hwsub L _ _ hL f₁)).2,
      (VG.Proof.Scrypt.X86_64.Whole.covers c₂ (hsub L _ _ hL f₂) (hwsub L _ _ hL f₂)).1,
      (VG.Proof.Scrypt.X86_64.Whole.covers c₂ (hsub L _ _ hL f₂) (hwsub L _ _ hL f₂)).2, VG.Proof.Scrypt.X86_64.Whole.rsp_two c₁ c₂⟩) hw

/-! ## The calls -/

theorem pbk_pub_two {L : VG.Proof.Scrypt.X86_64.Whole.Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (c₁ : VG.Proof.Scrypt.X86_64.Whole.Ctx L g₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.X86_64.Whole.Ctx L g₂ m₂ t₂) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (a₁ : VG.Proof.Scrypt.X86_64.Whole.PbkArgs L salt sl out ol t₁) (a₂ : VG.Proof.Scrypt.X86_64.Whole.PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (VG.Proof.Scrypt.X86_64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol))
      (t₂.callEntry.withRegions (VG.Proof.Scrypt.X86_64.Whole.pbkRd L salt sl) (VG.Proof.Scrypt.X86_64.Whole.pbkWr L out ol)) := by
  simp only [VG.Proof.Scrypt.X86_64.Whole.pbkK, Proof.Pbkdf2.Md.X86_64.pbkG, VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.r8, a₁.r9, a₂.rdi,
    a₂.rsi, a₂.rdx, a₂.rcx, a₂.r8, a₂.r9, VG.Proof.Scrypt.X86_64.Whole.pbk_e0 hL c₁ a₁, VG.Proof.Scrypt.X86_64.Whole.pbk_e0 hL c₂ a₂, VG.Proof.Scrypt.X86_64.Whole.pbk_e1 hL c₁ a₁,
    VG.Proof.Scrypt.X86_64.Whole.pbk_e1 hL c₂ a₂, c₁.ce_rsp, c₂.ce_rsp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : VG.Proof.Scrypt.X86_64.Whole.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Scrypt.X86_64.Whole.Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ i t) (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) (128 * L.r.toNat) = VG.Proof.Scrypt.X86_64.Whole.X L m₀ i := by
  rw [State.withRegions_mem, VG.Proof.Scrypt.X86_64.Whole.ce_bytesAt t (by
      rw [hc.ret]; exact hL.stk_in (by omega) (by simpa [Nat.mul_comm] using VG.Proof.Scrypt.X86_64.Whole.blk_in hL hi))
    (by have := hL.blen_lt; have := VG.Proof.Scrypt.X86_64.Whole.blk_le hL hi; omega), hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : VG.Proof.Scrypt.X86_64.Whole.Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (hk : VG.Proof.Scrypt.X86_64.Whole.LeakEq L m₁ m₂) (c₁ : VG.Proof.Scrypt.X86_64.Whole.Ctx L g₁ m₁ t₁) (c₂ : VG.Proof.Scrypt.X86_64.Whole.Ctx L g₂ m₂ t₂) {i : Nat} (hi : i < L.pp)
    (b₁ : VG.Proof.Scrypt.X86_64.Whole.InvB L m₁ i t₁) (b₂ : VG.Proof.Scrypt.X86_64.Whole.InvB L m₂ i t₂) (a₁ : VG.Proof.Scrypt.X86_64.Whole.RomixArgs L (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) t₁)
    (a₂ : VG.Proof.Scrypt.X86_64.Whole.RomixArgs L (VG.Proof.Scrypt.X86_64.Whole.blkAt L i) t₂) :
    Proof.Scrypt.roMixX86_64.pub (t₁.callEntry.withRegions [] (VG.Proof.Scrypt.X86_64.Whole.romixWr L i))
      (t₂.callEntry.withRegions [] (VG.Proof.Scrypt.X86_64.Whole.romixWr L i)) := by
  simp only [Proof.Scrypt.roMixX86_64, VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    VG.Proof.Scrypt.X86_64.Whole.gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.r8, a₁.r9, a₂.rdi,
    a₂.rsi, a₂.rdx, a₂.rcx, a₂.r8, a₂.r9, c₁.ce_rsp, c₂.ce_rsp, true_and,
    VG.Proof.Scrypt.X86_64.Whole.romix_bytes hL c₁ hi b₁, VG.Proof.Scrypt.X86_64.Whole.romix_bytes hL c₂ hi b₂]
  exact VG.Proof.Scrypt.X86_64.Whole.leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : VG.Proof.Scrypt.X86_64.Whole.Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two (VG.Proof.Scrypt.X86_64.Whole.LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.X86_64.roMix) (.block nextBlock)))
      (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two (VG.Proof.Scrypt.X86_64.Whole.LoopAt n)) (.block romixArgs) (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ (L.pp - n) t ∧ VG.Proof.Scrypt.X86_64.Whole.RomixArgs L (VG.Proof.Scrypt.X86_64.Whole.blkAt L (L.pp - n)) t) :=
    VG.Proof.Scrypt.X86_64.Whole.two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨h0, hn, hb⟩ =>
      WP.mono (VG.Proof.Scrypt.X86_64.Whole.romixArgs_ok hL hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ (L.pp - n) t ∧
      VG.Proof.Scrypt.X86_64.Whole.RomixArgs L (VG.Proof.Scrypt.X86_64.Whole.blkAt L (L.pp - n)) t) (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix)
      (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86_64.Whole.Mid L m₀ (L.pp - n) t) :=
    VG.Proof.Scrypt.X86_64.Whole.two_call RoMix.roMix_correct RoMix.roMix_ct (fun _ => []) (fun L => VG.Proof.Scrypt.X86_64.Whole.romixWr L (L.pp - n))
      (fun _ _ _ _ hL hc ⟨h0, hn, _, ha⟩ => VG.Proof.Scrypt.X86_64.Whole.romix_pre hL hc (by omega) ha)
      (fun _ _ _ _ _ _ _ hL hk c₁ c₂ ⟨h0, hn, b₁, a₁⟩ ⟨_, _, b₂, a₂⟩ =>
        VG.Proof.Scrypt.X86_64.Whole.romix_pub_two hL hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ hL ⟨h0, hn, _⟩ => VG.Proof.Scrypt.X86_64.Whole.romix_sub hL (by omega))
      (fun _ _ _ hL ⟨h0, hn, _⟩ => VG.Proof.Scrypt.X86_64.Whole.romix_wsub hL (by omega))
      (fun _ _ _ _ hL hc ⟨h0, hn, hb, ha⟩ =>
        WP.mono (VG.Proof.Scrypt.X86_64.Whole.call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86_64.Whole.Mid L m₀ (L.pp - n) t) (.block nextBlock)
      (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) :=
    VG.Proof.Scrypt.X86_64.Whole.two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      WP.mono (VG.Proof.Scrypt.X86_64.Whole.next_step hL (by omega) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', h0, hn, hb, hz⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ 0 t) romixLoop (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ L.pp t)
    (fun n => VG.Proof.Scrypt.X86_64.Whole.Two (VG.Proof.Scrypt.X86_64.Whole.LoopAt n)) (fun n => (VG.Proof.Scrypt.X86_64.Whole.body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨h0, hn, b₁, z₁⟩, ⟨-, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.1.pp - n + 1 = e.1.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show VG.Proof.Scrypt.X86_64.Whole.InvB e.1 _ e.1.pp a from hl ▸ b₁,
          show VG.Proof.Scrypt.X86_64.Whole.InvB e.1 _ e.1.pp b from hl ▸ b₂⟩
      · have hl : e.1.pp - n + 1 ≠ e.1.pp := by simpa using ht
        have e₁ : e.1.pp - (n - 1) = e.1.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, c₁, c₂, ⟨by omega, by omega, e₁ ▸ b₁⟩,
          ⟨by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, b₁, b₂⟩ => ⟨e.1.pp, e, hL, hk, c₁, c₂,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

theorem scryptBody_ct : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L _ t => VG.Proof.Scrypt.X86_64.Whole.Entry L t) (scryptBody name pbk) fun _ _ => True := by
  have p1a : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L _ t => VG.Proof.Scrypt.X86_64.Whole.Entry L t) (.block pbk1Args)
      (VG.Proof.Scrypt.X86_64.Whole.Two fun L _ t => VG.Proof.Scrypt.X86_64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    VG.Proof.Scrypt.X86_64.Whole.two_blk (by taint_decide) fun _ _ _ _ hL hc he =>
      WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk1Args_ok hL hc he) fun _ ⟨hc', ha, _⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L _ t => VG.Proof.Scrypt.X86_64.Whole.PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.X86_64.Whole.X L m₀ k) :=
    VG.Proof.Scrypt.X86_64.Whole.two_call (VG.Proof.Scrypt.X86_64.Whole.pbk_correct hv) (VG.Proof.Scrypt.X86_64.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.X86_64.Whole.pbkRd L L.salt L.sl)
      (fun L => VG.Proof.Scrypt.X86_64.Whole.pbkWr L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ hL hc ha => VG.Proof.Scrypt.X86_64.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.X86_64.Whole.pbk1_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => VG.Proof.Scrypt.X86_64.Whole.pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => VG.Proof.Scrypt.X86_64.Whole.pbk_sub hL (VG.Proof.Scrypt.X86_64.Whole.pbk1_regions hL)) (fun _ _ _ hL _ => VG.Proof.Scrypt.X86_64.Whole.pbk_wsub hL (VG.Proof.Scrypt.X86_64.Whole.pbk1_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk1_call_ok hv hsp hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (VG.Proof.Scrypt.X86_64.Whole.blkAt L k) (128 * L.r.toNat) = VG.Proof.Scrypt.X86_64.Whole.X L m₀ k)
      (.block cur0) (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ 0 t) :=
    VG.Proof.Scrypt.X86_64.Whole.two_blk (by taint_decide) fun _ _ _ _ hL hc hx => VG.Proof.Scrypt.X86_64.Whole.start_ok hL hc hx
  have p2a : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L m₀ t => VG.Proof.Scrypt.X86_64.Whole.InvB L m₀ L.pp t) (.block pbk2Args)
      (VG.Proof.Scrypt.X86_64.Whole.Two fun L _ t => VG.Proof.Scrypt.X86_64.Whole.PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    VG.Proof.Scrypt.X86_64.Whole.two_blk (by taint_decide) fun _ _ _ _ hL hc _ =>
      WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk2Args_ok hL hc) fun _ ⟨hc', ha, _⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (VG.Proof.Scrypt.X86_64.Whole.Two fun L _ t => VG.Proof.Scrypt.X86_64.Whole.PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (VG.Proof.Scrypt.X86_64.Whole.Two fun _ _ _ => True) :=
    VG.Proof.Scrypt.X86_64.Whole.two_call (VG.Proof.Scrypt.X86_64.Whole.pbk_correct hv) (VG.Proof.Scrypt.X86_64.Whole.pbk_ct hv) (fun L => VG.Proof.Scrypt.X86_64.Whole.pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => VG.Proof.Scrypt.X86_64.Whole.pbkWr L L.out L.ol)
      (fun _ _ _ _ hL hc ha => VG.Proof.Scrypt.X86_64.Whole.pbk_pre' hL hc ha (VG.Proof.Scrypt.X86_64.Whole.pbk2_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => VG.Proof.Scrypt.X86_64.Whole.pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => VG.Proof.Scrypt.X86_64.Whole.pbk_sub hL (VG.Proof.Scrypt.X86_64.Whole.pbk2_regions hL)) (fun _ _ _ hL _ => VG.Proof.Scrypt.X86_64.Whole.pbk_wsub hL (VG.Proof.Scrypt.X86_64.Whole.pbk2_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (VG.Proof.Scrypt.X86_64.Whole.pbk_call hv hsp hd name hL hc ha (VG.Proof.Scrypt.X86_64.Whole.pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  exact ((p1a.seq p1c).seq (c0.seq (loop_ct.seq (p2a.seq p2c)))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptX86_64.pre Proof.Scrypt.scryptX86_64.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (RelCT.mono (VG.Proof.Scrypt.X86_64.Whole.scryptBody_ct hv hsp hd name) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, hsp', hlk⟩, rfl, rfl⟩
  have e : VG.Proof.Scrypt.X86_64.Whole.lay s₂ = VG.Proof.Scrypt.X86_64.Whole.lay s₁ := by
    simp only [VG.Proof.Scrypt.X86_64.Whole.lay, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, hsp']
  refine ⟨⟨VG.Proof.Scrypt.X86_64.Whole.lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, VG.Proof.Scrypt.X86_64.Whole.lay_ok h₁, ?_, VG.Proof.Scrypt.X86_64.Whole.push_ctx h₁, e ▸ VG.Proof.Scrypt.X86_64.Whole.push_ctx h₂,
    VG.Proof.Scrypt.X86_64.Whole.push_entry s₁, e ▸ VG.Proof.Scrypt.X86_64.Whole.push_entry s₂⟩
  rw [← hdi, ← hsi, ← hdx, ← hcx, ← h8, ← a0, ← a2] at hlk
  exact hlk

end

end VG.Proof.Scrypt.X86_64.Whole

end

/-!
# scrypt on x86-64: the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract, is verified against `Spec.Scrypt.scryptContract` for the
88 bytes of stack its frame and calls use (`scrypt_verified_of`); for the
PBKDF2 made with an implementation `c` of SHA-256's compression function
(`scrypt_verified`), whose code never writes `rsp` but by the frame
(`scrypt_spSafe`).
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (core core_pbkdf2 nosp_of)

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
bytes at `0x90008`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rdx => 0x20000 | .r8 => 1 | .r9 => 0x30000 | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x90008 then 1 else if a = 0x90012 then 4 else if a = 0x90018 then 2
    else if a = 0x90022 then 5 else if a = 0x90028 then 17 else if a = 0x90032 then 6
    else if a = 0x90038 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 56⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptX86_64.Implies (Spec.Scrypt.scryptContract X86_64.abi 88) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64, X86_64.abi,
          X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64, X86_64.abi,
          X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
        sig_split h
        rename_i hrsp hlk h1 h2 h3 h4 h5 h6 a0 a1 a2 a3 a4 a5
        exact ⟨h1, h2, h3, h4, h5, h6, a0, a1, a2, a3, a4, a5, h, hrsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, X86_64.abi, X86_64.argRegs,
          _root_.List.range, _root_.List.range.loop, List.append_eq, VG.Proof.Scrypt.X86_64.Whole.satState] [satState] using VG.Proof.Scrypt.X86_64.Whole.satState }

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`, if
no instruction of it (or of the functions it calls) loads MXCSR. -/
theorem scrypt_verified_of (hmx : (scrypt name pbk).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (scrypt name pbk) (Spec.Scrypt.scryptContract X86_64.abi 88) :=
  Verified.of_correct (VG.Proof.Scrypt.X86_64.Whole.scrypt_correct hv hsp hd name hmx) (VG.Proof.Scrypt.X86_64.Whole.scrypt_ct hv hsp hd name) VG.Proof.Scrypt.X86_64.Whole.scrypt_implies

end

/-! ## With PBKDF2 made with an implementation of SHA-256's compression function -/

open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- How deeply calls nest in `pbkdf2`, from its own code. -/
theorem core_pbkdf2_depth {H : Hash} (hc : H.compC.depth = 0) (hi : H.initC.depth = 0)
    (h : (core H).pbkdf2.depth ≤ 3) : H.pbkdf2.depth ≤ 3 := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream, Hash.initKeys,
    Impl.Pbkdf2.Md.X86_64.Stream.callInit, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.depth, hc, hi] at h ⊢
  exact h

variable (c : Proof.Sha256.X86_64.Compress)

/-- PBKDF2-HMAC-SHA256 made with `c`. -/
abbrev pbkOf : Prog isa := (Proof.Pbkdf2.Md.X86_64.Sha256.hash c).pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2ScratchApi.name ++ c.suffix

theorem pbk_verified :
    Verified X86_64.target (VG.Proof.Scrypt.X86_64.Whole.pbkOf c) (Spec.Hmac.sha256I.pbkdf2ScratchContract X86_64.abi 24) :=
  (Proof.Pbkdf2.Md.X86_64.Sha256.variant c).pbkdf2

theorem pbk_nosp : NoSp (VG.Proof.Scrypt.X86_64.Whole.pbkOf c) :=
  nosp_of (core_pbkdf2 (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cNs
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iNs
    (by decide +kernel : Proof.Pbkdf2.Md.X86_64.Sha256.coreH.pbkdf2.allInstrs
      (fun i => !Taint.clobbers i .rsp) = true))

theorem pbk_depth : (VG.Proof.Scrypt.X86_64.Whole.pbkOf c).depth ≤ 3 :=
  VG.Proof.Scrypt.X86_64.Whole.core_pbkdf2_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cD
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iD
    (by decide +kernel : Proof.Pbkdf2.Md.X86_64.Sha256.coreH.pbkdf2.depth ≤ 3)

theorem pbk_mx : (VG.Proof.Scrypt.X86_64.Whole.pbkOf c).allInstrs (fun i => !loadsMxcsr i) = true :=
  core_pbkdf2 (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cMx (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iMx
    Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.pbkMx

theorem scrypt_mx : (scrypt (VG.Proof.Scrypt.X86_64.Whole.pbkName c) (VG.Proof.Scrypt.X86_64.Whole.pbkOf c)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hr : Impl.Scrypt.X86_64.roMix.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide
  simp only [scrypt, scryptBody, pbkCall, romixLoop, Code.allInstrs, VG.Proof.Scrypt.X86_64.Whole.pbk_mx c, hr, Bool.and_true,
    Bool.true_and]
  decide

/-- `vg_scrypt` made with `c`. -/
theorem scrypt_verified :
    Verified X86_64.target (scrypt (VG.Proof.Scrypt.X86_64.Whole.pbkName c) (VG.Proof.Scrypt.X86_64.Whole.pbkOf c)) (Spec.Scrypt.scryptContract X86_64.abi 88) :=
  VG.Proof.Scrypt.X86_64.Whole.scrypt_verified_of (VG.Proof.Scrypt.X86_64.Whole.pbk_verified c) (VG.Proof.Scrypt.X86_64.Whole.pbk_nosp c) (VG.Proof.Scrypt.X86_64.Whole.pbk_depth c) (VG.Proof.Scrypt.X86_64.Whole.pbkName c) (VG.Proof.Scrypt.X86_64.Whole.scrypt_mx c)

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem scrypt_spSafe : (scrypt (VG.Proof.Scrypt.X86_64.Whole.pbkName c) (VG.Proof.Scrypt.X86_64.Whole.pbkOf c)).all (fun i => !isa.writesSp i) = true := by
  have hp : (VG.Proof.Scrypt.X86_64.Whole.pbkOf c).all (fun i => !isa.writesSp i) = true :=
    (Proof.Pbkdf2.Md.X86_64.Sha256.variant c).pbkdf2Sp
  have hr : Impl.Scrypt.X86_64.roMix.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  simp only [scrypt, scryptBody, pbkCall, romixLoop, Code.all, hp, hr, Bool.and_true, Bool.true_and]
  decide

end VG.Proof.Scrypt.X86_64.Whole

end
