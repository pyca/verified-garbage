import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Poly1305.Arm.Init
import VerifiedGarbage.Proof.Poly1305.Arm.Finalize
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Stages`. -/
section

section

/-!
# ChaCha20-Poly1305 on ARMv7: the entry state, regions and invariant
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.Arm in
/-- The precondition of both functions, `(key = r0, nonce = r1, aad = r2,
aad_len = r3, data = [sp], len = [sp + 4], tag = [sp + 8], work = [sp + 12])`:
`work` (632 bytes) and `data` may be read and written, `key`, `nonce`, `aad`
and the stack arguments read, and `tag` written if `enc` (`seal`) and read if
not (`open`); the written ones overlap nothing else; `work`, `data`, `aad`
and `tag` do not overlap the 8 bytes below the stack pointer; nothing wraps
around the end of the address space. -/
def preArm (enc : Bool) (s : Arm.State) : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), 32⟩
  let nonce : Region := ⟨State.addr (s.gpr .r1), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  let tag : Region := ⟨State.addr (stackArg s 2), 16⟩
  let work : Region := ⟨State.addr (stackArg s 3), 632⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  let below : Region := ⟨State.addr s.sp - 8, 8⟩
  s.rd = (if enc then [key, nonce, aad, args] else [key, nonce, aad, tag, args]) ∧
  s.wr = (if enc then [data, tag, work] else [data, work]) ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧ work.Disjoint args ∧
  data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧ data.Disjoint args ∧
  (if enc then tag.Disjoint args else True) ∧
  below.Disjoint work ∧ below.Disjoint aad ∧ below.Disjoint data ∧ below.Disjoint tag ∧
  (stackArg s 3).toNat + 632 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
  (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 16 ≤ 2 ^ 32 ∧
  (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 12 ≤ 2 ^ 32 ∧
  8 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32

open VG.Arm in
def pubArm (s₁ s₂ : Arm.State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
  s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
  stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3

open VG.Arm in
/-- `vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, data, len, tag, work)`. -/
def sealArm : Contract Arm.isa where
  pre := VG.Proof.ChaCha20Poly1305.preArm true
  post s s' :=
    encrypt (bytesAt s.mem (State.addr (s.gpr .r0)) 32) (bytesAt s.mem (State.addr (s.gpr .r1)) 12)
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat) =
      (bytesAt s'.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat,
        bytesAt s'.mem (State.addr (stackArg s 2)) 16)
  pub := VG.Proof.ChaCha20Poly1305.pubArm

open VG.Arm in
/-- `vg_chacha20_poly1305_open(key, nonce, aad, aad_len, data, len, tag, work) -> u32`. -/
def openArm : Contract Arm.isa where
  pre := VG.Proof.ChaCha20Poly1305.preArm false
  post s s' :=
    match decrypt (bytesAt s.mem (State.addr (s.gpr .r0)) 32) (bytesAt s.mem (State.addr (s.gpr .r1)) 12)
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
        (bytesAt s.mem (State.addr (stackArg s 2)) 16) with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat = pt
    | none => s'.gpr .r0 = 0
  pub := VG.Proof.ChaCha20Poly1305.pubArm

end VG.Proof.ChaCha20Poly1305

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `p + d`, as a 64-bit address. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-! ## The entry state -/

section
variable (s₀ : State)
/-- The context (the working space), the key, the nonce, the additional
data, the data and the tag, as 32-bit pointers. -/
abbrev cP : BitVec 32 := stackArg s₀ 3
abbrev kP : BitVec 32 := s₀.gpr .r0
abbrev nP : BitVec 32 := s₀.gpr .r1
abbrev aP : BitVec 32 := s₀.gpr .r2
abbrev dP : BitVec 32 := stackArg s₀ 0
abbrev tP : BitVec 32 := stackArg s₀ 2
abbrev cx : Addr := State.addr (VG.Proof.ChaCha20Poly1305.Arm.cP s₀)
abbrev kp : Addr := State.addr (VG.Proof.ChaCha20Poly1305.Arm.kP s₀)
abbrev np : Addr := State.addr (VG.Proof.ChaCha20Poly1305.Arm.nP s₀)
abbrev ad : Addr := State.addr (VG.Proof.ChaCha20Poly1305.Arm.aP s₀)
abbrev dp : Addr := State.addr (VG.Proof.ChaCha20Poly1305.Arm.dP s₀)
abbrev tp : Addr := State.addr (VG.Proof.ChaCha20Poly1305.Arm.tP s₀)
abbrev AL : Nat := (s₀.gpr .r3).toNat
abbrev L : Nat := (stackArg s₀ 1).toNat
/-- The key, the nonce, the additional data, the data and the tag on entry. -/
abbrev K : List Byte := bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.np s₀) 12
abbrev A : List Byte := bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.ad s₀) (VG.Proof.ChaCha20Poly1305.Arm.AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 16
/-- The one-time Poly1305 key. -/
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (VG.Proof.ChaCha20Poly1305.Arm.K s₀) (VG.Proof.ChaCha20Poly1305.Arm.N s₀)
abbrev ctxR : Region := ⟨VG.Proof.ChaCha20Poly1305.Arm.cx s₀, 632⟩
abbrev kR : Region := ⟨VG.Proof.ChaCha20Poly1305.Arm.kp s₀, 32⟩
abbrev nR : Region := ⟨VG.Proof.ChaCha20Poly1305.Arm.np s₀, 12⟩
abbrev aR : Region := ⟨VG.Proof.ChaCha20Poly1305.Arm.ad s₀, VG.Proof.ChaCha20Poly1305.Arm.AL s₀⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20Poly1305.Arm.dp s₀, VG.Proof.ChaCha20Poly1305.Arm.L s₀⟩
abbrev tR : Region := ⟨VG.Proof.ChaCha20Poly1305.Arm.tp s₀, 16⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
/-- The 8 bytes below the stack pointer, which the frame pushes. -/
abbrev belR : Region := ⟨State.addr s₀.sp - 8, 8⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) k, n⟩
/-- `ctx + k`, as the code computes it. -/
abbrev ptr (k : Nat) : BitVec 32 := VG.Proof.ChaCha20Poly1305.Arm.cP s₀ + BitVec.ofNat 32 k
end

/-- What the proof uses of the precondition; `enc` for `seal`. -/
structure APre (enc : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = if enc then [VG.Proof.ChaCha20Poly1305.Arm.kR s₀, VG.Proof.ChaCha20Poly1305.Arm.nR s₀, VG.Proof.ChaCha20Poly1305.Arm.aR s₀, VG.Proof.ChaCha20Poly1305.Arm.argR s₀] else [VG.Proof.ChaCha20Poly1305.Arm.kR s₀, VG.Proof.ChaCha20Poly1305.Arm.nR s₀, VG.Proof.ChaCha20Poly1305.Arm.aR s₀, VG.Proof.ChaCha20Poly1305.Arm.tR s₀, VG.Proof.ChaCha20Poly1305.Arm.argR s₀]
  wr : s₀.wr = if enc then [VG.Proof.ChaCha20Poly1305.Arm.dR s₀, VG.Proof.ChaCha20Poly1305.Arm.tR s₀, VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] else [VG.Proof.ChaCha20Poly1305.Arm.dR s₀, VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀]
  c_k : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.kR s₀)
  c_n : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.nR s₀)
  c_a : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.aR s₀)
  c_d : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.dR s₀)
  c_t : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.tR s₀)
  c_arg : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.argR s₀)
  d_k : (VG.Proof.ChaCha20Poly1305.Arm.dR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.kR s₀)
  d_n : (VG.Proof.ChaCha20Poly1305.Arm.dR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.nR s₀)
  d_a : (VG.Proof.ChaCha20Poly1305.Arm.dR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.aR s₀)
  d_t : (VG.Proof.ChaCha20Poly1305.Arm.dR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.tR s₀)
  d_arg : (VG.Proof.ChaCha20Poly1305.Arm.dR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.argR s₀)
  t_arg : if enc then (VG.Proof.ChaCha20Poly1305.Arm.tR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.argR s₀) else True
  b_c : (VG.Proof.ChaCha20Poly1305.Arm.belR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀)
  b_a : (VG.Proof.ChaCha20Poly1305.Arm.belR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.aR s₀)
  b_d : (VG.Proof.ChaCha20Poly1305.Arm.belR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.dR s₀)
  b_t : (VG.Proof.ChaCha20Poly1305.Arm.belR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.tR s₀)
  fit_c : (VG.Proof.ChaCha20Poly1305.Arm.cP s₀).toNat + 632 ≤ 2 ^ 32
  fit_a : (VG.Proof.ChaCha20Poly1305.Arm.aP s₀).toNat + VG.Proof.ChaCha20Poly1305.Arm.AL s₀ ≤ 2 ^ 32
  fit_d : (VG.Proof.ChaCha20Poly1305.Arm.dP s₀).toNat + VG.Proof.ChaCha20Poly1305.Arm.L s₀ ≤ 2 ^ 32
  fit_t : (VG.Proof.ChaCha20Poly1305.Arm.tP s₀).toNat + 16 ≤ 2 ^ 32
  fit_k : (VG.Proof.ChaCha20Poly1305.Arm.kP s₀).toNat + 32 ≤ 2 ^ 32
  fit_n : (VG.Proof.ChaCha20Poly1305.Arm.nP s₀).toNat + 12 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  spfit : s₀.sp.toNat + 16 ≤ 2 ^ 32

theorem APre.of {enc : Bool} (s₀ : State) (h : VG.Proof.ChaCha20Poly1305.preArm enc s₀) : VG.Proof.ChaCha20Poly1305.Arm.APre enc s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

variable {e : Bool}

theorem APre.a_d {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : (VG.Proof.ChaCha20Poly1305.Arm.aR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.dR s₀) := hp.d_a.symm

theorem APre.ctx_wr {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀ ∈ s₀.wr := by
  rw [hp.wr]; cases e <;> simp

theorem APre.d_wr {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∈ s₀.wr := by
  rw [hp.wr]; cases e <;> simp

theorem APre.a_rd {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.aR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.k_rd {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.kR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.n_rd {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.nR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.arg_rd {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.argR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.t_wr {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre true s₀) : VG.Proof.ChaCha20Poly1305.Arm.tR s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem APre.t_rd {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre false s₀) : VG.Proof.ChaCha20Poly1305.Arm.tR s₀ ∈ s₀.rd := by
  rw [hp.rd]; simp

theorem toNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem addr_toNat (p : BitVec 32) : (State.addr p).toNat = p.toNat :=
  VG.Proof.ChaCha20.Arm.Xor.addr_toNat p

/-! ## Regions -/

theorem sub_off (p : Addr) {a n len : Nat} (h : a + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := Offset.sub_base p h

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 632) : Region.Sub (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀) :=
  VG.Proof.ChaCha20Poly1305.Arm.sub_off _ h

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 632)
    (hb : b + m ≤ 632) : (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ a n).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ b m) := Offset.disjoint (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) h (by lit_omega) (by lit_omega)

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (_h₃ : a + m ≤ 632) :
    Region.Sub (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ a m) := Offset.sub (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) h₁ h₂

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 632) :
    (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n).Contains (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) w := Offset.contains (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) h₁ h₂ (by lit_omega)

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 632) : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Contains (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) w :=
  Offset.contains_base (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) h (by lit_omega)

theorem off_off (p : Addr) (a b : Nat) : VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.off p a) b = VG.Proof.ChaCha20Poly1305.Arm.off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_add (p : Addr) (a b : Nat) : VG.Proof.ChaCha20Poly1305.Arm.off p a + BitVec.ofNat 64 b = VG.Proof.ChaCha20Poly1305.Arm.off p (a + b) :=
  VG.Proof.ChaCha20Poly1305.Arm.off_off p a b

theorem off_zero (p : Addr) : VG.Proof.ChaCha20Poly1305.Arm.off p 0 = p := by simp

namespace APre
variable {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀)
include hp

theorem in_ctx {a w : Nat} (h : a + w ≤ 632) : InRegions s₀.wr (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) w :=
  ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, hp.ctx_wr, VG.Proof.ChaCha20Poly1305.Arm.contains_ctx s₀ h⟩

theorem in_ctx' {a w : Nat} (h : a + w ≤ 632) : InRegions (s₀.rd ++ s₀.wr) (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) w :=
  ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by simp [hp.ctx_wr], VG.Proof.ChaCha20Poly1305.Arm.contains_ctx s₀ h⟩

/-- `ctx + k`, computed in 32 bits, is `cx + k`. -/
theorem addr_ptr {k : Nat} (h : k < 632) : State.addr (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ k) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) k :=
  addr_add (by have := hp.fit_c; omega)

theorem addr_cP_off {d : Nat} (h : d < 632) :
    State.addr (VG.Proof.ChaCha20Poly1305.Arm.cP s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) d :=
  hp.addr_ptr h

theorem ptr_toNat {k : Nat} (h : k < 632) : (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ k).toNat = (VG.Proof.ChaCha20Poly1305.Arm.cP s₀).toNat + k := by
  have := hp.fit_c
  rw [BitVec.toNat_add, VG.Proof.ChaCha20Poly1305.Arm.toNat32 (by lit_omega), Nat.mod_eq_of_lt (by lit_omega)]

end APre

/-- The stack arguments are above the 8 bytes the frame pushes. -/
theorem bel_arg (s₀ : State) : (VG.Proof.ChaCha20Poly1305.Arm.belR s₀).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.argR s₀) := by
  have e : stackArgAddr s₀ 0 = (State.addr s₀.sp - 8) + BitVec.ofNat 64 8 := by
    rw [show stackArgAddr s₀ 0 = State.addr s₀.sp by simp [stackArgAddr]]
    exact (BitVec.sub_add_cancel _ _).symm
  have h := Offset.disjoint (State.addr s₀.sp - 8) (d := 0) (n := 8) (e := 8) (k := 16) (by omega)
    (by omega) (by omega)
  rw [show (State.addr s₀.sp - 8) + BitVec.ofNat 64 0 = State.addr s₀.sp - 8 from BitVec.add_zero _] at h
  show Region.Disjoint ⟨State.addr s₀.sp - 8, 8⟩ ⟨stackArgAddr s₀ 0, 16⟩
  rw [e]; exact h

/-! ## Covering the callees' regions -/

theorem covers_sub {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k r.len ∧ k + r.len ≤ 632) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by rw [hwr]; exact hp.ctx_wr, k, by rw [hrk], hk⟩

/-- A callee's working space (at `ctx + a`, `n` bytes) and argument (at
`ctx + b`, `m` bytes) in the context. -/
theorem covers2 {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (hwr : s.wr = s₀.wr) {a n b m : Nat}
    (ha : a + n ≤ 632) (hb : b + m ≤ 632) :
    Covers ([VG.Proof.ChaCha20Poly1305.Arm.sub s₀ b m] ++ [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ a n]) (s.rd ++ s.wr) :=
  Covers.right (VG.Proof.ChaCha20Poly1305.Arm.covers_sub hp hwr _ fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨b, rfl, hb⟩
    · exact ⟨a, rfl, ha⟩)

theorem covers1 {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (hwr : s.wr = s₀.wr) {a n : Nat} (ha : a + n ≤ 632) :
    Covers [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ a n] s.wr :=
  VG.Proof.ChaCha20Poly1305.Arm.covers_sub hp hwr _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨a, rfl, ha⟩

/-! ## What a part keeps -/

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `lr`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.ChaCha20Poly1305.Arm.Kept rs s₁ s₂) (h₂ : VG.Proof.ChaCha20Poly1305.Arm.Kept rs s₂ s₃) :
    VG.Proof.ChaCha20Poly1305.Arm.Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : VG.Proof.ChaCha20Poly1305.Arm.Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem Kept.mem_eq {s s' : State} (hk : VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s') : s'.mem = s.mem :=
  funext fun x => hk.frame x fun _ h => absurd h List.not_mem_nil

/-- A block that writes no callee-saved register keeps them, and the stack
pointer. -/
theorem WP.kept {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : (is.all fun i => preserved.all fun r => dstOf i != some r) = true) :
    WP isa (.block is) s fun s' => Q s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl rfl), Exec.sp he⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

/-- Kept, from a block's facts. -/
theorem Kept.of {rs : List Region} {s s' : State} (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    VG.Proof.ChaCha20Poly1305.Arm.Kept rs s s' :=
  ⟨fun r hr _ => hg r hr, hsp, hrd, hwr, hf⟩

/-! ## The saved registers and the invariant -/

/-- Our caller's `r4`–`r11` and our return address, saved in `ctx[464, 500)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) p.2) 32 = s₀.gpr p.1

theorem saved_bound : ∀ p ∈ saved, savOff ≤ p.2 ∧ p.2 + 4 ≤ savOff + 36 := by decide

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20Poly1305.Arm.Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ savOff 36).Disjoint r) : VG.Proof.ChaCha20Poly1305.Arm.Saved s₀ m' := by
  intro p hp
  have hb := VG.Proof.ChaCha20Poly1305.Arm.saved_bound p hp
  rw [hf.readW (VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (w := 32 / 8) hb.1 hb.2 (by simp [savOff])) hd (by decide), h p hp]

/-- The values we keep in `r7`–`r11`. -/
structure Regs (s₀ s : State) : Prop where
  r7 : s.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀
  r8 : s.gpr .r8 = VG.Proof.ChaCha20Poly1305.Arm.aP s₀
  r9 : s.gpr .r9 = s₀.gpr .r3
  r10 : s.gpr .r10 = VG.Proof.ChaCha20Poly1305.Arm.dP s₀
  r11 : s.gpr .r11 = stackArg s₀ 1

theorem Regs.kept {s₀ s s' : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Regs s₀ s) (hk : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) :
    VG.Proof.ChaCha20Poly1305.Arm.Regs s₀ s' :=
  ⟨by rw [hk _ (by decide) (by decide), h.r7], by rw [hk _ (by decide) (by decide), h.r8],
    by rw [hk _ (by decide) (by decide), h.r9], by rw [hk _ (by decide) (by decide), h.r10],
    by rw [hk _ (by decide) (by decide), h.r11]⟩

/-- What holds between the parts of the code: the registers, the stack
pointer and the regions, the saved registers, and the memory changed only
in the context, the data and the stack below the stack pointer. -/
structure Inv (s₀ : State) (s : State) : Prop where
  regs : VG.Proof.ChaCha20Poly1305.Arm.Regs s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : VG.Proof.ChaCha20Poly1305.Arm.Saved s₀ s.mem
  frame : Frame [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, VG.Proof.ChaCha20Poly1305.Arm.dR s₀, VG.Proof.ChaCha20Poly1305.Arm.belR s₀] s₀.mem s.mem

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the context outside the saved registers, and the data. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) (hk : VG.Proof.ChaCha20Poly1305.Arm.Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, VG.Proof.ChaCha20Poly1305.Arm.dR s₀, VG.Proof.ChaCha20Poly1305.Arm.belR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ savOff 36).Disjoint r) : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' where
  regs := h.regs.kept hk.cs
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- A part that writes `ctx[k, k + n)` keeps the invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {k n : Nat} (hk : VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n] s s')
    (h₂ : k + n ≤ 632) (h₃ : k + n ≤ savOff ∨ savOff + 36 ≤ k) : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by simp, VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ h₂⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp only [savOff] at h₃ ⊢; omega) (by simp [savOff]) h₂)

/-- A part that writes no memory keeps the invariant. -/
theorem Inv.step0 {s₀ s s' : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) (hk : VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s') : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

end VG.Proof.ChaCha20Poly1305.Arm

end

/-!
# ChaCha20-Poly1305 on ARMv7: the calls

Each call of a verified function, from its proof of `Verified` (with
`WP.call`): what it needs of the state it is called from, and what holds when
it returns. A call (`bl`) stores nothing in memory, so the callee changes
memory only within the regions it may write; the frame around
`vg_poly1305_finalize_scratch` also stores its stack arguments below the stack
pointer.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm
open VG.Spec.Poly1305 (Repr Buffered bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-! ## Memory -/

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_off P (a := 24) (by lit_omega)))
      (by lit_omega)]
    exact h2
  · rw [VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by lit_omega)))
      (by lit_omega)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p :=
  VG.Proof.ChaCha20.Arm.Xor.stateAt_frame hf hd

/-! ## Registers the callees keep -/

theorem keeps {c : Prog isa} {r : Reg} (h : ((instrs c).all fun i => dstOf i != some r) = true) :
    ∀ i ∈ instrs c, dstOf i ≠ some r := by
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem init_keeps_r0 : ∀ i ∈ instrs Impl.Poly1305.Arm.init, dstOf i ≠ some .r0 :=
  VG.Proof.ChaCha20Poly1305.Arm.keeps (by rw [← Code.allInstrs_eq]; lit_decide)

theorem blocks_keeps_r0 : ∀ i ∈ instrs Impl.Poly1305.Arm.blocks, dstOf i ≠ some .r0 :=
  VG.Proof.ChaCha20Poly1305.Arm.keeps (by rw [← Code.allInstrs_eq]; lit_decide)

theorem init_noCalls : Impl.Poly1305.Arm.init.noCalls = true := by lit_decide
theorem blocks_noCalls : Impl.Poly1305.Arm.blocks.noCalls = true := by lit_decide
theorem finalize_noCalls : Impl.Poly1305.Arm.finalize.noCalls = true := by lit_decide
theorem block_noCalls : Impl.ChaCha20.Arm.block.noCalls = true := by lit_decide
theorem xor_noFrames : Impl.ChaCha20.Arm.Xor.xor.noFrames = true := by lit_decide

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : BitVec 32} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = B)
    (hdj : (⟨State.addr B, 256⟩ : Region).Disjoint ⟨State.addr S, 64⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hB : B.toNat + 256 ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr S, 64⟩] ++ [⟨State.addr B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20Poly1305.Arm.Kept [⟨State.addr B, 256⟩] s s' → s'.gpr .r1 = B →
      stateAt s'.mem (State.addr B) = Spec.ChaCha20.block (stateAt s.mem (State.addr S)) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockArm) Proof.ChaCha20.Arm.block_correct
    (rd := [⟨State.addr S, 64⟩]) (wr := [⟨State.addr B, 256⟩]) ?_ hc hw ?_ VG.Proof.ChaCha20Poly1305.Arm.block_noCalls
  · simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1]
    exact ⟨trivial, trivial, hdj, hS, hB⟩
  · intro s' hrd hwr hsp hf hcs hkeep hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩
      (by rw [hkeep .r1 Proof.ChaCha20.Arm.Xor.block_keeps_r1 (by decide), h1]) ?_
    simpa only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1] using hpost

/-! ## `vg_chacha20_xor` -/

/-- `vg_chacha20_xor`'s contract, with what its proof shows of `r0` and `r1`
on return. -/
def xorK : Contract isa :=
  { Proof.ChaCha20.xorArm with
    post := fun s s' => Proof.ChaCha20.xorArm.post s s' ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r3 }

theorem xor_call {s : State} {S D B : BitVec 32} {n : Nat} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = D)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (h3 : s.gpr .r3 = B) (hn : n < 2 ^ 32)
    (hSD : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hSB : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hDB : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32) (hB : B.toNat + 320 ≤ 2 ^ 32)
    (hc : Covers ([] ++ [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20Poly1305.Arm.Kept [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s s' → s'.gpr .r1 = B →
      Spec.ChaCha20.bytesAt s'.mem (State.addr D) n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (State.addr D) n)
          (keystream (stateAt s.mem (State.addr S)) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.callCalls (k := VG.Proof.ChaCha20Poly1305.Arm.xorK) (fun s hs => Proof.ChaCha20.Arm.Xor.xor_regs s hs)
    (rd := []) (wr := [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) ?_ hc hw ?_
    VG.Proof.ChaCha20Poly1305.Arm.xor_noFrames
  · simp only [VG.Proof.ChaCha20Poly1305.Arm.xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hS, hD, hB⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [VG.Proof.ChaCha20Poly1305.Arm.xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, hn'] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost.2.2 hpost.1

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : BitVec 32} (h0 : s.gpr .r0 = P) (h1 : s.gpr .r1 = K)
    (hdj : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr K, 32⟩)
    (hP : P.toNat + 128 ≤ 2 ^ 32) (hK : K.toNat + 32 ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr K, 32⟩] ++ [⟨State.addr P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20Poly1305.Arm.Kept [⟨State.addr P, 128⟩] s s' → s'.gpr .r0 = P →
      Repr s'.mem (State.addr P) (bytesAt s.mem (State.addr K) 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.Arm.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initArm) Proof.Poly1305.Arm.init_ok
    (rd := [⟨State.addr K, 32⟩]) (wr := [⟨State.addr P, 128⟩]) ?_ hc hw ?_ VG.Proof.ChaCha20Poly1305.Arm.init_noCalls
  · simp only [Proof.Poly1305.initArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1]
    exact ⟨trivial, trivial, hdj, hP, hK⟩
  · intro s' hrd hwr hsp hf hcs hkeep hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ (by rw [hkeep .r0 VG.Proof.ChaCha20Poly1305.Arm.init_keeps_r0 (by decide), h0]) ?_
    simpa only [Proof.Poly1305.initArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1] using hpost

/-! ## `vg_poly1305_blocks` -/

theorem blocks_call {s : State} {P p : BitVec 32} {n : Nat} (h0 : s.gpr .r0 = P) (h1 : s.gpr .r1 = p)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (hn : 16 * n < 2 ^ 32)
    (hdj : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr p, 16 * n⟩)
    (hP : P.toNat + 128 ≤ 2 ^ 32) (hp : p.toNat + 16 * n ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr p, 16 * n⟩] ++ [⟨State.addr P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20Poly1305.Arm.Kept [⟨State.addr P, 128⟩] s s' → s'.gpr .r0 = P →
      (∀ key msg, Repr s.mem (State.addr P) key msg →
        Repr s'.mem (State.addr P) key (msg ++ bytesAt s.mem (State.addr p) (16 * n))) → Q s') :
    WP isa (.call "vg_poly1305_blocks" Impl.Poly1305.Arm.blocks) s Q := by
  have hn' : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by lit_omega)
  refine WP.call (k := Proof.Poly1305.blocksArm) Proof.Poly1305.Arm.blocks_ok
    (rd := [⟨State.addr p, 16 * n⟩]) (wr := [⟨State.addr P, 128⟩]) ?_ hc hw ?_ VG.Proof.ChaCha20Poly1305.Arm.blocks_noCalls
  · simp only [Proof.Poly1305.blocksArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      h0, h1, h2, hn']
    exact ⟨trivial, trivial, hdj, hP, hp⟩
  · intro s' hrd hwr hsp hf hcs hkeep hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ (by rw [hkeep .r0 VG.Proof.ChaCha20Poly1305.Arm.blocks_keeps_r0 (by decide), h0])
      fun key msg hr => ?_
    simp only [Proof.Poly1305.blocksArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      h0, h1, h2, hn'] at hpost
    exact hpost key msg hr

/-! ## `vg_poly1305_finalize_scratch`, in its frame -/

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by lit_omega), Nat.mod_eq_of_lt (a := k) (by lit_omega),
    Nat.mod_eq_of_lt (a := a.toNat) (by lit_omega)]
  omega

/-- The 8 bytes below `sp`, as the frame's push computes them. -/
theorem addr_below {sp : BitVec 32} (h : 8 ≤ sp.toNat) :
    State.addr (sp - BitVec.ofNat 32 (4 * [Reg.r1, Reg.r12].length)) = State.addr sp - 8 :=
  VG.Proof.ChaCha20Poly1305.Arm.addr_sub h

/-- What the frame around `vg_poly1305_finalize_scratch` needs of the state it is
entered in: the state at `P`, `out` at `O` and `scratch` at `Sc` in `r0`,
`r1` and `r12`, disjoint, writable, and disjoint from the 8 bytes of stack the
frame pushes. -/
structure FinArgs (s : State) (P O Sc : BitVec 32) : Prop where
  h0 : s.gpr .r0 = P
  h1 : s.gpr .r1 = O
  h12 : s.gpr .r12 = Sc
  hsp : 8 ≤ s.sp.toNat
  hPO : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  hPS : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr Sc, 128⟩
  hOS : (⟨State.addr O, 16⟩ : Region).Disjoint ⟨State.addr Sc, 128⟩
  hbP : (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint ⟨State.addr P, 128⟩
  hbO : (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  hbS : (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint ⟨State.addr Sc, 128⟩
  hP : P.toNat + 128 ≤ 2 ^ 32
  hO : O.toNat + 16 ≤ 2 ^ 32
  hS : Sc.toNat + 128 ≤ 2 ^ 32
  hw : Covers [⟨State.addr P, 128⟩, ⟨State.addr O, 16⟩, ⟨State.addr Sc, 128⟩] s.wr

/-- The regions `vg_poly1305_finalize_scratch` is called with. -/
abbrev finRd (s : State) : List Region := [⟨State.addr s.sp - 8, 8⟩]
abbrev finWr (P O Sc : BitVec 32) : List Region := [⟨State.addr P, 128⟩, ⟨State.addr O, 16⟩, ⟨State.addr Sc, 128⟩]

/-- The state `vg_poly1305_finalize_scratch` runs from, with the permissions it is
given. -/
abbrev finView (s : State) (P O Sc : BitVec 32) : State :=
  (pushed [.r1, .r12] s).callEntry.withRegions (VG.Proof.ChaCha20Poly1305.Arm.finRd s) (VG.Proof.ChaCha20Poly1305.Arm.finWr P O Sc)

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r1, Reg.r12].length) = 8 := rfl

theorem fin_asp (s : State) : (pushed [.r1, .r12] s).sp = s.sp - 8 := by rw [pushed_sp, VG.Proof.ChaCha20Poly1305.Arm.e8]

theorem fin_nsp (s : State) (P O Sc : BitVec 32) : (VG.Proof.ChaCha20Poly1305.Arm.finView s P O Sc).sp = s.sp - 8 := VG.Proof.ChaCha20Poly1305.Arm.fin_asp s


theorem fin_ng (s : State) (P O Sc : BitVec 32) (r : Reg) (hr : r ∉ linkRegs) :
    (VG.Proof.ChaCha20Poly1305.Arm.finView s P O Sc).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

namespace FinArgs
variable {s : State} {P O Sc : BitVec 32} (h : VG.Proof.ChaCha20Poly1305.Arm.FinArgs s P O Sc)
include h

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := by
  have := VG.Proof.ChaCha20Poly1305.Arm.addr_below h.hsp; rwa [VG.Proof.ChaCha20Poly1305.Arm.e8] at this

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h.hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [h.hspA]; omega), h.hA]; rfl

theorem amem : (pushed [.r1, .r12] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) O).writeW (State.addr s.sp - 8 + 4) Sc := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r1, Reg.r12].length)) [s.gpr .r1, s.gpr .r12] = _
  rw [VG.Proof.ChaCha20Poly1305.Arm.e8, VG.Proof.ChaCha20Poly1305.Arm.storeWords_two, h.hA, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl, h.hA4,
    h.h1, h.h12]

theorem sa0 (t : State) (ht : t.sp = s.sp - 8) : stackArgAddr t 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr; rw [ht, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from BitVec.add_zero _, h.hA]

theorem arg0 (t : State) (ht : t.sp = s.sp - 8) (hm : t.mem = (pushed [.r1, .r12] s).mem) : stackArg t 0 = O := by
  have := h.hsp
  rw [stackArg, h.sa0 t ht, hm, h.amem, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 (t : State) (ht : t.sp = s.sp - 8) (hm : t.mem = (pushed [.r1, .r12] s).mem) : stackArg t 1 = Sc := by
  rw [stackArg, show stackArgAddr t 1 = State.addr s.sp - 8 + 4 by unfold stackArgAddr; rw [ht]; exact h.hA4, hm,
    h.amem, Mem.readW_writeW_self32]

theorem fA : Frame [⟨State.addr s.sp - 8, 8⟩] s.mem (pushed [.r1, .r12] s).mem := by
  rw [h.amem]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

theorem pre : Proof.Poly1305.finalizeArm.pre (VG.Proof.ChaCha20Poly1305.Arm.finView s P O Sc) := by
  simp only [Proof.Poly1305.finalizeArm, h.arg0 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp s P O Sc) rfl, h.arg1 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp s P O Sc) rfl, h.sa0 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp s P O Sc),
    VG.Proof.ChaCha20Poly1305.Arm.fin_ng s P O Sc .r0 (by decide), h.h0, State.withRegions_rd, State.withRegions_wr]
  refine ⟨trivial, trivial, h.hPO, h.hPS, h.hOS, h.hbP, h.hbO, h.hbS, h.hP, h.hO, h.hS, ?_⟩
  rw [VG.Proof.ChaCha20Poly1305.Arm.fin_nsp s P O Sc, h.hspA]; omega

/-- The stack arguments are the frame. -/
theorem cov : Covers (VG.Proof.ChaCha20Poly1305.Arm.finRd s ++ VG.Proof.ChaCha20Poly1305.Arm.finWr P O Sc) ((pushed [.r1, .r12] s).rd ++ (pushed [.r1, .r12] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rwa [VG.Proof.ChaCha20Poly1305.Arm.e8, h.hA]
  · obtain ⟨r', hr', hc'⟩ := h.hw x n' ⟨r, hr, hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (VG.Proof.ChaCha20Poly1305.Arm.finWr P O Sc) (pushed [.r1, .r12] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.hw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end FinArgs

theorem finalize_ok {s : State} {P O Sc : BitVec 32} (h : VG.Proof.ChaCha20Poly1305.Arm.FinArgs s P O Sc) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.ChaCha20Poly1305.Arm.Kept [⟨State.addr P, 128⟩, ⟨State.addr O, 16⟩, ⟨State.addr Sc, 128⟩,
        ⟨State.addr s.sp - 8, 8⟩] s s' →
      (∀ key msg, Repr s.mem (State.addr P) key msg →
        Proof.Poly1305.countArm s = BitVec.ofNat 64 msg.length →
        bytesAt s'.mem (State.addr O) 16 = mac key msg) → Q s') :
    WP isa Impl.ChaCha20Poly1305.Arm.finalize s Q := by
  refine WP.frame (rs := [.r1, .r12]) (r := .r1) rfl (by simpa using h.hsp) (by decide) ?_
  have hbw : ∀ r ∈ [⟨State.addr s.sp - 8, 8⟩], (⟨State.addr P, 128⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.hbP.symm
  refine WP.call (k := Proof.Poly1305.finalizeArm) Proof.Poly1305.Arm.Fin.finalize_ok
    (rd := VG.Proof.ChaCha20Poly1305.Arm.finRd s) (wr := VG.Proof.ChaCha20Poly1305.Arm.finWr P O Sc) h.pre h.cov h.covW ?_ VG.Proof.ChaCha20Poly1305.Arm.finalize_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hcnt : Proof.Poly1305.countArm (VG.Proof.ChaCha20Poly1305.Arm.finView s P O Sc) = Proof.Poly1305.countArm s := by
    simp only [Proof.Poly1305.countArm, VG.Proof.ChaCha20Poly1305.Arm.fin_ng s P O Sc .r2 (by decide), VG.Proof.ChaCha20Poly1305.Arm.fin_ng s P O Sc .r3 (by decide)]
  simp only [Proof.Poly1305.finalizeArm, VG.Proof.ChaCha20Poly1305.Arm.fin_ng s P O Sc .r0 (by decide), h.h0, hcnt, h.arg0 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp s P O Sc) rfl,
    State.withRegions_mem] at hpost
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ fun key msg hr hc => ?_
  · have hr1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr1, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, VG.Proof.ChaCha20Poly1305.Arm.fin_asp s, VG.Proof.ChaCha20Poly1305.Arm.e8]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (h.fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]
    exact hpost key msg (Proof.Poly1305.Repr.buffered (Repr.frame h.fA hbw hr)) hc

end VG.Proof.ChaCha20Poly1305.Arm

section

/-!
# ChaCha20-Poly1305 on ARMv7: the prologue

Saving the registers, moving the arguments, copying words of the context, the
ChaCha20 state for counter 0, the one-time key and the Poly1305 state for it.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd saveMem saveList_ok save_sep readW_writeW_save wp_mov
  wp_add wp_ldr wp_str wp_ldrSp op2_imm op2_reg)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-! ## More instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## Saving the registers -/

theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (VG.Arm.Spill.saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 :=
  Spill.saveMem_saved (lo := 464) (hi := 500) B g m saved (by decide)

theorem saveMem_frame (s₀ : State) (m : Mem) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, savOff ≤ p.2 ∧ p.2 + 4 ≤ savOff + 36) →
      Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ savOff 36] m (VG.Arm.Spill.saveMem m (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (w := 32 / 8) h.1 h.2 (by simp [savOff]))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem saved_ne12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

/-! ## The stack arguments -/

/-- The `i`-th stack argument, of the 16 bytes of them. -/
theorem stackArgAddr_eq (s : State) {i : Nat} (hi : i < 4) (hsp : s.sp.toNat + 16 ≤ 2 ^ 32) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  unfold stackArgAddr
  rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _, addr_add (by omega)]

namespace APre
variable {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀)
include hp

theorem arg_contains {i : Nat} (hi : i < 4) : (VG.Proof.ChaCha20Poly1305.Arm.argR s₀).Contains (stackArgAddr s₀ i) 4 := by
  rw [VG.Proof.ChaCha20Poly1305.Arm.stackArgAddr_eq s₀ hi hp.spfit]; exact Offset.contains_base _ (by omega) (by omega)

theorem arg_in {i : Nat} (hi : i < 4) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s₀ i) 4 :=
  ⟨VG.Proof.ChaCha20Poly1305.Arm.argR s₀, by rw [hrd]; exact List.mem_append_left _ hp.arg_rd, hp.arg_contains hi⟩

/-- A stack argument, from memory that agrees with the entry's on them. -/
theorem arg_eq {m : Mem} (hm : ∀ a, (VG.Proof.ChaCha20Poly1305.Arm.argR s₀).Contains a 1 → m a = s₀.mem a) {i : Nat} (hi : i < 4) :
    m.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i :=
  Mem.readW_congr fun j hj => hm _ ((hp.arg_contains hi).byte (by
    rw [Mem.sub_ofNat_toNat _ (by omega)]; omega))

theorem addr_kP_off {d : Nat} (h : d < 32) : State.addr (VG.Proof.ChaCha20Poly1305.Arm.kP s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) d :=
  addr_add (by have := hp.fit_k; omega)

theorem addr_nP_off {d : Nat} (h : d < 12) : State.addr (VG.Proof.ChaCha20Poly1305.Arm.nP s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.np s₀) d :=
  addr_add (by have := hp.fit_n; omega)

theorem addr_tP_off {d : Nat} (h : d < 16) : State.addr (VG.Proof.ChaCha20Poly1305.Arm.tP s₀ + BitVec.ofNat 32 d) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) d :=
  addr_add (by have := hp.fit_t; omega)

theorem k_in {d : Nat} (h : d + 4 ≤ 32) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) d) 4 :=
  ⟨VG.Proof.ChaCha20Poly1305.Arm.kR s₀, by rw [hrd]; exact List.mem_append_left _ hp.k_rd, Offset.contains_base _ h (by omega)⟩

theorem n_in {d : Nat} (h : d + 4 ≤ 12) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.np s₀) d) 4 :=
  ⟨VG.Proof.ChaCha20Poly1305.Arm.nR s₀, by rw [hrd]; exact List.mem_append_left _ hp.n_rd, Offset.contains_base _ h (by omega)⟩

end APre

/-- `work`, the context, into `r12`. -/
theorem entry_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) → s.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ → s.mem = s₀.mem →
      s.rd = s₀.rd → s.wr = s₀.wr → s.sp = s₀.sp → WP isa (.block rest) s Q) :
    WP isa (.block (entry ++ rest)) s₀ Q :=
  wp_ldrSp (a := stackArgAddr s₀ 3) (by decide) rfl (hp.arg_in (by decide) rfl) fun s₁ u₁ =>
    k s₁ (fun r hr => u₁.other r hr) u₁.gpr u₁.mem u₁.rd u₁.wr u₁.sp

/-- The moves' results. -/
theorem moves_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (hg : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r)
    (h12 : s.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀) (hrd : s.rd = s₀.rd) (hsp : s.sp = s₀.sp)
    (hm : ∀ a, (VG.Proof.ChaCha20Poly1305.Arm.argR s₀).Contains a 1 → s.mem a = s₀.mem a) :
    WP isa (.block moves) s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Regs s₀ s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r := by
  unfold moves
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _)
    fun s₃ u₃ => ?_
  have hsp₃ : s₃.sp = s₀.sp := by rw [u₃.sp, u₂.sp, u₁.sp, hsp]
  have hrd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, hrd]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [hsp₃]; rfl) (hp.arg_in (by decide) hrd₃)
    fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₄.sp, hsp₃]; rfl)
    (hp.arg_in (by decide) (by rw [u₄.rd, hrd₃])) fun s₅ u₅ => ?_
  refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun r h7 h8 h9 h10 h11 => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, h12]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, hm₃]; exact hp.arg_eq hm (by decide)
  · rw [u₅.gpr, u₄.mem, hm₃]; exact hp.arg_eq hm (by decide)
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₅.other _ h11, u₄.other _ h10, u₃.other _ h9, u₂.other _ h8, u₁.other _ h7]

/-- Loading the context, saving the registers and moving the arguments. -/
theorem saveMoves_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, VG.Proof.ChaCha20Poly1305.Arm.Regs s₀ s → s.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.kP s₀ → s.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.nP s₀ → s.sp = s₀.sp → s.rd = s₀.rd →
      s.wr = s₀.wr → VG.Proof.ChaCha20Poly1305.Arm.Saved s₀ s.mem → Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ savOff 36] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (entry ++ save ++ moves ++ rest)) s₀ Q := by
  simp only [List.append_assoc]
  refine VG.Proof.ChaCha20Poly1305.Arm.entry_ok hp fun s₁ g₁ c₁ m₁ rd₁ wr₁ sp₁ => ?_
  rw [show save = saved.map (fun p => Instr.str p.1 .r12 p.2) from rfl]
  refine VG.Arm.Spill.saveList_ok saved s₁ Q (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := VG.Proof.ChaCha20Poly1305.Arm.saved_bound p hp'
    simp only [savOff] at hb
    have := hp.fit_c
    rw [c₁, wr₁]
    exact ⟨by omega, by omega, hp.in_ctx (by lit_omega)⟩
  have f₂ : Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ savOff 36] s₀.mem s₂.mem := by
    rw [m₂, c₁, m₁]; exact VG.Proof.ChaCha20Poly1305.Arm.saveMem_frame s₀ _ _ _ VG.Proof.ChaCha20Poly1305.Arm.saved_bound
  refine WP.block_append (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.moves_ok hp (s := s₂) (fun r hr => by rw [g₂, g₁ r hr]) (by rw [g₂, c₁])
    (by rw [rd₂, rd₁]) (by rw [sp₂, sp₁]) fun a ha => f₂ a fun r hr hc => ?_)
    fun s₃ ⟨rg₃, m₃, rd₃, wr₃, sp₃, o₃⟩ => ?_)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hp.c_arg.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [savOff]))) a hc ha
  refine k s₃ rg₃ ?_ ?_ (by rw [sp₃, sp₂, sp₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) ?_
    (by rw [m₃]; exact f₂)
  · rw [o₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂, g₁ _ (by decide)]
  · rw [o₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂, g₁ _ (by decide)]
  · intro p hp'
    rw [m₃, m₂, c₁]
    exact (VG.Proof.ChaCha20Poly1305.Arm.saveMem_saved _ _ _ p hp').trans (g₁ _ (VG.Proof.ChaCha20Poly1305.Arm.saved_ne12 p hp'))

/-! ## Copying words of the context -/

/-- The context may be read and written. -/
def CtxOk (s₀ s : State) : Prop :=
  ∀ a w, a + w ≤ 632 → InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) w ∧ InRegions s.wr (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) w

theorem Inv.ctxOk {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (h : s.rd = s₀.rd) (h' : s.wr = s₀.wr) : VG.Proof.ChaCha20Poly1305.Arm.CtxOk s₀ s :=
  fun _ _ hw => by rw [h, h']; exact ⟨hp.in_ctx' hw, hp.in_ctx hw⟩

theorem readW_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (VG.Proof.ChaCha20Poly1305.Arm.off p e) v).readW (VG.Proof.ChaCha20Poly1305.Arm.off p d) 32 = m.readW (VG.Proof.ChaCha20Poly1305.Arm.off p d) 32 :=
  readW_writeW_save m p v hd he h

/-- Bytes equal byte by byte. -/
theorem bytesAt_eq_of {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' q n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.getElem_map, List.getElem_range]
  exact h i (by simpa using h₁)

theorem copyWords_step (a b n : Nat) : copyWords a b (n + 1) =
    copyWords a b n ++ ([.ldr .r12 .r7 (a + 4 * n), .str .r12 .r7 (b + 4 * n)] : List Instr) := by
  simp [copyWords, List.range_succ, List.flatMap_append]

/-- `n` words from `ctx + a` to `ctx + b`. -/
theorem copyWords_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {a b n : Nat} (hab : a + 4 * n ≤ b ∨ b + 4 * n ≤ a)
    (ha : a + 4 * n ≤ 632) (hb : b + 4 * n ≤ 632) {s : State} (h7 : s.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀)
    (hc : VG.Proof.ChaCha20Poly1305.Arm.CtxOk s₀ s) :
    WP isa (.block (copyWords a b n)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ b (4 * n)] s.mem s'.mem ∧
      ∀ i < n, s'.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (b + 4 * i)) 32 = s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (a + 4 * i)) 32 := by
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by lit_omega)⟩
  | succ n ih =>
    rw [VG.Proof.ChaCha20Poly1305.Arm.copyWords_step]
    refine WP.block_append (WP.mono (ih (by lit_omega) (by lit_omega) (by lit_omega))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : VG.Proof.ChaCha20Poly1305.Arm.CtxOk s₀ s₁ := by rw [VG.Proof.ChaCha20Poly1305.Arm.CtxOk, rd₁, wr₁]; exact hc
    have h7₁ : s₁.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [g₁ _ (by decide), h7]
    refine wp_ldr (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (a + 4 * n)) (by lit_omega) (by rw [h7₁]; exact hp.addr_cP_off (by lit_omega))
      (hc₁ _ 4 (by lit_omega)).1 fun s₂ u₂ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (b + 4 * n)) (by lit_omega)
      (by rw [u₂.other _ (by decide), h7₁]; exact hp.addr_cP_off (by lit_omega))
      (by rw [u₂.wr]; exact (hc₁ _ 4 (by lit_omega)).2) fun s₃ u₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr], by rw [u₃.rd, u₂.rd, rd₁],
      by rw [u₃.wr, u₂.wr, wr₁], by rw [u₃.sp, u₂.sp, sp₁], ?_, fun i hi => ?_⟩
    · rw [u₃.mem, u₂.mem]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by lit_omega)
      · exact VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (w := 32 / 8) (by lit_omega) (by lit_omega) (by lit_omega)
    · rw [u₃.mem, u₂.gpr, u₂.mem]
      by_cases h : i = n
      · subst h
        rw [Mem.readW_writeW_self32]
        exact f₁.readW (VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (k := a + 4 * i) (n := 4) (w := 32 / 8) (Nat.le_refl _) (by lit_omega) (by lit_omega))
          (by simp only [List.mem_singleton, forall_eq]; exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
          (by decide)
      · rw [VG.Proof.ChaCha20Poly1305.Arm.readW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), w₁ i (by lit_omega)]

/-- Words copied are bytes copied. -/
theorem bytes_of_words {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (q + BitVec.ofNat 64 (4 * k)) 32 = m.readW (p + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' q (4 * n) = bytesAt m p (4 * n) := by
  refine VG.Proof.ChaCha20Poly1305.Arm.bytesAt_eq_of fun i hi => ?_
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) := by
    intro a
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e, e, Mem.readW_byte m' (q + BitVec.ofNat 64 (4 * (i / 4))) (Nat.mod_lt _ (by lit_omega)),
    Mem.readW_byte m (p + BitVec.ofNat 64 (4 * (i / 4))) (Nat.mod_lt _ (by lit_omega)), h _ (by lit_omega)]

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m`, the key at `kp` and the nonce at `np`. -/
def wordOf (m : Mem) (kp np : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then consts.getD k 0
  else if k < 12 then m.readW (VG.Proof.ChaCha20Poly1305.Arm.off kp (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (VG.Proof.ChaCha20Poly1305.Arm.off np (4 * (k - 13))) 32

theorem stW_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {k : Nat} (hk : k < 16) {s : State} (h7 : s.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀)
    (h0 : s.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.kP s₀) (h1 : s.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.nP s₀) (hrd : s.rd = s₀.rd) (hc : VG.Proof.ChaCha20Poly1305.Arm.CtxOk s₀ s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * k)) (VG.Proof.ChaCha20Poly1305.Arm.wordOf s.mem (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) (VG.Proof.ChaCha20Poly1305.Arm.np s₀) k) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o := (hc (stOff + 4 * k) 4 (by simp [stOff]; omega)).2
  have ea : State.addr (VG.Proof.ChaCha20Poly1305.Arm.cP s₀ + BitVec.ofNat 32 (stOff + 4 * k)) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * k) :=
    hp.addr_cP_off (by simp [stOff]; omega)
  unfold stW stSrc VG.Proof.ChaCha20Poly1305.Arm.wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true, List.cons_append, List.nil_append]
    refine VG.Proof.ChaCha20Poly1305.Arm.wp_movw fun s₁ u₁ => VG.Proof.ChaCha20Poly1305.Arm.wp_movt fun s₂ u₂ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * k)) (by simp [stOff]; omega)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h7]; exact ea)
      (by rw [u₂.wr, u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, movw_movt], fun r hr => by
      rw [g₃.gpr, u₂.other r hr, u₁.other r hr], by rw [g₃.rd, u₂.rd, u₁.rd], by rw [g₃.wr, u₂.wr, u₁.wr],
      by rw [g₃.sp, u₂.sp, u₁.sp]⟩
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.nil_append]
    refine wp_ldr (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) (4 * (k - 4))) (by lit_omega)
      (by rw [h0]; exact hp.addr_kP_off (by lit_omega)) (hp.k_in (by lit_omega) hrd) fun s₁ u₁ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * k)) (by simp [stOff]; omega)
      (by rw [u₁.other _ (by decide), h7]; exact ea) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  by_cases h₃ : k = 12
  · simp only [h₃, ite_true]
    refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * 12)) (by simp [stOff])
      (by rw [u₁.other _ (by decide), h7]; exact h₃ ▸ ea) (by rw [u₁.wr]; exact h₃ ▸ o)
      fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem]; simp, fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  · simp only [h₁, h₂, h₃, ite_false, List.cons_append, List.nil_append]
    refine wp_ldr (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.np s₀) (4 * (k - 13))) (by lit_omega)
      (by rw [h1]; exact hp.addr_nP_off (by lit_omega)) (hp.n_in (by lit_omega) hrd) fun s₁ u₁ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * k)) (by simp [stOff]; omega)
      (by rw [u₁.other _ (by decide), h7]; exact ea) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩

/-- A frame of `ctx[k, k + n)` is one of the context. -/
theorem frame_ctx {s₀ : State} {m m' : Mem} {k n : Nat} (hf : Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n] m m') (h : k + n ≤ 632) :
    Frame [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by simp, VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ h⟩

/-- Words outside the context are unchanged by a frame of the context. -/
theorem readW_out {s₀ : State} {m m' : Mem} (hf : Frame [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] m m') {p : Addr} {n : Nat}
    (hd : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint ⟨p, n⟩) {a : Nat} (ha : a + 4 ≤ n) :
    m'.readW (VG.Proof.ChaCha20Poly1305.Arm.off p a) 32 = m.readW (VG.Proof.ChaCha20Poly1305.Arm.off p a) 32 :=
  hf.readW (r := ⟨VG.Proof.ChaCha20Poly1305.Arm.off p a, 4⟩) (Region.contains_self _ _)
    (by simp only [List.mem_singleton, forall_eq]; exact (hd.sub_right (Offset.sub_base p (d := a) (n := 4) ha)).symm)
    (by decide)

theorem wordOf_frame {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {m m' : Mem} (hf : Frame [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] m m') {k : Nat}
    (hk : k < 16) :
    VG.Proof.ChaCha20Poly1305.Arm.wordOf m' (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) (VG.Proof.ChaCha20Poly1305.Arm.np s₀) k = VG.Proof.ChaCha20Poly1305.Arm.wordOf m (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) (VG.Proof.ChaCha20Poly1305.Arm.np s₀) k := by
  unfold VG.Proof.ChaCha20Poly1305.Arm.wordOf
  split_ifs
  · rfl
  · exact VG.Proof.ChaCha20Poly1305.Arm.readW_out hf hp.c_k (by lit_omega)
  · rfl
  · exact VG.Proof.ChaCha20Poly1305.Arm.readW_out hf hp.c_n (by lit_omega)

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {j : Nat} (hj : j ≤ 16) {s : State}
    (h7 : s.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀) (h0 : s.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.kP s₀) (h1 : s.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.nP s₀) (hrd : s.rd = s₀.rd)
    (hc : VG.Proof.ChaCha20Poly1305.Arm.CtxOk s₀ s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ stOff (4 * j)] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * i)) 32 = VG.Proof.ChaCha20Poly1305.Arm.wordOf s.mem (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) (VG.Proof.ChaCha20Poly1305.Arm.np s₀) i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by lit_omega)⟩
  | succ j ih =>
    rw [VG.Proof.ChaCha20Poly1305.Arm.initState_step]
    refine WP.block_append (WP.mono (ih (by lit_omega)) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : VG.Proof.ChaCha20Poly1305.Arm.CtxOk s₀ s₁ := by rw [VG.Proof.ChaCha20Poly1305.Arm.CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.stW_ok hp (by lit_omega) (by rw [g₁ _ (by decide), h7]) (by rw [g₁ _ (by decide), h0])
      (by rw [g₁ _ (by decide), h1]) (by rw [rd₁, hrd]) hc₁)
      fun s₂ ⟨m₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁],
      ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by lit_omega)
      · exact VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (w := 32 / 8) (by lit_omega) (by lit_omega) (by simp [stOff]; omega)
    · rw [m₂, VG.Proof.ChaCha20Poly1305.Arm.wordOf_frame hp (VG.Proof.ChaCha20Poly1305.Arm.frame_ctx f₁ (by simp [stOff]; omega)) (k := j) (by lit_omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [VG.Proof.ChaCha20Poly1305.Arm.readW_off _ _ _ (by simp [stOff]; omega) (by simp [stOff]; omega) (by lit_omega)]
        exact w₁ i (by lit_omega)

theorem consts_eq : ∀ i < 4, consts.getD i 0 = Spec.ChaCha20.constants.getD i 0 := by decide +kernel

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce, if the key and the nonce are as on entry. -/
theorem stateAt_initState {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {m₁ m' : Mem} (hf₁ : Frame [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * i)) 32 = VG.Proof.ChaCha20Poly1305.Arm.wordOf m₁ (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) (VG.Proof.ChaCha20Poly1305.Arm.np s₀) i) :
    stateAt m' (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff + BitVec.ofNat 64 (4 * i) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 4 * i) from VG.Proof.ChaCha20Poly1305.Arm.off_off _ _ _,
    hw i hi]
  unfold VG.Proof.ChaCha20Poly1305.Arm.wordOf
  split_ifs with h₁ h₂ h₃
  · exact VG.Proof.ChaCha20Poly1305.Arm.consts_eq i h₁
  · rw [VG.Proof.ChaCha20Poly1305.Arm.readW_out hf₁ hp.c_k (by lit_omega), show (VG.Proof.ChaCha20Poly1305.Arm.K s₀) = Spec.ChaCha20.bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) 32 from rfl,
      VG.Proof.ChaCha20Poly1305.wordLE_bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.kp s₀) (n := 32) (j := i - 4) (by lit_omega)]
  · rfl
  · rw [VG.Proof.ChaCha20Poly1305.Arm.readW_out hf₁ hp.c_n (by lit_omega), show (VG.Proof.ChaCha20Poly1305.Arm.N s₀) = Spec.ChaCha20.bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.np s₀) 12 from rfl,
      VG.Proof.ChaCha20Poly1305.wordLE_bytesAt s₀.mem (VG.Proof.ChaCha20Poly1305.Arm.np s₀) (n := 12) (j := i - 13) (by lit_omega)]

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by lit_omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## The first block -/

theorem sub_zero (s₀ : State) (n : Nat) : VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 n = ⟨VG.Proof.ChaCha20Poly1305.Arm.cx s₀, n⟩ := by simp [VG.Proof.ChaCha20Poly1305.Arm.sub, VG.Proof.ChaCha20Poly1305.Arm.off]

/-- The regions of the context `[k, k + n)` are within the context, and so
within the regions of the invariant's frame. -/
theorem sub_inv (s₀ : State) {k n : Nat} (h : k + n ≤ 632) :
    ∃ r' ∈ [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, VG.Proof.ChaCha20Poly1305.Arm.dR s₀, VG.Proof.ChaCha20Poly1305.Arm.belR s₀], Region.Sub (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) r' :=
  ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by simp, VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ h⟩

/-- After the first block: the registers saved and moved, and the ChaCha20
state. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  inv : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s
  st : stateAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀)
  fctx : Frame [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] s₀.mem s.mem

theorem initStateBlock_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s₁ : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s₁)
    (h0 : s₁.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.kP s₀) (h1 : s₁.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.nP s₀) (hf : Frame [VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] s₀.mem s₁.mem) :
    WP isa (.block initState) s₁ fun s₂ => VG.Proof.ChaCha20Poly1305.Arm.Post1 s₀ s₂ ∧ Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ stOff (4 * 16)] s₁.mem s₂.mem := by
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.initState_ok hp (j := 16) (Nat.le_refl _) h.regs.r7 h0 h1 h.rd (Inv.ctxOk hp h.rd h.wr))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, f₂, w₂⟩ => ⟨⟨?_, VG.Proof.ChaCha20Poly1305.Arm.stateAt_initState hp hf w₂,
      hf.trans (VG.Proof.ChaCha20Poly1305.Arm.frame_ctx f₂ (by simp [stOff]))⟩, f₂⟩
  have hk₂ : VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ stOff (4 * 16)] s₁ s₂ :=
    ⟨fun r hr _ => g₂ r (by rintro rfl; simp [preserved] at hr), sp₂, rd₂, wr₂, f₂⟩
  exact h.step1 hk₂ (by simp [stOff]) (by simp [stOff, savOff])

/-- The first block of both functions. -/
theorem block1_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) :
    WP isa (.block (entry ++ save ++ moves ++ initState)) s₀ (VG.Proof.ChaCha20Poly1305.Arm.Post1 s₀) :=
  VG.Proof.ChaCha20Poly1305.Arm.saveMoves_ok hp fun s₁ rg h0 h1 sp rd wr sv f₁ => WP.mono (VG.Proof.ChaCha20Poly1305.Arm.initStateBlock_ok hp
    ⟨rg, sp, rd, wr, sv, f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20Poly1305.Arm.sub_inv s₀ (by simp [savOff])⟩
    h0 h1 (VG.Proof.ChaCha20Poly1305.Arm.frame_ctx f₁ (by simp [savOff]))) fun _ h => h.1

/-! ## The one-time key -/

theorem hr7 {s₀ s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) : s.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := h.regs.r7

/-- `r0 = r7 + stOff`, `r1 = r7`. -/
theorem kgA_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa (.block [.dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r7)]) s fun s' =>
      s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ stOff ∧ s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := by
  have core : WP isa (.block [.dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r7)]) s
      fun s' => s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ stOff ∧ s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_add (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr, VG.Proof.ChaCha20Poly1305.Arm.hr7 h], by rw [u₂.gpr, u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h0, h1, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h0, h1, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- After the one-time key is computed. -/
structure PostK (s₀ : State) (s : State) : Prop where
  inv : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s
  st : stateAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀)
  key : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) keyOff) 32 = VG.Proof.ChaCha20Poly1305.Arm.otk s₀

theorem keyGen_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Post1 s₀ s) :
    WP isa keyGen s fun s' => VG.Proof.ChaCha20Poly1305.Arm.PostK s₀ s' ∧ Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 256, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ keyOff 32] s.mem s'.mem := by
  unfold keyGen
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.kgA_ok h.inv) fun s₁ ⟨h0, h1, k₁⟩ => ?_)
  have i₁ := h.inv.step0 k₁
  have m₁ := k₁.mem_eq
  refine WP.seq (VG.Proof.ChaCha20Poly1305.Arm.block_call h0 h1 (by
      rw [hp.addr_ptr (by simp [stOff]), ← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]
      exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (a := 0) (n := 256) (by simp [stOff]) (by lit_omega) (by simp [stOff]))
    (by rw [hp.ptr_toNat (by simp [stOff])]; have := hp.fit_c; simp [stOff]; omega)
    (by have := hp.fit_c; omega)
    (by rw [hp.addr_ptr (by simp [stOff]), ← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]
        exact VG.Proof.ChaCha20Poly1305.Arm.covers2 hp i₁.wr (a := 0) (n := 256) (b := stOff) (m := 64) (by lit_omega) (by simp [stOff]))
    (by rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact VG.Proof.ChaCha20Poly1305.Arm.covers1 hp i₁.wr (a := 0) (n := 256) (by lit_omega)) fun s₂ k₂ r1₂ blk₂ => ?_)
  rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero] at k₂
  have i₂ := i₁.step1 k₂ (by lit_omega) (by simp [savOff])
  -- `mov r7, r1`, then the copy.
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  have h7₃ : s₃.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₃.gpr, r1₂]
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.copyWords_ok hp (a := 0) (b := keyOff) (n := 8) (by simp [keyOff]) (by lit_omega)
    (by simp [keyOff]) h7₃ (Inv.ctxOk hp (by rw [u₃.rd, i₂.rd]) (by rw [u₃.wr, i₂.wr])))
    fun s₄ ⟨g₄, rd₄, wr₄, sp₄, f₄, w₄⟩ => ?_
  have g₃ : ∀ r, s₃.gpr r = s₂.gpr r := fun r => by
    by_cases e : r = .r7
    · subst e; rw [h7₃, i₂.regs.r7]
    · exact u₃.other r e
  have hk₄ : VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ keyOff (4 * 8)] s₂ s₄ :=
    ⟨fun r hr _ => by rw [g₄ r (by rintro rfl; simp [preserved] at hr), g₃ r],
      by rw [sp₄, u₃.sp], by rw [rd₄, u₃.rd], by rw [wr₄, u₃.wr], by rw [← u₃.mem]; exact f₄⟩
  have i₄ := i₂.step1 hk₄ (by simp [keyOff]) (by simp [keyOff, savOff])
  refine ⟨⟨i₄, ?_, ?_⟩, ?_⟩
  · -- The ChaCha20 state is outside both writes.
    rw [VG.Proof.ChaCha20Poly1305.Arm.stateAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [stOff, keyOff]) (by simp [stOff]) (by simp [keyOff])),
      u₃.mem, VG.Proof.ChaCha20Poly1305.Arm.stateAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (a := stOff) (n := 64) (b := 0) (m := 256) (by simp [stOff]) (by simp [stOff])
          (by lit_omega)), m₁, h.st]
  · have e : bytesAt s₄.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) keyOff) (4 * 8) = bytesAt s₃.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) 0) (4 * 8) :=
      VG.Proof.ChaCha20Poly1305.Arm.bytes_of_words fun k hk => by rw [VG.Proof.ChaCha20Poly1305.Arm.off_add, VG.Proof.ChaCha20Poly1305.Arm.off_add]; exact w₄ k hk
    rw [show (32 : Nat) = 4 * 8 from rfl, e, u₃.mem, VG.Proof.ChaCha20Poly1305.Arm.off_zero, VG.Proof.ChaCha20Poly1305.Arm.bytesAt_serialize _ _ (by lit_omega), blk₂, m₁,
      hp.addr_ptr (by simp [stOff]), h.st]
    rfl
  · refine (k₁.frame.sub fun _ hr => absurd hr List.not_mem_nil).trans ((k₂.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · rw [← u₃.mem]
      exact f₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-! ## The Poly1305 state -/

/-- `r0 = r7`, `r1 = r7 + keyOff`. -/
theorem piA_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa (.block [.mov .r0 (.reg .r7), .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 keyOff))]) s fun s' =>
      s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧ s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ keyOff ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := by
  have core : WP isa (.block [.mov .r0 (.reg .r7), .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 keyOff))]) s
      fun s' => s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧ s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ keyOff ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr, VG.Proof.ChaCha20Poly1305.Arm.hr7 h], by rw [u₂.gpr, u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h0, h1, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h0, h1, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `mov r7, r0` with `r0` the context. -/
theorem anchor_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {r : Reg} (hr : s.gpr r = VG.Proof.ChaCha20Poly1305.Arm.cP s₀) :
    WP isa (.block [.mov .r7 (.reg r)]) s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_
  have g : ∀ q, s₁.gpr q = s.gpr q := fun q => by
    by_cases e : q = .r7
    · subst e; rw [u₁.gpr, hr, VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
    · exact u₁.other q e
  have hk : VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s₁ := ⟨fun q _ _ => g q, u₁.sp, u₁.rd, u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _⟩
  exact ⟨h.step0 hk, hk⟩

theorem polyInit_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s)
    (hkey : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) keyOff) 32 = VG.Proof.ChaCha20Poly1305.Arm.otk s₀) :
    WP isa polyInit s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128] s s' ∧ Repr s'.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) [] := by
  unfold polyInit
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.piA_ok h) fun s₁ ⟨h0, h1, k₁⟩ => ?_)
  have i₁ := h.step0 k₁
  refine WP.seq (VG.Proof.ChaCha20Poly1305.Arm.init_call h0 h1 (by
      rw [hp.addr_ptr (by simp [keyOff]), ← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]
      exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (a := 0) (n := 128) (by simp [keyOff]) (by lit_omega) (by simp [keyOff]))
    (by have := hp.fit_c; omega)
    (by rw [hp.ptr_toNat (by simp [keyOff])]; have := hp.fit_c; simp [keyOff]; omega)
    (by rw [hp.addr_ptr (by simp [keyOff]), ← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]
        exact VG.Proof.ChaCha20Poly1305.Arm.covers2 hp i₁.wr (a := 0) (n := 128) (b := keyOff) (m := 32) (by lit_omega) (by simp [keyOff]))
    (by rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact VG.Proof.ChaCha20Poly1305.Arm.covers1 hp i₁.wr (a := 0) (n := 128) (by lit_omega)) fun s₂ k₂ r0₂ repr₂ => ?_)
  rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero] at k₂
  have i₂ := i₁.step1 k₂ (by lit_omega) (by simp [savOff])
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.anchor_ok i₂ r0₂) fun s₃ ⟨i₃, k₃⟩ => ⟨i₃, (k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans
    (k₂.trans (k₃.sub fun _ hr => absurd hr List.not_mem_nil)), ?_⟩
  rw [k₃.mem_eq]
  rw [hp.addr_ptr (by simp [keyOff]), k₁.mem_eq, hkey] at repr₂
  exact repr₂

end VG.Proof.ChaCha20Poly1305.Arm

end

/-!
# ChaCha20-Poly1305 on ARMv7: absorbing padded data

`macPad p n` absorbs the `n` bytes at `p` into the Poly1305 state (at `ctx`),
and zeros to a multiple of 16: `msg ++ x ++ pad16 x`.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_and wp_subs wp_cmp wp_ldr wp_str
  wp_ldrb wp_strb op2_imm op2_reg op2_lsr eval_eq eval_ne ofNat_beq_zero sub_ofNat ofNat_shr)
open VG.Proof.ChaCha20.Arm.Xor (writeW8_apply)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-- The Poly1305 state and the padded block. -/
abbrev macR (s₀ : State) : List Region := [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16]

theorem kept_mac {s₀ s s' : State} {k n : Nat} (hk : VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n] s s')
    (h : (k = 0 ∧ n = 128) ∨ (k = padOff ∧ n = 16)) : VG.Proof.ChaCha20Poly1305.Arm.Kept (VG.Proof.ChaCha20Poly1305.Arm.macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, by simp, fun _ h => h⟩

theorem kept_mac0 {s₀ s s' : State} (hk : VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s') : VG.Proof.ChaCha20Poly1305.Arm.Kept (VG.Proof.ChaCha20Poly1305.Arm.macR s₀) s s' :=
  hk.sub fun _ hr => absurd hr List.not_mem_nil

theorem mac_inv {s₀ s s' : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) (hk : VG.Proof.ChaCha20Poly1305.Arm.Kept (VG.Proof.ChaCha20Poly1305.Arm.macR s₀) s s') : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact VG.Proof.ChaCha20Poly1305.Arm.sub_inv s₀ (by simp [padOff]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [savOff, padOff]) (by simp [savOff])
        (by simp [padOff]))

/-! ## Absorbing whole blocks -/

/-- `n` blocks at `p` absorbed, from `r1 = p` and `r2 = n`. -/
theorem absorb_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {p : BitVec 32} {n : Nat}
    (h1 : s.gpr .r1 = p) (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (hn : 16 * n < 2 ^ 32)
    (hdj : (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128).Disjoint ⟨State.addr p, 16 * n⟩) (hfit : p.toNat + 16 * n ≤ 2 ^ 32)
    (hc : Covers [⟨State.addr p, 16 * n⟩] (s₀.rd ++ s₀.wr)) :
    WP isa absorb s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128] s s' ∧
      ∀ key msg, Repr s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg →
        Repr s'.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key (msg ++ bytesAt s.mem (State.addr p) (16 * n)) := by
  unfold absorb
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s₁ := ⟨fun r hr _ => u₁.other r (by rintro rfl; simp [preserved] at hr), u₁.sp,
    u₁.rd, u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _⟩
  have i₁ := h.step0 k₁
  refine WP.seq (VG.Proof.ChaCha20Poly1305.Arm.blocks_call (P := VG.Proof.ChaCha20Poly1305.Arm.cP s₀) (p := p) (n := n) (by rw [u₁.gpr, VG.Proof.ChaCha20Poly1305.Arm.hr7 h])
    (by rw [u₁.other _ (by decide), h1]) (by rw [u₁.other _ (by decide), h2]) hn
    (by rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact hdj) (by have := hp.fit_c; simp only [VG.Proof.ChaCha20Poly1305.Arm.cP] at this ⊢; omega) hfit (fun a w hi => ?_)
    (by rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact VG.Proof.ChaCha20Poly1305.Arm.covers1 hp i₁.wr (a := 0) (n := 128) (by lit_omega)) fun s₂ k₂ r0₂ repr₂ => ?_)
  · obtain ⟨r, hr, hcn⟩ := hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [i₁.rd, i₁.wr]; exact hc a w ⟨_, List.mem_singleton_self _, hcn⟩
    · rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero] at hcn
      exact Covers.right (VG.Proof.ChaCha20Poly1305.Arm.covers1 hp i₁.wr (a := 0) (n := 128) (by lit_omega)) a w ⟨_, List.mem_singleton_self _, hcn⟩
  rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero] at k₂
  have i₂ := i₁.step1 k₂ (by lit_omega) (by simp [savOff])
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.anchor_ok i₂ r0₂) fun s₃ ⟨i₃, k₃⟩ => ⟨i₃, (k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans
    (k₂.trans (k₃.sub fun _ hr => absurd hr List.not_mem_nil)), fun key msg hr => ?_⟩
  rw [k₃.mem_eq, ← k₁.mem_eq]
  exact repr₂ key msg (by rw [k₁.mem_eq]; exact hr)

/-! ## Zeroing the padded block -/

theorem writeW32_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · simp
  · rfl

theorem padZ_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa (.block [.mov .r12 (.imm 0), .str .r12 .r7 padOff, .str .r12 .r7 (padOff + 4),
      .str .r12 .r7 (padOff + 8), .str .r12 .r7 (padOff + 12),
      .dp .add .r2 .r7 (.imm (BitVec.ofNat 32 padOff))]) s fun s' =>
      s'.gpr .r2 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ padOff ∧ (∀ r, r ≠ .r12 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + j)) = 0 := by
  have o : ∀ d, d < 4 → InRegions s.wr (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * d)) 4 := fun d hd => by
    rw [h.wr]; exact hp.in_ctx (by simp [padOff]; omega)
  have ea : ∀ d, d < 4 → State.addr (VG.Proof.ChaCha20Poly1305.Arm.cP s₀ + BitVec.ofNat 32 (padOff + 4 * d)) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * d) :=
    fun d hd => hp.addr_cP_off (by simp [padOff]; omega)
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have h7 : s₁.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
  refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 0)) (by simp [padOff]) (by rw [h7]; exact ea 0 (by lit_omega))
    (by rw [u₁.wr]; exact o 0 (by lit_omega)) fun s₂ g₂ => ?_
  refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 1)) (by simp [padOff]) (by rw [g₂.gpr, h7]; exact ea 1 (by lit_omega))
    (by rw [g₂.wr, u₁.wr]; exact o 1 (by lit_omega)) fun s₃ g₃ => ?_
  refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 2)) (by simp [padOff])
    (by rw [g₃.gpr, g₂.gpr, h7]; exact ea 2 (by lit_omega))
    (by rw [g₃.wr, g₂.wr, u₁.wr]; exact o 2 (by lit_omega)) fun s₄ g₄ => ?_
  refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 3)) (by simp [padOff])
    (by rw [g₄.gpr, g₃.gpr, g₂.gpr, h7]; exact ea 3 (by lit_omega))
    (by rw [g₄.wr, g₃.wr, g₂.wr, u₁.wr]; exact o 3 (by lit_omega)) fun s₅ g₅ => ?_
  refine wp_add (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have x12 : s₁.gpr .r12 = 0 := u₁.gpr
  have hm : s₆.mem = (((s.mem.writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 0)) (0 : BitVec 32)).writeW
      (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 1)) (0 : BitVec 32)).writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 2)) (0 : BitVec 32)).writeW
      (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * 3)) (0 : BitVec 32) := by
    rw [u₆.mem, g₅.mem, g₄.gpr, g₄.mem, g₃.gpr, g₃.mem, g₂.gpr, g₂.mem, u₁.mem, x12]
  refine ⟨by rw [u₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, h7], fun r h₁ h₂ => by
      rw [u₆.other _ h₂, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, u₁.other _ h₁],
    by rw [u₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, u₁.rd], by rw [u₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, u₁.wr],
    by rw [u₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, u₁.sp], ?_, fun j hj => ?_⟩
  · rw [hm]
    have c : ∀ d, d < 4 → (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16).Contains (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + 4 * d)) (32 / 8) :=
      fun d hd => VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (by lit_omega) (by lit_omega) (by simp [padOff])
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 1 (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 2 (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 3 (by lit_omega))
  · rw [hm]
    have e : ∀ d, d ≤ j → (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + j) - VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + d)).toNat = j - d := by
      intro d hd
      rw [Offset.sub_toNat _ (Nat.add_le_add_left hd _) (by simp only [padOff]; omega)]
      omega
    have e' : ∀ d, j < d → d < 16 → ¬ (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + j) - VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + d)).toNat < 4 := by
      intro d hd hd'
      rw [Offset.sub_toNat' _ (by simp only [padOff]; omega) (by simp only [padOff]; omega)]
      split <;> omega
    simp only [VG.Proof.ChaCha20Poly1305.Arm.writeW32_zero_apply]
    rcases (by omega : j < 4 ∨ (4 ≤ j ∧ j < 8) ∨ (8 ≤ j ∧ j < 12) ∨ 12 ≤ j) with hj' | hj' | hj' | hj'
    · simp (disch := omega) only [e' (4 * 3), e' (4 * 2), e' (4 * 1), ite_false, e (4 * 0),
        Nat.mul_zero, Nat.sub_zero, hj', ite_true]
    · simp (disch := omega) only [e' (4 * 3), e' (4 * 2), ite_false, e (4 * 1), show j - 4 * 1 < 4 by omega,
        ite_true]
    · simp (disch := omega) only [e' (4 * 3), ite_false, e (4 * 2), show j - 4 * 2 < 4 by omega, ite_true]
    · simp (disch := omega) only [e (4 * 3), show j - 4 * 3 < 4 by omega, ite_true]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : BitVec 32) (t i : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = Q + BitVec.ofNat 32 i
  r2 : s.gpr .r2 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ (padOff + i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (t - i)
  keep : ∀ r ∈ preserved, s.gpr r = s₂.gpr r
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + j)) =
    if j < i then s₂.mem (State.addr Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.ldrb .r12 .r1 0, .strb .r12 .r2 0, .dp .add .r1 .r1 (.imm 1), .dp .add .r2 .r2 (.imm 1),
   .subs .r3 .r3 (.imm 1)]

theorem copyLoop_eq : copyLoop = .loop (.block VG.Proof.ChaCha20Poly1305.Arm.copyBody) .ne := rfl

theorem byte_rt (b : Byte) : ((b.setWidth 32).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by lit_omega), BitVec.setWidth_eq]

theorem off_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) : VG.Proof.ChaCha20Poly1305.Arm.off p a ≠ VG.Proof.ChaCha20Poly1305.Arm.off p b := by
  intro he
  have e : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
    have e := congrArg (· - p) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
  exact h this

theorem add_ofNat32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem copy_step {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s₂ : State} {Q : BitVec 32} {t : Nat} (ht : t < 16)
    (hwr : s₂.wr = s₀.wr) (hQ : Q.toNat + t ≤ 2 ^ 32)
    (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (State.addr Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨State.addr Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16))
    {i : Nat} (hi : i < t) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.CpInv s₀ s₂ Q t i s) :
    WP isa (.block VG.Proof.ChaCha20Poly1305.Arm.copyBody) s fun s' => VG.Proof.ChaCha20Poly1305.Arm.CpInv s₀ s₂ Q t (i + 1) s' ∧ s'.z = (BitVec.ofNat 32 (t - (i + 1)) == 0) := by
  have hin : InRegions (s.rd ++ s.wr) (State.addr Q + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + i)) 1 := by
    rw [h.wr, hwr]; exact hp.in_ctx (by simp [padOff]; omega)
  unfold VG.Proof.ChaCha20Poly1305.Arm.copyBody
  refine wp_ldrb (a := State.addr Q + BitVec.ofNat 64 i) (by decide)
    (by rw [h.r1, show Q + BitVec.ofNat 32 i + BitVec.ofNat 32 0 = Q + BitVec.ofNat 32 i from BitVec.add_zero _]
        exact addr_add (a := Q) (k := i) (by lit_omega)) hin fun s₁ u₁ => ?_
  refine wp_strb (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + i)) (by decide)
    (by rw [u₁.other _ (by decide), h.r2,
          show VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ (padOff + i) + BitVec.ofNat 32 0 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ (padOff + i) from BitVec.add_zero _]
        exact hp.addr_ptr (by simp [padOff]; omega))
    (by rw [u₁.wr]; exact hout) fun s₂' g₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  have r3₄ : s₄.gpr .r3 = BitVec.ofNat 32 (t - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r3]
  have e3 : s₄.gpr .r3 - 1 = BitVec.ofNat 32 (t - (i + 1)) := by
    rw [r3₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by lit_omega), Nat.sub_sub]
  have hm : s₅.mem = s.mem.writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + i)) (s.mem (State.addr Q + BitVec.ofNat 64 i)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, VG.Proof.ChaCha20Poly1305.Arm.byte_rt]
  have hg : ∀ r ∈ preserved, s₅.gpr r = s.gpr r := fun r hr => by
    have h1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
    have h2 : r ≠ .r2 := by rintro rfl; simp [preserved] at hr
    have h3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, g₂.gpr, u₁.other _ h12]
  refine ⟨⟨?_, ?_, ?_, fun r hr => by rw [hg r hr, h.keep r hr], ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.ChaCha20Poly1305.Arm.add_ofNat32]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.ChaCha20Poly1305.Arm.ptr, VG.Proof.ChaCha20Poly1305.Arm.add_ofNat32, Nat.add_assoc]
  · rw [u₅.gpr, e3]
  · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
  · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (w := 8 / 8) (by lit_omega) (by lit_omega)
      (by simp [padOff]))
  · have hbyte : s.mem (State.addr Q + BitVec.ofNat 64 i) = s₂.mem (State.addr Q + BitVec.ofNat 64 i) :=
      h.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdisj i hi _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
    rw [hm, VG.Proof.ChaCha20.Arm.Xor.writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, hbyte]
    · simp only [VG.Proof.ChaCha20Poly1305.Arm.off_ne (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (a := padOff + k) (b := padOff + i) (by simp [padOff]; omega)
        (by simp [padOff]; omega) (by lit_omega), ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [z₅, e3]

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) padOff) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) padOff + BitVec.ofNat 64 k = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (padOff + k) from VG.Proof.ChaCha20Poly1305.Arm.off_off _ _ _, h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

theorem padTail_eq : padTail =
    .seq (.block [.mov .r12 (.imm 0), .str .r12 .r7 padOff, .str .r12 .r7 (padOff + 4),
      .str .r12 .r7 (padOff + 8), .str .r12 .r7 (padOff + 12),
      .dp .add .r2 .r7 (.imm (BitVec.ofNat 32 padOff))])
    (.seq (.loop (.block VG.Proof.ChaCha20Poly1305.Arm.copyBody) .ne)
    (.seq (.block [.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 padOff)), .mov .r2 (.imm 1)]) absorb)) := rfl

theorem ptA_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa (.block [.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 padOff)), .mov .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ padOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := by
  have core : WP isa (.block [.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 padOff)), .mov .r2 (.imm 1)]) s
      fun s' => s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ padOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_add (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr, VG.Proof.ChaCha20Poly1305.Arm.hr7 h], by rw [u₂.gpr]; rfl,
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem padTail_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {Q : BitVec 32} {t : Nat}
    (ht0 : 0 < t) (ht : t < 16) (h1 : s.gpr .r1 = Q) (h3 : s.gpr .r3 = BitVec.ofNat 32 t)
    (hQ : Q.toNat + t ≤ 2 ^ 32)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (State.addr Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨State.addr Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16)) :
    WP isa padTail s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept (VG.Proof.ChaCha20Poly1305.Arm.macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg →
        Repr s'.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key (msg ++ (bytesAt s.mem (State.addr Q) t ++ List.replicate (16 - t) 0)) := by
  rw [VG.Proof.ChaCha20Poly1305.Arm.padTail_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.padZ_ok hp h) fun s₂ ⟨r2₂, g₂, rd₂, wr₂, sp₂, f₂, z₂⟩ => ?_)
  have src₂ : ∀ j < t, s₂.mem (State.addr Q + BitVec.ofNat 64 j) = s.mem (State.addr Q + BitVec.ofNat 64 j) :=
    fun j hj => f₂ _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj j hj _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  have hk₂ : VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16] s s₂ :=
    ⟨fun r hr _ => g₂ r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr),
      sp₂, rd₂, wr₂, f₂⟩
  have i₂ := h.step1 hk₂ (by simp [padOff]) (by simp [padOff, savOff])
  refine WP.seq (WP.mono (Q := VG.Proof.ChaCha20Poly1305.Arm.CpInv s₀ s₂ Q t t) ?_ fun s₃ h₃ => ?_)
  · let I : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ VG.Proof.ChaCha20Poly1305.Arm.CpInv s₀ s₂ Q t i s
    have hstep : ∀ n s, I n s → WP isa (.block VG.Proof.ChaCha20Poly1305.Arm.copyBody) s (fun s' =>
        (isa.eval .ne s' = some false ∧ VG.Proof.ChaCha20Poly1305.Arm.CpInv s₀ s₂ Q t t s') ∨
        (isa.eval .ne s' = some true ∧ ∃ n' < n, I n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.copy_step hp ht (by rw [i₂.wr]) hQ (by rw [rd₂, wr₂]; exact hsrc) hdisj hi hI)
        fun s' ⟨h', hz⟩ => ?_
      have hz' : isa.eval .ne s' = some (decide (t - (i + 1) ≠ 0)) := by
        show some (!s'.z) = _
        rw [hz, ofNat_beq_zero (by lit_omega)]; simp
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz']; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz']; simp; omega, t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) I hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), h1]; simp,
      by rw [r2₂]; rfl, by rw [g₂ _ (by decide) (by decide), h3]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  have hk₃ : VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16] s₂ s₃ := ⟨fun r hr _ => h₃.keep r hr, h₃.sp, h₃.rd, h₃.wr, h₃.frame⟩
  have i₃ := i₂.step1 hk₃ (by simp [padOff]) (by simp [padOff, savOff])
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.ptA_ok i₃) fun s₄ ⟨h1₄, h2₄, k₄⟩ => ?_)
  have i₄ := i₃.step0 k₄
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.absorb_ok hp i₄ (n := 1) h1₄ h2₄ (by lit_omega)
    (by rw [hp.addr_ptr (by simp [padOff])]
        exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (a := 0) (n := 128) (by simp [padOff]) (by lit_omega) (by simp [padOff]))
    (by rw [hp.ptr_toNat (by simp [padOff])]; have := hp.fit_c; simp [padOff]; omega)
    (by rw [hp.addr_ptr (by simp [padOff])]
        exact Covers.right (VG.Proof.ChaCha20Poly1305.Arm.covers1 hp rfl (a := padOff) (n := 16 * 1) (by simp [padOff]))))
    fun s₅ ⟨i₅, k₅, repr₅⟩ => ⟨i₅, (VG.Proof.ChaCha20Poly1305.Arm.kept_mac hk₂ (.inr ⟨rfl, rfl⟩)).trans ((VG.Proof.ChaCha20Poly1305.Arm.kept_mac hk₃ (.inr ⟨rfl, rfl⟩)).trans
      ((VG.Proof.ChaCha20Poly1305.Arm.kept_mac0 k₄).trans (VG.Proof.ChaCha20Poly1305.Arm.kept_mac k₅ (.inl ⟨rfl, rfl⟩)))), fun key msg hr => ?_⟩
  have m₄ := k₄.mem_eq
  have hr₄ : Repr s₄.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg := by
    rw [m₄]
    refine Repr.frame (f₂.trans h₃.frame) (fun r hr => ?_) hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [padOff]) (by lit_omega) (by simp [padOff])
  have hb : bytesAt s₄.mem (State.addr (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ padOff)) (16 * 1) =
      bytesAt s.mem (State.addr Q) t ++ List.replicate (16 - t) 0 := by
    rw [m₄, hp.addr_ptr (by simp [padOff]), show 16 * 1 = 16 from rfl, VG.Proof.ChaCha20Poly1305.Arm.padded_bytes ht h₃.buf]
    refine congrArg (· ++ _) (VG.Proof.ChaCha20Poly1305.Arm.bytesAt_eq_of fun j hj => src₂ j hj)
  have := repr₅ key msg hr₄
  rwa [hb] at this

/-! ## The whole of `macPad` -/

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .r8 ∨ p = .r10) ∧ (n = .r9 ∨ n = .r11)

theorem MacRegs.p_ne {p n : Reg} (hr : VG.Proof.ChaCha20Poly1305.Arm.MacRegs p n) :
    p ≠ .r0 ∧ p ≠ .r1 ∧ p ≠ .r2 ∧ p ≠ .r3 ∧ p ≠ .r12 ∧ p ∈ preserved ∧ p ≠ .lr := by
  rcases hr.1 with rfl | rfl <;> decide

theorem MacRegs.n_ne {p n : Reg} (hr : VG.Proof.ChaCha20Poly1305.Arm.MacRegs p n) :
    n ≠ .r0 ∧ n ≠ .r1 ∧ n ≠ .r2 ∧ n ≠ .r3 ∧ n ≠ .r12 ∧ n ∈ preserved ∧ n ≠ .lr := by
  rcases hr.2 with rfl | rfl <;> decide

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : BitVec 32) (len : Nat) : Prop where
  lt : len < 2 ^ 32
  fit : P.toNat + len ≤ 2 ^ 32
  ctx : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint ⟨State.addr P, len⟩
  cov : Covers [⟨State.addr P, len⟩] (s₀.rd ++ s₀.wr)

theorem contains_off_sub {P : Addr} {a n len : Nat} {x : Addr} (h : a + n ≤ len)
    (hc : (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Contains x 1) : (⟨P, len⟩ : Region).Contains x 1 :=
  VG.Proof.ChaCha20Poly1305.Arm.sub_off P h x hc

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

theorem macA_ok {p n : Reg} (hr : VG.Proof.ChaCha20Poly1305.Arm.MacRegs p n) (s : State) :
    WP isa (.block [.mov .r1 (.reg p), .mov .r2 (.shifted n .lsr 4)]) s fun s' =>
      s'.gpr .r1 = s.gpr p ∧ s'.gpr .r2 = s.gpr n >>> 4 ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := by
  have hp := hr.p_ne
  have hn := hr.n_ne
  have core : WP isa (.block [.mov .r1 (.reg p), .mov .r2 (.shifted n .lsr 4)]) s fun s' =>
      s'.gpr .r1 = s.gpr p ∧ s'.gpr .r2 = s.gpr n >>> 4 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ hn.2.1],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem macC_ok (n : Reg) (s : State) :
    WP isa (.block [.dp .and .r3 n (.imm 15), .cmp .r3 (.imm 0)]) s fun s' =>
      s'.gpr .r3 = BitVec.ofNat 32 ((s.gpr n).toNat % 16) ∧
      s'.z = (BitVec.ofNat 32 ((s.gpr n).toNat % 16) - 0 == 0) ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := by
  have core : WP isa (.block [.dp .and .r3 n (.imm 15), .cmp .r3 (.imm 0)]) s fun s' =>
      s'.gpr .r3 = BitVec.ofNat 32 ((s.gpr n).toNat % 16) ∧
      s'.z = (BitVec.ofNat 32 ((s.gpr n).toNat % 16) - 0 == 0) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem :=
    wp_and (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ u₂ z₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.gpr, VG.Proof.ChaCha20Poly1305.Arm.and15], by rw [z₂, u₁.gpr, VG.Proof.ChaCha20Poly1305.Arm.and15], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr],
        by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h3, hz, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h3, hz, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem macD_ok {p n : Reg} (hr : VG.Proof.ChaCha20Poly1305.Arm.MacRegs p n) (s : State) :
    WP isa (.block [.dp .sub .r1 n (.reg .r3), .dp .add .r1 p (.reg .r1)]) s fun s' =>
      s'.gpr .r1 = s.gpr p + (s.gpr n - s.gpr .r3) ∧ (∀ r, r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := by
  have hp := hr.p_ne
  have core : WP isa (.block [.dp .sub .r1 n (.reg .r3), .dp .add .r1 p (.reg .r1)]) s fun s' =>
      s'.gpr .r1 = s.gpr p + (s.gpr n - s.gpr .r3) ∧ (∀ r, r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_sub (op2_reg _ _) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.other _ hp.2.1, u₁.gpr], fun r h => by rw [u₂.other _ h, u₁.other _ h],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, hg', hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, hg', Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem macPad_eq (p n : Reg) : macPad p n =
    .seq (.block [.mov .r1 (.reg p), .mov .r2 (.shifted n .lsr 4)])
    (.seq absorb
    (.seq (.block [.dp .and .r3 n (.imm 15), .cmp .r3 (.imm 0)])
      (.ite .eq (.block [])
        (.seq (.block [.dp .sub .r1 n (.reg .r3), .dp .add .r1 p (.reg .r1)]) padTail)))) := rfl

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {p n : Reg} (hr : VG.Proof.ChaCha20Poly1305.Arm.MacRegs p n) {P : BitVec 32} {len : Nat}
    (hs : VG.Proof.ChaCha20Poly1305.Arm.Src s₀ P len) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 32 len) :
    WP isa (macPad p n) s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept (VG.Proof.ChaCha20Poly1305.Arm.macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg →
        Repr s'.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key (msg ++ (bytesAt s.mem (State.addr P) len ++
          pad16 (bytesAt s.mem (State.addr P) len))) := by
  have hpn := hr.p_ne
  have hnn := hr.n_ne
  have hlt := hs.lt
  have hcP : (VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀).Disjoint ⟨State.addr P, len⟩ := hs.ctx
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  rw [VG.Proof.ChaCha20Poly1305.Arm.macPad_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.macA_ok hr s) fun s₁ ⟨r1₁, r2₁, k₁⟩ => ?_)
  have i₁ := h.step0 k₁
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.absorb_ok hp i₁ (p := P) (n := len / 16) (by rw [r1₁, hP])
    (by rw [r2₁, hn, ofNat_shr hlt]) (by lit_omega)
    ((hcP.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix hk)) (by have := hs.fit; omega)
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩))
    fun s₂ ⟨i₂, k₂, repr₂⟩ => ?_)
  have m₁ := k₁.mem_eq
  rw [m₁] at repr₂
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.macC_ok n s₂) fun s₃ ⟨r3₃, z₃, k₃⟩ => ?_)
  have n₂ : s₂.gpr n = BitVec.ofNat 32 len := by
    rw [k₂.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, k₁.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, hn]
  have p₂ : s₂.gpr p = P := by
    rw [k₂.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, k₁.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, hP]
  rw [n₂, VG.Proof.ChaCha20Poly1305.Arm.toNat32 hlt] at r3₃ z₃
  have i₃ := i₂.step0 k₃
  have k₁₃ : VG.Proof.ChaCha20Poly1305.Arm.Kept (VG.Proof.ChaCha20Poly1305.Arm.macR s₀) s s₃ :=
    (VG.Proof.ChaCha20Poly1305.Arm.kept_mac0 k₁).trans ((VG.Proof.ChaCha20Poly1305.Arm.kept_mac k₂ (.inl ⟨rfl, rfl⟩)).trans (VG.Proof.ChaCha20Poly1305.Arm.kept_mac0 k₃))
  have x_eq : bytesAt s.mem (State.addr P) len = bytesAt s.mem (State.addr P) (16 * (len / 16)) ++
      bytesAt s.mem (State.addr P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem (State.addr P) len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₃ := k₃.mem_eq
  refine WP.ite (decide (len % 16 = 0)) (by
      show some s₃.z = _
      rw [z₃, show BitVec.ofNat 32 (len % 16) - 0 = BitVec.ofNat 32 (len % 16) from BitVec.sub_zero _,
        ofNat_beq_zero (by lit_omega)]) (fun hb => ?_) (fun hb => ?_)
  · -- A multiple of 16: nothing to pad.
    have h0 : len % 16 = 0 := by simpa using hb
    refine WP.block_nil ⟨i₃, k₁₃, fun key msg hr => ?_⟩
    rw [m₃]
    have := repr₂ key msg hr
    rwa [show pad16 (bytesAt s.mem (State.addr P) len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using hb
    refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.macD_ok hr s₃) fun s₄ ⟨r1₄, g₄, k₄⟩ => ?_)
    have i₄ := i₃.step0 k₄
    have hQ : s₄.gpr .r1 = P + BitVec.ofNat 32 (16 * (len / 16)) := by
      rw [r1₄, r3₃, k₃.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, n₂, k₃.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, p₂,
        sub_ofNat (by lit_omega), show len - len % 16 = 16 * (len / 16) by omega]
    have hfitQ : (P + BitVec.ofNat 32 (16 * (len / 16))).toNat + len % 16 ≤ 2 ^ 32 := by
      have := hs.fit
      rw [BitVec.toNat_add, VG.Proof.ChaCha20Poly1305.Arm.toNat32 (by lit_omega), Nat.mod_eq_of_lt (by lit_omega)]; omega
    have eQ : State.addr (P + BitVec.ofNat 32 (16 * (len / 16))) = State.addr P + BitVec.ofNat 64 (16 * (len / 16)) :=
      addr_add (by have := hs.fit; omega)
    have hsrc : ∀ j < len % 16, InRegions (s₄.rd ++ s₄.wr)
        (State.addr (P + BitVec.ofNat 32 (16 * (len / 16))) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [i₄.rd, i₄.wr, eQ, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hs.cov _ _ ⟨_, List.mem_singleton_self _, VG.Proof.ChaCha20Poly1305.Arm.contains_off_sub (a := 16 * (len / 16) + j) (n := 1)
        (by lit_omega) (VG.Proof.ChaCha20Poly1305.Arm.self_contains _)⟩
    have hdj : ∀ j < len % 16, (⟨State.addr (P + BitVec.ofNat 32 (16 * (len / 16))) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ padOff 16) := fun j hj => by
      rw [eQ, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hcP.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [padOff]))).sub_right
        (VG.Proof.ChaCha20Poly1305.Arm.sub_off (State.addr P) (a := 16 * (len / 16) + j) (n := 1) (by lit_omega))).symm
    refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.padTail_ok hp i₄ (Q := P + BitVec.ofNat 32 (16 * (len / 16))) (t := len % 16)
      (by lit_omega) (by lit_omega) hQ (by rw [g₄ _ (by decide), r3₃]) hfitQ hsrc hdj) fun s₅ ⟨i₅, k₅, repr₅⟩ => ?_
    refine ⟨i₅, k₁₃.trans ((VG.Proof.ChaCha20Poly1305.Arm.kept_mac0 k₄).trans k₅), fun key msg hr => ?_⟩
    have m₄ := k₄.mem_eq
    have := repr₅ key _ (by rw [m₄, m₃]; exact repr₂ key msg hr)
    rw [m₄, m₃, VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [eQ]
        exact ((hcP.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by lit_omega))).sub_right
          (VG.Proof.ChaCha20Poly1305.Arm.sub_off (State.addr P) (a := 16 * (len / 16)) (by lit_omega))).symm) (by lit_omega), m₁, eQ] at this
    rw [show pad16 (bytesAt s.mem (State.addr P) len) = List.replicate (16 - len % 16) 0 by
      simp [pad16, hlen, h0], x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.Arm

/-!
# ChaCha20-Poly1305 on ARMv7: the other parts

The encryption, the lengths block, the arguments of `vg_poly1305_finalize_scratch` and
the tag, copying and comparing tags, and restoring the registers.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_and wp_orr wp_ldr wp_str op2_imm
  op2_reg op2_lsr op2_lsl saveMem restoreList_ok wp_ldrSp)
open VG.Proof.ChaCha20.Arm.Xor (stateAt_writeW_counter wp_eor)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem cryptA_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa (.block [.mov .r12 (.imm 1), .str .r12 .r7 (stOff + 48),
      .dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r10), .mov .r2 (.reg .r11),
      .mov .r3 (.reg .r7)]) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 48)) (1 : BitVec 32) ∧ s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ stOff ∧
      s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.dP s₀ ∧ s'.gpr .r2 = stackArg s₀ 1 ∧ s'.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧
      VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ stOff 64] s s' := by
  have o := hp.in_ctx (a := stOff + 48) (w := 4) (by simp [stOff])
  rw [← h.wr] at o
  have core : WP isa (.block [.mov .r12 (.imm 1), .str .r12 .r7 (stOff + 48),
      .dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r10), .mov .r2 (.reg .r11),
      .mov .r3 (.reg .r7)]) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 48)) (1 : BitVec 32) ∧ s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ stOff ∧
      s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.dP s₀ ∧ s'.gpr .r2 = stackArg s₀ 1 ∧ s'.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 48)) (by simp [stOff])
      (by rw [u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h]; exact hp.addr_cP_off (by simp [stOff])) (by rw [u₁.wr]; exact o)
      fun s₂ g₂ => ?_
    refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
      wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr,
        u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.regs.r10]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.regs.r11]
    · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨hm, h0, h1, h2, h3, hrd, hwr⟩, hg, hsp⟩ => ⟨hm, h0, h1, h2, h3, Kept.of hg hsp hrd hwr ?_⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (w := 32 / 8) (by simp [stOff]) (by simp [stOff]) (by simp [stOff]))

theorem hL (s₀ : State) : stackArg s₀ 1 = BitVec.ofNat 32 (VG.Proof.ChaCha20Poly1305.Arm.L s₀) := by simp [VG.Proof.ChaCha20Poly1305.Arm.L]

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The data encrypted (or decrypted) from block counter 1, with the ChaCha20
state for counter 0 at `ctx + stOff`. -/
theorem crypt_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s)
    (hst : stateAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀)) :
    WP isa crypt s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 (stOff + 64), VG.Proof.ChaCha20Poly1305.Arm.dR s₀] s s' ∧
      bytesAt s'.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = Spec.ChaCha20.encrypt (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 1 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) (bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀)) := by
  unfold crypt
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.cryptA_ok hp h) fun s₁ ⟨m₁, h0, h1, h2, h3, k₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by simp [stOff]) (by simp [stOff, savOff])
  have hw : Covers [⟨State.addr (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ stOff), 64⟩, ⟨State.addr (VG.Proof.ChaCha20Poly1305.Arm.dP s₀), VG.Proof.ChaCha20Poly1305.Arm.L s₀⟩, ⟨State.addr (VG.Proof.ChaCha20Poly1305.Arm.cP s₀), 320⟩]
      s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by rw [i₁.wr]; exact hp.ctx_wr, stOff, by rw [hp.addr_ptr (by simp [stOff])], by simp [stOff]⟩
    · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.dR s₀, by rw [i₁.wr]; exact hp.d_wr, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by rw [i₁.wr]; exact hp.ctx_wr, 0, by simp, by simp⟩
  refine WP.seq (VG.Proof.ChaCha20Poly1305.Arm.xor_call h0 h1 (by rw [h2]; exact VG.Proof.ChaCha20Poly1305.Arm.hL s₀) h3 (stackArg s₀ 1).isLt
    (by rw [hp.addr_ptr (by simp [stOff])]; exact hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [stOff])))
    (by rw [hp.addr_ptr (by simp [stOff]), ← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]
        exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (a := stOff) (n := 64) (b := 0) (m := 320) (by simp [stOff]) (by simp [stOff])
          (by lit_omega))
    (by rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact (hp.c_d.symm.sub_right (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by lit_omega))))
    (by rw [hp.ptr_toNat (by simp [stOff])]; have := hp.fit_c; simp [stOff]; omega)
    hp.fit_d (by have := hp.fit_c; omega)
    (by simpa using Covers.right hw) hw fun s₂ k₂ r1₂ data₂ => ?_)
  have hsub : ∀ r ∈ [⟨State.addr (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ stOff), 64⟩, ⟨State.addr (VG.Proof.ChaCha20Poly1305.Arm.dP s₀), VG.Proof.ChaCha20Poly1305.Arm.L s₀⟩, ⟨State.addr (VG.Proof.ChaCha20Poly1305.Arm.cP s₀), 320⟩],
      ∃ r' ∈ [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 (stOff + 64), VG.Proof.ChaCha20Poly1305.Arm.dR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 (stOff + 64), by simp, ?_⟩
      rw [hp.addr_ptr (by simp [stOff])]; exact VG.Proof.ChaCha20Poly1305.Arm.sub_sub s₀ (by lit_omega) (by simp [stOff]) (by simp [stOff])
    · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.dR s₀, by simp, fun _ h => h⟩
    · refine ⟨VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 (stOff + 64), by simp, ?_⟩
      rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact VG.Proof.ChaCha20Poly1305.Arm.sub_sub s₀ (Nat.le_refl _) (by simp [stOff]) (by simp [stOff])
  have k₁₂ : VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 (stOff + 64), VG.Proof.ChaCha20Poly1305.Arm.dR s₀] s s₂ :=
    (k₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 (stOff + 64), by simp, VG.Proof.ChaCha20Poly1305.Arm.sub_sub s₀ (by lit_omega) (by simp [stOff]) (by simp [stOff])⟩).trans
    (k₂.sub hsub)
  have i₂ := h.step k₁₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.ChaCha20Poly1305.Arm.sub_inv s₀ (by simp [stOff])
      · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [stOff, savOff]) (by simp [savOff]) (by simp [stOff])
      · exact hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [savOff])))
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.anchor_ok i₂ r1₂) fun s₃ ⟨i₃, k₃⟩ => ⟨i₃, k₁₂.trans (k₃.sub fun _ hr => absurd hr List.not_mem_nil), ?_⟩
  have d₁ : bytesAt s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) :=
    VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame k₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [stOff]))).symm)
      (by simp only [VG.Proof.ChaCha20Poly1305.Arm.L]; have := (stackArg s₀ 1).isLt; omega)
  have st₁ : stateAt s₁.mem (State.addr (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ stOff)) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 1 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) := by
    rw [m₁, hp.addr_ptr (by simp [stOff]), show VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (stOff + 48) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff + BitVec.ofNat 64 48 from
      (VG.Proof.ChaCha20Poly1305.Arm.off_off _ _ _).symm, stateAt_writeW_counter, hst, show (1 : BitVec 32) = 1 from rfl, VG.Proof.ChaCha20Poly1305.Arm.set12_initState]
  rw [k₃.mem_eq, show Spec.ChaCha20.bytesAt = bytesAt from rfl] at *
  rw [data₂, st₁, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## The lengths block -/

theorem bytesAt_leBytes_32 (m : Mem) (p : Addr) : bytesAt m p 4 = leBytes 4 (m.readW p 32).toNat := by
  rw [VG.Proof.Poly1305.bytesAt_leBytes]; simp [Mem.readW]

/-- A 32-bit length, zero-extended to 64 bits. -/
theorem bytesAt_len {m : Mem} {p : Addr} {x : Nat} (hx : x < 2 ^ 32) (h0 : (m.readW p 32).toNat = x)
    (h1 : m.readW (p + BitVec.ofNat 64 4) 32 = 0) : bytesAt m p 8 = leBytes 8 x := by
  rw [show 8 = 4 + 4 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.ChaCha20Poly1305.Arm.bytesAt_leBytes_32, VG.Proof.ChaCha20Poly1305.Arm.bytesAt_leBytes_32, h0, h1,
    VG.Proof.Poly1305.leBytes_add, Nat.div_eq_of_lt (by lit_omega)]
  rfl

theorem lengthsA_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa (.block [.str .r9 .r7 lenOff, .mov .r12 (.imm 0), .str .r12 .r7 (lenOff + 4),
      .str .r11 .r7 (lenOff + 8), .str .r12 .r7 (lenOff + 12),
      .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 lenOff)), .mov .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ lenOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ lenOff 16] s s' ∧
      bytesAt s'.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) lenOff) 16 = leBytes 8 (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) ++ leBytes 8 (VG.Proof.ChaCha20Poly1305.Arm.L s₀) := by
  have o : ∀ d, d < 4 → InRegions s.wr (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * d)) 4 := fun d hd => by
    rw [h.wr]; exact hp.in_ctx (by simp [lenOff]; omega)
  have ea : ∀ d, d < 4 → State.addr (VG.Proof.ChaCha20Poly1305.Arm.cP s₀ + BitVec.ofNat 32 (lenOff + 4 * d)) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * d) :=
    fun d hd => hp.addr_cP_off (by simp [lenOff]; omega)
  have core : WP isa (.block [.str .r9 .r7 lenOff, .mov .r12 (.imm 0), .str .r12 .r7 (lenOff + 4),
      .str .r11 .r7 (lenOff + 8), .str .r12 .r7 (lenOff + 12),
      .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 lenOff)), .mov .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ lenOff ∧ s'.gpr .r2 = BitVec.ofNat 32 1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = (((s.mem.writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 0)) (s₀.gpr .r3)).writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 1))
        (0 : BitVec 32)).writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 2)) (stackArg s₀ 1)).writeW
        (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 3)) (0 : BitVec 32) := by
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 0)) (by simp [lenOff]) (by rw [VG.Proof.ChaCha20Poly1305.Arm.hr7 h]; exact ea 0 (by lit_omega))
      (o 0 (by lit_omega)) fun s₁ g₁ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
    have h7 : s₂.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₂.other _ (by decide), g₁.gpr, VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 1)) (by simp [lenOff]) (by rw [h7]; exact ea 1 (by lit_omega))
      (by rw [u₂.wr, g₁.wr]; exact o 1 (by lit_omega)) fun s₃ g₃ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 2)) (by simp [lenOff]) (by rw [g₃.gpr, h7]; exact ea 2 (by lit_omega))
      (by rw [g₃.wr, u₂.wr, g₁.wr]; exact o 2 (by lit_omega)) fun s₄ g₄ => ?_
    refine wp_str (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 3)) (by simp [lenOff])
      (by rw [g₄.gpr, g₃.gpr, h7]; exact ea 3 (by lit_omega))
      (by rw [g₄.wr, g₃.wr, u₂.wr, g₁.wr]; exact o 3 (by lit_omega)) fun s₅ g₅ => ?_
    refine wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), u₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, h7]
    · rw [u₇.gpr]; rfl
    · rw [u₇.rd, u₆.rd, g₅.rd, g₄.rd, g₃.rd, u₂.rd, g₁.rd]
    · rw [u₇.wr, u₆.wr, g₅.wr, g₄.wr, g₃.wr, u₂.wr, g₁.wr]
    · have x12 : s₂.gpr .r12 = 0 := u₂.gpr
      rw [u₇.mem, u₆.mem, g₅.mem, g₄.mem, g₃.mem, u₂.mem, g₁.mem, g₄.gpr, g₃.gpr, x12, u₂.other _ (by decide),
        g₁.gpr, h.regs.r11, h.regs.r9]
  refine WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h1, h2, Kept.of hg hsp hrd hwr ?_, ?_⟩
  · rw [hm]
    have c : ∀ d, d < 4 → (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ lenOff 16).Contains (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * d)) (32 / 8) :=
      fun d hd => VG.Proof.ChaCha20Poly1305.Arm.contains_sub s₀ (by lit_omega) (by lit_omega) (by simp [lenOff])
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 1 (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 2 (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 3 (by lit_omega))
  · have r : ∀ d, d < 4 → ∀ e, e < 4 → d ≠ e → ∀ (m : Mem) (v : BitVec 32),
        (m.writeW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * e)) v).readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * d)) 32 =
          m.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * d)) 32 :=
      fun d hd e he hde m v => VG.Proof.ChaCha20Poly1305.Arm.readW_off m _ v (by simp [lenOff]; omega) (by simp [lenOff]; omega) (by lit_omega)
    rw [show (16 : Nat) = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, hm]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine VG.Proof.ChaCha20Poly1305.Arm.bytesAt_len (s₀.gpr .r3).isLt ?_ ?_
      · rw [show VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) lenOff = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (lenOff + 4 * 0) from rfl,
          r 0 (by lit_omega) 3 (by lit_omega) (by lit_omega), r 0 (by lit_omega) 2 (by lit_omega) (by lit_omega),
          r 0 (by lit_omega) 1 (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
      · rw [VG.Proof.ChaCha20Poly1305.Arm.off_add, show lenOff + 4 = lenOff + 4 * 1 from rfl, r 1 (by lit_omega) 3 (by lit_omega) (by lit_omega),
          r 1 (by lit_omega) 2 (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
    · rw [VG.Proof.ChaCha20Poly1305.Arm.off_add]
      refine VG.Proof.ChaCha20Poly1305.Arm.bytesAt_len (stackArg s₀ 1).isLt ?_ ?_
      · rw [show lenOff + 8 = lenOff + 4 * 2 from rfl, r 2 (by lit_omega) 3 (by lit_omega) (by lit_omega),
          Mem.readW_writeW_self32]
      · rw [VG.Proof.ChaCha20Poly1305.Arm.off_add, show lenOff + 8 + 4 = lenOff + 4 * 3 from rfl, Mem.readW_writeW_self32]

theorem lengths_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa lengths s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ lenOff 16] s s' ∧
      ∀ key msg, Repr s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg →
        Repr s'.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key (msg ++ (leBytes 8 (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) ++ leBytes 8 (VG.Proof.ChaCha20Poly1305.Arm.L s₀))) := by
  unfold lengths
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.lengthsA_ok hp h) fun s₁ ⟨h1, h2, k₁, len₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by simp [lenOff]) (by simp [lenOff, savOff])
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.absorb_ok hp i₁ (n := 1) h1 h2 (by lit_omega)
    (by rw [hp.addr_ptr (by simp [lenOff])]
        exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (a := 0) (n := 128) (by simp [lenOff]) (by lit_omega) (by simp [lenOff]))
    (by rw [hp.ptr_toNat (by simp [lenOff])]; have := hp.fit_c; simp [lenOff]; omega)
    (by rw [hp.addr_ptr (by simp [lenOff])]
        exact Covers.right (VG.Proof.ChaCha20Poly1305.Arm.covers1 hp rfl (a := lenOff) (n := 16 * 1) (by simp [lenOff]))))
    fun s₂ ⟨i₂, k₂, repr₂⟩ => ⟨i₂, (k₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (k₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩), fun key msg hr => ?_⟩
  have hr₁ : Repr s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg := Repr.frame k₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [lenOff]) (by lit_omega) (by simp [lenOff])) hr
  have := repr₂ key msg hr₁
  rwa [hp.addr_ptr (by simp [lenOff]), show 16 * 1 = 16 from rfl, len₁] at this

/-! ## The length of the message authenticated -/

theorem length_pad (x : List Byte) : (x ++ Spec.ChaCha20Poly1305.pad16 x).length = 16 * ((x.length + 15) / 16) := by
  simp only [List.length_append, Spec.ChaCha20Poly1305.pad16]
  split
  · simp; omega
  · simp; omega

theorem length_macData (a c : List Byte) :
    (Spec.ChaCha20Poly1305.macData a c).length = 16 * ((a.length + 15) / 16 + (c.length + 15) / 16 + 1) := by
  have ha := VG.Proof.ChaCha20Poly1305.Arm.length_pad a
  have hc := VG.Proof.ChaCha20Poly1305.Arm.length_pad c
  simp only [List.length_append] at ha hc
  simp only [Spec.ChaCha20Poly1305.macData, List.length_append, leBytes, List.length_map, List.length_range]
  omega

/-- `⌈x / 16⌉`, as `ceil16` computes it. -/
theorem ceil16_val (x : BitVec 32) :
    x >>> 4 + ((x &&& 15) + 15) >>> 4 = BitVec.ofNat 32 ((x.toNat + 15) / 16) := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  have e : (x &&& 15).toNat = x.toNat % 16 := by
    rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 32).toNat = 15 from rfl]
  omega

/-- `r3:r2 = 16 n`, from `n` in `r2`. -/
theorem count_val (n : BitVec 32) : n >>> 28 ++ n <<< 4 = BitVec.ofNat 64 (16 * n.toNat) := by
  have hn := n.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    ← Nat.shiftLeft_add_eq_or_of_lt (by exact Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem finArgs_all {out : Instr} (hkeep : (preserved.all fun r => dstOf out != some r) = true) :
    ((finalizeArgs out).all fun i => preserved.all fun r => dstOf i != some r) = true := by
  simp only [finalizeArgs, ceil16, List.cons_append, List.nil_append, List.all_cons, List.all_nil, hkeep,
    Bool.and_true, Bool.true_and]
  decide

/-- The arguments of `vg_poly1305_finalize_scratch`, with `out` set to `O`
by the instruction `out`. -/
theorem finArgs_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {out : Instr} {O : BitVec 32}
    (hkeep : (preserved.all fun r => dstOf out != some r) = true)
    (hout : ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.mem = s.mem → t.sp = s.sp →
      t.rd = s.rd → t.gpr .r7 = s.gpr .r7 → (∀ t', Upd t t' .r1 O → WP isa (.block rest) t' Q) →
      WP isa (.block (out :: rest)) t Q) :
    WP isa (.block (finalizeArgs out)) s fun s' => VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' ∧ s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧
      s'.gpr .r1 = O ∧ s'.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ scrOff ∧
      Proof.Poly1305.countArm s' = BitVec.ofNat 64 (16 * ((VG.Proof.ChaCha20Poly1305.Arm.AL s₀ + 15) / 16 + (VG.Proof.ChaCha20Poly1305.Arm.L s₀ + 15) / 16 + 1)) := by
  have core : WP isa (.block (finalizeArgs out)) s fun s' => s'.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ ∧
      s'.gpr .r1 = O ∧ s'.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ scrOff ∧
      s'.gpr .r3 ++ s'.gpr .r2 = BitVec.ofNat 64 (16 * ((VG.Proof.ChaCha20Poly1305.Arm.AL s₀ + 15) / 16 + (VG.Proof.ChaCha20Poly1305.Arm.L s₀ + 15) / 16 + 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
    unfold finalizeArgs ceil16
    simp only [List.cons_append, List.nil_append]
    refine wp_mov (op2_lsr (by decide)) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ =>
      wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_lsr (by decide)) fun s₄ u₄ =>
      wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_and (op2_imm (by decide)) fun s₆ u₆ =>
      wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_add (op2_lsr (by decide)) fun s₈ u₈ =>
      wp_add (op2_reg _ _) fun s₉ u₉ => wp_add (op2_imm (by decide)) fun s₁₀ u₁₀ =>
      wp_mov (op2_lsr (by decide)) fun s₁₁ u₁₁ => wp_mov (op2_lsl (by decide)) fun s₁₂ u₁₂ =>
      wp_mov (op2_reg _ _) fun s₁₃ u₁₃ => ?_
    refine hout s₁₃ _ _
      (by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
        u₂.mem, u₁.mem])
      (by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp,
        u₂.sp, u₁.sp])
      (by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd,
        u₂.rd, u₁.rd])
      (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide),
        u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
      fun s₁₄ u₁₄ => wp_add (op2_imm (by decide)) fun s₁₅ u₁₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide),
        u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
    · rw [u₁₅.other _ (by decide), u₁₄.gpr]
    · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
        u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
    · -- `r2` = ⌈aad_len / 16⌉ + ⌈len / 16⌉ + 1, then shifted into `r3:r2`.
      have cA : s₄.gpr .r2 = BitVec.ofNat 32 ((VG.Proof.ChaCha20Poly1305.Arm.AL s₀ + 15) / 16) := by
        rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), h.regs.r9, VG.Proof.ChaCha20Poly1305.Arm.ceil16_val]
      have cL : s₈.gpr .r0 = BitVec.ofNat 32 ((VG.Proof.ChaCha20Poly1305.Arm.L s₀ + 15) / 16) := by
        rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₇.gpr, u₆.gpr,
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.regs.r11, VG.Proof.ChaCha20Poly1305.Arm.ceil16_val]
      have cN : s₁₀.gpr .r2 = BitVec.ofNat 32 ((VG.Proof.ChaCha20Poly1305.Arm.AL s₀ + 15) / 16 + (VG.Proof.ChaCha20Poly1305.Arm.L s₀ + 15) / 16 + 1) := by
        rw [u₁₀.gpr, u₉.gpr, cL, u₈.other .r2 (by decide), u₇.other .r2 (by decide),
          u₆.other .r2 (by decide), u₅.other .r2 (by decide), cA]
        rw [← BitVec.ofNat_add, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
      have hN : ((VG.Proof.ChaCha20Poly1305.Arm.AL s₀ + 15) / 16 + (VG.Proof.ChaCha20Poly1305.Arm.L s₀ + 15) / 16 + 1) < 2 ^ 32 := by
        have := (s₀.gpr .r3).isLt; have := (stackArg s₀ 1).isLt; simp only [VG.Proof.ChaCha20Poly1305.Arm.AL, VG.Proof.ChaCha20Poly1305.Arm.L]; omega
      have c3 : s₁₅.gpr .r3 = s₁₀.gpr .r2 >>> 28 := by
        rw [u₁₅.other .r3 (by decide), u₁₄.other .r3 (by decide), u₁₃.other .r3 (by decide),
          u₁₂.other .r3 (by decide), u₁₁.gpr]
      have c2 : s₁₅.gpr .r2 = s₁₀.gpr .r2 <<< 4 := by
        rw [u₁₅.other .r2 (by decide), u₁₄.other .r2 (by decide), u₁₃.other .r2 (by decide), u₁₂.gpr,
          u₁₁.other .r2 (by decide)]
      rw [c3, c2, cN, VG.Proof.ChaCha20Poly1305.Arm.count_val, VG.Proof.ChaCha20Poly1305.Arm.toNat32 hN]
    · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd,
        u₂.rd, u₁.rd]
    · rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr,
        u₂.wr, u₁.wr]
    · rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem,
        u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (WP.kept core (VG.Proof.ChaCha20Poly1305.Arm.finArgs_all hkeep))
    fun s' ⟨⟨h0, h1, h12, hc, hrd, hwr, hm⟩, hg, hsp⟩ => ?_
  have hk : VG.Proof.ChaCha20Poly1305.Arm.Kept [] s s' := Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)
  exact ⟨h.step0 hk, hk, h0, h1, h12, hc⟩

/-- The stack arguments are unchanged while the invariant holds. -/
theorem Inv.arg {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {i : Nat} (hi : i < 4) :
    s.mem.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i :=
  hp.arg_eq (fun a ha => h.frame a fun r hr hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_arg a hc ha
    · exact hp.d_arg a hc ha
    · exact VG.Proof.ChaCha20Poly1305.Arm.bel_arg s₀ a hc ha) hi

/-- `seal`'s `out`: `tag`, from the stack. -/
theorem out_seal {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.mem = s.mem → t.sp = s.sp →
      t.rd = s.rd → t.gpr .r7 = s.gpr .r7 → (∀ t', Upd t t' .r1 (VG.Proof.ChaCha20Poly1305.Arm.tP s₀) → WP isa (.block rest) t' Q) →
      WP isa (.block (.ldrSp .r1 8 :: rest)) t Q := by
  intro t rest Q tm tsp trd _ k
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) (by rw [tsp, h.sp]; rfl)
    (hp.arg_in (by decide) (trd.trans h.rd)) fun t' u => k t' ⟨u.gpr.trans ?_, u.other, u.mem, u.rd, u.wr, u.sp⟩
  rw [tm]; exact h.arg hp (by decide)

/-- `open`'s `out`: the tag computed, in the context. -/
theorem out_open {s₀ s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.mem = s.mem → t.sp = s.sp →
      t.rd = s.rd → t.gpr .r7 = s.gpr .r7 → (∀ t', Upd t t' .r1 (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ tagOff) → WP isa (.block rest) t' Q) →
      WP isa (.block (.dp .add .r1 .r7 (.imm (BitVec.ofNat 32 tagOff)) :: rest)) t Q := by
  intro t rest Q _ _ _ t7 k
  exact wp_add (op2_imm (by decide)) fun t' u => k t' ⟨by rw [u.gpr, t7, VG.Proof.ChaCha20Poly1305.Arm.hr7 h], u.other, u.mem, u.rd,
    u.wr, u.sp⟩

/-! ## The tag -/

/-- Where `out` may be: 16 writable bytes disjoint from the Poly1305 state,
the working space of `vg_poly1305_finalize_scratch`, the saved registers, the
data and the stack below. -/
structure OutOk (s₀ : State) (O : BitVec 32) : Prop where
  fit : O.toNat + 16 ≤ 2 ^ 32
  dP : (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128).Disjoint ⟨State.addr O, 16⟩
  dS : (⟨State.addr O, 16⟩ : Region).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ scrOff 128)
  dB : (VG.Proof.ChaCha20Poly1305.Arm.belR s₀).Disjoint ⟨State.addr O, 16⟩
  dSv : (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ savOff 36).Disjoint ⟨State.addr O, 16⟩
  dD : (VG.Proof.ChaCha20Poly1305.Arm.dR s₀).Disjoint ⟨State.addr O, 16⟩
  w : ∃ r ∈ s₀.wr, ∃ k, State.addr O = r.base + BitVec.ofNat 64 k ∧ k + 16 ≤ r.len

/-- `open`'s tag computed. -/
theorem outOk_tag {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.OutOk s₀ (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ tagOff) := by
  have et := hp.addr_ptr (k := tagOff) (by simp [tagOff])
  refine ⟨by rw [hp.ptr_toNat (by simp [tagOff])]; have := hp.fit_c; simp [tagOff]; omega, ?_, ?_, ?_, ?_, ?_,
    ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, hp.ctx_wr, tagOff, et, by simp [tagOff]⟩⟩ <;> rw [et]
  · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [tagOff]) (by lit_omega) (by simp [tagOff])
  · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [tagOff, scrOff]) (by simp [tagOff]) (by simp [scrOff])
  · exact hp.b_c.sub_right (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [tagOff]))
  · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [savOff, tagOff]) (by simp [savOff]) (by simp [tagOff])
  · exact (hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [tagOff]))).symm

/-- `seal`'s `tag`. -/
theorem outOk_tP {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre true s₀) : VG.Proof.ChaCha20Poly1305.Arm.OutOk s₀ (VG.Proof.ChaCha20Poly1305.Arm.tP s₀) :=
  ⟨hp.fit_t, hp.c_t.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by lit_omega)),
    (hp.c_t.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [scrOff]))).symm, hp.b_t,
    hp.c_t.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [savOff])), hp.d_t,
    ⟨VG.Proof.ChaCha20Poly1305.Arm.tR s₀, hp.t_wr, 0, by simp, by simp⟩⟩

theorem fin_args {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {O : BitVec 32} (ho : VG.Proof.ChaCha20Poly1305.Arm.OutOk s₀ O)
    (h0 : s.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀) (h1 : s.gpr .r1 = O) (h12 : s.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ scrOff) :
    VG.Proof.ChaCha20Poly1305.Arm.FinArgs s (VG.Proof.ChaCha20Poly1305.Arm.cP s₀) O (VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ scrOff) := by
  have es := hp.addr_ptr (k := scrOff) (by simp [scrOff])
  have hsp := h.sp
  have bc : ∀ k n, k + n ≤ 632 → (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) := fun k n hk => by
    rw [hsp]; exact hp.b_c.sub_right (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ hk)
  exact ⟨h0, h1, h12, by rw [hsp]; exact hp.sp8,
    by rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact ho.dP,
    by rw [es, ← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [scrOff]) (by lit_omega) (by simp [scrOff]),
    by rw [es]; exact ho.dS,
    by rw [← VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact bc 0 128 (by lit_omega),
    by rw [hsp]; exact ho.dB,
    by rw [es]; exact bc _ _ (by simp [scrOff]),
    by have := hp.fit_c; omega,
    ho.fit,
    by rw [hp.ptr_toNat (by simp [scrOff])]; have := hp.fit_c; simp [scrOff]; omega,
    Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 0, by simp, by simp⟩
      · obtain ⟨r', hr', k, hk, hl⟩ := ho.w
        exact ⟨r', by rw [h.wr]; exact hr', k, hk, hl⟩
      · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, scrOff, es, by simp [scrOff]⟩⟩

theorem fin_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {O : BitVec 32} (ho : VG.Proof.ChaCha20Poly1305.Arm.OutOk s₀ O)
    (h0 : s.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀) (h1 : s.gpr .r1 = O) (h12 : s.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ scrOff) :
    WP isa finalize s fun s' =>
      VG.Proof.ChaCha20Poly1305.Arm.Kept [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128, ⟨State.addr O, 16⟩, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ scrOff 128, VG.Proof.ChaCha20Poly1305.Arm.belR s₀] s s' ∧ VG.Proof.ChaCha20Poly1305.Arm.Regs s₀ s' ∧
      VG.Proof.ChaCha20Poly1305.Arm.Saved s₀ s'.mem ∧
      ∀ key msg, Repr s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg → Proof.Poly1305.countArm s = BitVec.ofNat 64 msg.length →
        bytesAt s'.mem (State.addr O) 16 = mac key msg := by
  have es := hp.addr_ptr (k := scrOff) (by simp [scrOff])
  have hsp := h.sp
  refine VG.Proof.ChaCha20Poly1305.Arm.finalize_ok (VG.Proof.ChaCha20Poly1305.Arm.fin_args hp h ho h0 h1 h12) fun s' hk htag => ?_
  rw [es, ← VG.Proof.ChaCha20Poly1305.Arm.sub_zero, hsp] at hk
  refine ⟨hk, h.regs.kept hk.cs, h.saved.frame hk.frame fun r hr => ?_, htag⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [savOff]) (by simp [savOff]) (by lit_omega)
  · exact ho.dSv
  · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [savOff, scrOff]) (by simp [savOff]) (by simp [scrOff])
  · exact (hp.b_c.sub_right (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [savOff]))).symm

/-! ## Restoring the registers -/

theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem preserved_eq : preserved = saved.map Prod.fst := rfl

/-- Restoring `r4`–`r11` and `lr` from `ctx[464, 500)`, through `r12`. -/
theorem restore_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {s : State} (h7 : s.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀) (hsv : VG.Proof.ChaCha20Poly1305.Arm.Saved s₀ s.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ preserved → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold restore
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₁.gpr, h7]
  rw [← List.append_nil (saved.map _)]
  refine VG.Proof.ChaCha20Poly1305.Arm.restoreList_ok (b := .r12) saved s₁ _ (by decide) (fun p hp' => ?_)
    fun s' ho hr hm hrd' hwr' hsp => WP.block_nil ⟨fun r hr' => ?_, fun r hr' h12' => ?_, ?_, ?_, ?_, ?_⟩
  · have hb := VG.Proof.ChaCha20Poly1305.Arm.saved_bound p hp'
    simp only [savOff] at hb
    have := hp.fit_c
    simp only [VG.Proof.ChaCha20Poly1305.Arm.cP] at this
    refine ⟨fun e => by simp [saved] at hp'; rcases hp' with h | h | h | h | h | h | h | h | h <;>
      simp_all, by omega, by rw [h12]; simp only [VG.Proof.ChaCha20Poly1305.Arm.cP]; omega, ?_⟩
    rw [h12, u₁.rd, u₁.wr, hrd, hwr]; exact hp.in_ctx' (by lit_omega)
  · rw [VG.Proof.ChaCha20Poly1305.Arm.preserved_eq] at hr'
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
    rw [ho p hp', h12, u₁.mem]; exact hsv p hp'
  · rw [hr r (by rwa [← VG.Proof.ChaCha20Poly1305.Arm.preserved_eq]), u₁.other r h12']
  · rw [hm, u₁.mem]
  · rw [hsp, u₁.sp]
  · rw [hrd', u₁.rd]
  · rw [hwr', u₁.wr]

/-! ## Comparing the tags -/

theorem compare_eq : compare =
    [.ldrSp .r3 8, .ldr .r0 .r7 448, .ldr .r1 .r3 0, .dp .eor .r0 .r0 (.reg .r1),
     .ldr .r1 .r7 452, .ldr .r2 .r3 4, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
     .ldr .r1 .r7 456, .ldr .r2 .r3 8, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
     .ldr .r1 .r7 460, .ldr .r2 .r3 12, .dp .eor .r1 .r1 (.reg .r2), .dp .orr .r0 .r0 (.reg .r1),
     .mov .r1 (.imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1),
     .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (.imm 1), .dp .sub .r0 .r1 (.reg .r0)] := rfl

/-- `(x | -x) >> 31` is 0 if `x = 0` and 1 otherwise. -/
theorem nz_bit (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    have hneg : (0 - x).toNat = 2 ^ 32 - x.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]; omega
    have h1 : 2 ^ 31 ≤ (x ||| (0 - x)).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 31) with h2 | h2
      · exact Nat.le_trans (by lit_omega) (Nat.right_le_or (n := x.toNat))
      · exact Nat.le_trans h2 Nat.left_le_or
    have h2 := (x ||| (0 - x)).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega

theorem sel_eq {x : BitVec 32} {p : Prop} [Decidable p] (h : x = 0 ↔ p) :
    ((1 : BitVec 32) - if x = 0 then 0 else 1) = if p then 1 else 0 := by
  by_cases hp : p
  · have hx : x = 0 := h.mpr hp
    simp only [hx, hp, ↓reduceIte]
    decide
  · have hx : ¬ x = 0 := fun e => hp (h.mp e)
    simp only [hx, hp, ↓reduceIte]
    decide

/-- Words equal are bytes equal, and conversely. -/
theorem words_iff_bytes (m : Mem) (p q : Addr) :
    (∀ k < 4, m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (q + BitVec.ofNat 64 (4 * k)) 32) ↔
      bytesAt m p 16 = bytesAt m q 16 := by
  constructor
  · intro h; exact VG.Proof.ChaCha20Poly1305.Arm.bytes_of_words (n := 4) h
  · intro h k hk
    have hb : ∀ i < 16, m (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := fun i hi => by
      have := congrArg (fun l => l.getD i 0) h
      simpa [bytesAt, hi] using this
    rw [readW32, readW32]
    have e : ∀ (a : Addr) (j : Nat), a + BitVec.ofNat 64 (4 * k) + (BitVec.ofNat 64 j) =
        a + BitVec.ofNat 64 (4 * k + j) := fun a j => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have e3 := e p 3; have e2 := e p 2; have e1 := e p 1
    have f3 := e q 3; have f2 := e q 2; have f1 := e q 1
    simp only [show (3 : Addr) = BitVec.ofNat 64 3 from rfl, show (2 : Addr) = BitVec.ofNat 64 2 from rfl,
      show (1 : Addr) = BitVec.ofNat 64 1 from rfl, e3, e2, e1, f3, f2, f1]
    rw [hb _ (by lit_omega), hb _ (by lit_omega), hb _ (by lit_omega), hb _ (by lit_omega)]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (c t : Addr) :
    ((m.readW (VG.Proof.ChaCha20Poly1305.Arm.off c 448) 32 ^^^ m.readW (VG.Proof.ChaCha20Poly1305.Arm.off t 0) 32) |||
      (m.readW (VG.Proof.ChaCha20Poly1305.Arm.off c 452) 32 ^^^ m.readW (VG.Proof.ChaCha20Poly1305.Arm.off t 4) 32) |||
      (m.readW (VG.Proof.ChaCha20Poly1305.Arm.off c 456) 32 ^^^ m.readW (VG.Proof.ChaCha20Poly1305.Arm.off t 8) 32) |||
      (m.readW (VG.Proof.ChaCha20Poly1305.Arm.off c 460) 32 ^^^ m.readW (VG.Proof.ChaCha20Poly1305.Arm.off t 12) 32)) = 0#32 ↔
      bytesAt m (VG.Proof.ChaCha20Poly1305.Arm.off c tagOff) 16 = bytesAt m t 16 := by
  rw [← VG.Proof.ChaCha20Poly1305.Arm.words_iff_bytes, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff,
    BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff]
  simp only [VG.Proof.ChaCha20Poly1305.Arm.off_add]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    exact ⟨⟨⟨h 0 (by lit_omega), h 1 (by lit_omega)⟩, h 2 (by lit_omega)⟩, h 3 (by lit_omega)⟩

/-- The tags compared: the one computed, at `ctx + 448`, and `tag`, whose
pointer is loaded from the stack. -/
theorem compare_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre false s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) :
    WP isa (.block compare) s fun s' =>
      s'.gpr .r0 = (if bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) tagOff) 16 = bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 16 then 1 else 0) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have i : ∀ d, d + 4 ≤ 632 → InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) d) 4 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.in_ctx' hd
  have it : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) d) 4 := fun d hd =>
    ⟨VG.Proof.ChaCha20Poly1305.Arm.tR s₀, by rw [h.rd]; exact List.mem_append_left _ hp.t_rd, Offset.contains_base _ hd (by omega)⟩
  have ea : ∀ d, d < 632 → ∀ t : State, t.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ →
      State.addr (t.gpr .r7 + BitVec.ofNat 32 d) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) d := fun d hd t ht => by
    rw [ht]; exact hp.addr_cP_off hd
  have et : ∀ d, d < 16 → ∀ t : State, t.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀ →
      State.addr (t.gpr .r3 + BitVec.ofNat 32 d) = VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) d := fun d hd t ht => by
    rw [ht]; exact hp.addr_tP_off hd
  let x : BitVec 32 := (s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) 448) 32 ^^^ s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 0) 32) |||
      (s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) 452) 32 ^^^ s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 4) 32) |||
      (s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) 456) 32 ^^^ s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 8) 32) |||
      (s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) 460) 32 ^^^ s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 12) 32)
  have core : WP isa (.block compare) s fun s' =>
      s'.gpr .r0 = 1 - (x ||| (0 - x)) >>> 31 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.compare_eq]
    refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) (by rw [h.sp]; rfl) (hp.arg_in (by decide) h.rd)
      fun s₀' u₀ => ?_
    have r3₀ : s₀'.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀ := by rw [u₀.gpr]; exact h.arg hp (by decide)
    have r7₀ : s₀'.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₀.other _ (by decide), VG.Proof.ChaCha20Poly1305.Arm.hr7 h]
    refine wp_ldr (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) 448) (by decide) (ea 448 (by lit_omega) s₀' r7₀)
      (by rw [u₀.rd, u₀.wr]; exact i 448 (by lit_omega)) fun s₁ u₁ => ?_
    have r7₁ : s₁.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₁.other _ (by decide), r7₀]
    have r3₁ : s₁.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀ := by rw [u₁.other _ (by decide), r3₀]
    refine wp_ldr (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 0) (by decide) (et 0 (by lit_omega) s₁ r3₁)
      (by rw [u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact it 0 (by lit_omega)) fun s₂ u₂ => ?_
    have r7₂ : s₂.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₂.other _ (by decide), r7₁]
    have r3₂ : s₂.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀ := by rw [u₂.other _ (by decide), r3₁]
    refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
    have r7₃ : s₃.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ := by rw [u₃.other _ (by decide), r7₂]
    have r3₃ : s₃.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀ := by rw [u₃.other _ (by decide), r3₂]
    have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem, u₀.mem]
    have x₃ : s₃.gpr .r0 = s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) 448) 32 ^^^ s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 0) 32 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, u₀.mem]
    -- One more pair of words: `r0 |= [r7 + a] ^ [r3 + b]`.
    have step : ∀ (a b : Nat), a + 4 ≤ 632 → b + 4 ≤ 16 → ∀ (t : State) (rest : List Instr)
        (Q : State → Prop), t.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ → t.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀ → t.mem = s.mem → t.rd = s.rd →
        t.wr = s.wr →
        (∀ t', t'.gpr .r0 = t.gpr .r0 ||| (s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) 32 ^^^ s.mem.readW (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) b) 32) →
          t'.gpr .r7 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀ → t'.gpr .r3 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀ → t'.mem = s.mem → t'.rd = s.rd → t'.wr = s.wr →
          WP isa (.block rest) t' Q) →
        WP isa (.block (.ldr .r1 .r7 a :: .ldr .r2 .r3 b :: .dp .eor .r1 .r1 (.reg .r2) ::
          .dp .orr .r0 .r0 (.reg .r1) :: rest)) t Q := by
      intro a b ha hb t rest Q t7 t3 tm trd twr k
      refine wp_ldr (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) (by lit_omega) (ea a (by lit_omega) t t7)
        (by rw [trd, twr]; exact i a ha) fun t₁ v₁ => ?_
      refine wp_ldr (a := VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) b) (by lit_omega) (et b (by lit_omega) t₁ (by rw [v₁.other _ (by decide), t3]))
        (by rw [v₁.rd, v₁.wr, trd, twr]; exact it b hb) fun t₂ v₂ => ?_
      refine wp_eor (op2_reg _ _) fun t₃ v₃ => wp_orr (op2_reg _ _) fun t₄ v₄ => k t₄ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [v₄.gpr, v₃.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
          v₂.other _ (by decide), v₁.gpr, v₂.gpr, v₁.mem, tm]
      · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), t7]
      · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), t3]
      · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, tm]
      · rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, trd]
      · rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, twr]
    refine step 452 4 (by lit_omega) (by lit_omega) s₃ _ _ r7₃ r3₃ m₃ (by rw [u₃.rd, u₂.rd, u₁.rd, u₀.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]) fun t₁ w₁ r7t₁ r3t₁ mt₁ rdt₁ wrt₁ => ?_
    refine step 456 8 (by lit_omega) (by lit_omega) t₁ _ _ r7t₁ r3t₁ mt₁ rdt₁ wrt₁
      fun t₂ w₂ r7t₂ r3t₂ mt₂ rdt₂ wrt₂ => ?_
    refine step 460 12 (by lit_omega) (by lit_omega) t₂ _ _ r7t₂ r3t₂ mt₂ rdt₂ wrt₂
      fun t₃ w₃ _ _ mt₃ rdt₃ wrt₃ => ?_
    refine wp_mov (op2_imm (by decide)) fun t₄ v₄ => wp_sub (op2_reg _ _) fun t₅ v₅ =>
      wp_orr (op2_reg _ _) fun t₆ v₆ => wp_mov (op2_lsr (by decide)) fun t₇ v₇ =>
      wp_mov (op2_imm (by decide)) fun t₈ v₈ => wp_sub (op2_reg _ _) fun t₉ v₉ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
    · have hx : t₃.gpr .r0 = x := by rw [w₃, w₂, w₁, x₃]
      rw [v₉.gpr, v₈.gpr, v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.gpr, v₅.other _ (by decide), v₄.gpr,
        v₄.other _ (by decide), hx]
      rfl
    · rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, mt₃]
    · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, rdt₃]
    · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, wrt₃]
  refine WP.mono (WP.kept core (by simp [VG.Proof.ChaCha20Poly1305.Arm.compare_eq, dstOf, preserved]))
    fun s' ⟨⟨h0, hm, hrd', hwr'⟩, hg, hsp⟩ => ⟨?_, hg, hsp, hm, hrd', hwr'⟩
  rw [h0, VG.Proof.ChaCha20Poly1305.Arm.nz_bit]
  exact VG.Proof.ChaCha20Poly1305.Arm.sel_eq (VG.Proof.ChaCha20Poly1305.Arm.tag_eq s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (VG.Proof.ChaCha20Poly1305.Arm.tp s₀))

end VG.Proof.ChaCha20Poly1305.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified`. -/
section

section

/-!
# ChaCha20-Poly1305 on ARMv7: correctness

`seal` and `open`, from their parts: up to the arguments of
`vg_poly1305_finalize_scratch` (`sealMain`, `openMain`), the frame around it
(`finalize`), and the rest (`sealEnd`, `openEnd`). The constant-time proof
runs the taint analysis on the first and the last, and relates the two runs of
the frame by what these theorems say of the states between them.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The ciphertext `seal` computes. -/
abbrev Ct (s₀ : State) : List Byte := Spec.ChaCha20.encrypt (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 1 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀)

theorem srcA {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.Src s₀ (VG.Proof.ChaCha20Poly1305.Arm.aP s₀) (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) :=
  ⟨(s₀.gpr .r3).isLt, hp.fit_a, hp.c_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hp.a_rd, hc⟩⟩

theorem srcD {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) : VG.Proof.ChaCha20Poly1305.Arm.Src s₀ (VG.Proof.ChaCha20Poly1305.Arm.dP s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) :=
  ⟨(stackArg s₀ 1).isLt, hp.fit_d, hp.c_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ hp.d_wr, hc⟩⟩

theorem hAL (s₀ : State) : s₀.gpr .r3 = BitVec.ofNat 32 (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) := by simp [VG.Proof.ChaCha20Poly1305.Arm.AL]

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.ad s₀) (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) = VG.Proof.ChaCha20Poly1305.Arm.A s₀ :=
  VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm
    · exact hp.a_d
    · exact hp.b_a.symm) (by have := (s₀.gpr .r3).isLt; simp only [VG.Proof.ChaCha20Poly1305.Arm.AL]; omega)

/-- The data is unchanged by a frame of the context and the stack below. -/
theorem data_frame {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∃ k n, k + n ≤ 632 ∧ Region.Sub r (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀) :
    bytesAt m' (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = bytesAt m (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) :=
  VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame hf (fun r hr => by
    obtain ⟨k, n, h⟩ := hd r hr
    rcases h with ⟨hk, hs⟩ | rfl
    · exact (hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ hk)).symm.sub_right hs
    · exact hp.b_d.symm) (by have := (stackArg s₀ 1).isLt; simp only [VG.Proof.ChaCha20Poly1305.Arm.L]; omega)

theorem sub_self' (s₀ : State) (k n : Nat) : Region.Sub (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) := fun _ h => h

theorem macData_eq (a c : List Byte) :
    macData a c = [] ++ (a ++ pad16 a) ++ (c ++ pad16 c) ++ (leBytes 8 a.length ++ leBytes 8 c.length) := by
  simp [macData, List.append_assoc]

/-! ## Up to the frame -/

/-- The MAC so far, from the Poly1305 state for the one-time key: the
additional data and the text `x`, padded, and the lengths. -/
theorem mac_parts {s₀ s₁ s₂ s₃ s₄ : State} {x : List Byte} (hx : x.length = VG.Proof.ChaCha20Poly1305.Arm.L s₀)
    (hr₁ : Repr s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) [])
    (ha : ∀ key msg, Repr s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg → Repr s₂.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key (msg ++
      (bytesAt s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.ad s₀) (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) ++ pad16 (bytesAt s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.ad s₀) (VG.Proof.ChaCha20Poly1305.Arm.AL s₀)))))
    (hA : bytesAt s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.ad s₀) (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) = VG.Proof.ChaCha20Poly1305.Arm.A s₀)
    (hd : ∀ key msg, Repr s₂.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg → Repr s₃.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key (msg ++ (x ++ pad16 x)))
    (hl : ∀ key msg, Repr s₃.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key msg →
      Repr s₄.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) key (msg ++ (leBytes 8 (VG.Proof.ChaCha20Poly1305.Arm.AL s₀) ++ leBytes 8 (VG.Proof.ChaCha20Poly1305.Arm.L s₀)))) :
    Repr s₄.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) x) := by
  have := hl _ _ (hd _ _ (ha _ _ hr₁))
  rw [hA] at this
  rwa [VG.Proof.ChaCha20Poly1305.Arm.macData_eq, show (VG.Proof.ChaCha20Poly1305.Arm.A s₀).length = VG.Proof.ChaCha20Poly1305.Arm.AL s₀ from VG.Proof.Poly1305.length_bytesAt _ _ _, hx]

theorem count_eq {s₀ : State} {x : List Byte} (hx : x.length = VG.Proof.ChaCha20Poly1305.Arm.L s₀) :
    BitVec.ofNat 64 (16 * ((VG.Proof.ChaCha20Poly1305.Arm.AL s₀ + 15) / 16 + (VG.Proof.ChaCha20Poly1305.Arm.L s₀ + 15) / 16 + 1)) =
      BitVec.ofNat 64 (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) x).length := by
  rw [VG.Proof.ChaCha20Poly1305.Arm.length_macData, hx, show (VG.Proof.ChaCha20Poly1305.Arm.A s₀).length = VG.Proof.ChaCha20Poly1305.Arm.AL s₀ from VG.Proof.Poly1305.length_bytesAt _ _ _]

/-- Before the frame in `seal`. -/
structure PreFs (s₀ : State) (s : State) : Prop where
  inv : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s
  r0 : s.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀
  r1 : s.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.tP s₀
  r12 : s.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ scrOff
  cnt : Proof.Poly1305.countArm s = BitVec.ofNat 64 (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.Ct s₀)).length
  repr : Repr s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.Ct s₀))
  data : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.Ct s₀

theorem sealMain_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre true s₀) : WP isa sealMain s₀ (VG.Proof.ChaCha20Poly1305.Arm.PreFs s₀) := by
  unfold sealMain
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.block1_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ :=
    VG.Proof.ChaCha20Poly1305.Arm.data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 632, .inl ⟨(Nat.le_refl _), by rw [VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have d₂ : bytesAt s₂.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 256, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
      · exact ⟨keyOff, 32, .inl ⟨by simp [keyOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩, d₁]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.crypt_ok hp h₂.inv h₂.st) fun s₃ ⟨i₃, k₃, c₃⟩ => ?_)
  rw [d₂] at c₃
  have key₃ : bytesAt s₃.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) keyOff) 32 = VG.Proof.ChaCha20Poly1305.Arm.otk s₀ := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [keyOff, stOff]) (by simp [keyOff]) (by simp [stOff])
        · exact hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [keyOff]))) (by lit_omega), h₂.key]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.polyInit_ok hp i₃ key₃) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.Ct s₀ := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩, c₃]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.macPad_ok hp (p := .r8) (n := .r9) ⟨.inl rfl, .inl rfl⟩ (VG.Proof.ChaCha20Poly1305.Arm.srcA hp) i₄ i₄.regs.r8
    (by rw [i₄.regs.r9]; exact VG.Proof.ChaCha20Poly1305.Arm.hAL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have hmac : ∀ r ∈ VG.Proof.ChaCha20Poly1305.Arm.macR s₀, ∃ k n, k + n ≤ 632 ∧ Region.Sub r (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 128, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
    · exact ⟨padOff, 16, .inl ⟨by simp [padOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
  have c₅ : bytesAt s₅.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.Ct s₀ := by rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₅.frame hmac, c₄]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.macPad_ok hp (p := .r10) (n := .r11) ⟨.inr rfl, .inr rfl⟩ (VG.Proof.ChaCha20Poly1305.Arm.srcD hp) i₅ i₅.regs.r10
    (by rw [i₅.regs.r11]; exact VG.Proof.ChaCha20Poly1305.Arm.hL s₀)) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have c₆ : bytesAt s₆.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.Ct s₀ := by rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₆.frame hmac, c₅]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.lengths_ok hp i₆) fun s₇ ⟨i₇, k₇, r₇⟩ => ?_)
  have c₇ : bytesAt s₇.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.Ct s₀ := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₇.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
      · exact ⟨lenOff, 16, .inl ⟨by simp [lenOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩, c₆]
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.finArgs_ok i₇ (by decide) (VG.Proof.ChaCha20Poly1305.Arm.out_seal hp i₇)) fun s₈ ⟨i₈, k₈, h0, h1, h12, hc⟩ => ?_
  have hlen : (VG.Proof.ChaCha20Poly1305.Arm.Ct s₀).length = VG.Proof.ChaCha20Poly1305.Arm.L s₀ := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.length_encrypt, VG.Proof.Poly1305.length_bytesAt]
  refine ⟨i₈, h0, h1, h12, by rw [hc, VG.Proof.ChaCha20Poly1305.Arm.count_eq hlen], ?_, by rw [k₈.mem_eq, c₇]⟩
  rw [k₈.mem_eq]
  refine VG.Proof.ChaCha20Poly1305.Arm.mac_parts hlen r₄ r₅ (VG.Proof.ChaCha20Poly1305.Arm.aad_eq hp i₄) ?_ r₇
  rw [c₅] at r₆
  exact r₆

/-! ## The frame -/

/-- After the frame in `seal`: the tag written, and what restoring the
registers needs. -/
structure PostFs (s₀ : State) (s : State) : Prop where
  regs : VG.Proof.ChaCha20Poly1305.Arm.Regs s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : VG.Proof.ChaCha20Poly1305.Arm.Saved s₀ s.mem
  tag : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 16 = mac (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.Ct s₀))
  data : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.Ct s₀

theorem finalize_seal_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre true s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.PreFs s₀ s) :
    WP isa finalize s (VG.Proof.ChaCha20Poly1305.Arm.PostFs s₀) :=
  WP.mono (VG.Proof.ChaCha20Poly1305.Arm.fin_ok hp h.inv (VG.Proof.ChaCha20Poly1305.Arm.outOk_tP hp) h.r0 h.r1 h.r12) fun s' ⟨k', rg', sv', t'⟩ =>
    ⟨rg', by rw [k'.sp, h.inv.sp], by rw [k'.rd, h.inv.rd], by rw [k'.wr, h.inv.wr], sv',
      t' _ _ h.repr h.cnt, by
      rw [VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame k'.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by lit_omega))).symm
        · exact hp.d_t
        · exact (hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [scrOff]))).symm
        · exact hp.b_d.symm) (by have := (stackArg s₀ 1).isLt; simp only [VG.Proof.ChaCha20Poly1305.Arm.L]; omega), h.data]⟩

/-! ## After the frame -/

/-- The callee-saved registers restored, and the stack pointer as on entry. -/
theorem abi_of {s₀ s' : State} (hr : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r) (hsp : s'.sp = s₀.sp) :
    abiPreserved s₀ s' := ⟨hr, hsp⟩

theorem sealEnd_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre true s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.PostFs s₀ s) :
    WP isa (.block sealEnd) s fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' := by
  unfold sealEnd
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.restore_ok hp h.regs.r7 h.saved h.rd h.wr) fun s₂ ⟨g₂, _, m₂, sp₂, _, _⟩ =>
    ⟨VG.Proof.ChaCha20Poly1305.Arm.abi_of g₂ (by rw [sp₂, h.sp]), ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (VG.Proof.ChaCha20Poly1305.Arm.K s₀) (VG.Proof.ChaCha20Poly1305.Arm.N s₀) (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀) =
    (bytesAt s₂.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀), bytesAt s₂.mem (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 16)
  rw [m₂, h.data, h.tag]
  simp only [Spec.ChaCha20Poly1305.encrypt]

theorem seal_correct {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre true s₀) :
    WP isa Impl.ChaCha20Poly1305.Arm.«seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.sealMain_ok hp) fun _ h => WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.finalize_seal_ok hp h)
    fun _ h' => VG.Proof.ChaCha20Poly1305.Arm.sealEnd_ok hp h'))

/-! ## Open -/

/-- A part of the context is unchanged by a frame of other parts of it, the
data and the stack below. -/
theorem ctx_disj {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {rs : List Region} {a n : Nat} (ha : a + n ≤ 632)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀) :
    ∀ r ∈ rs, (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ a n).Disjoint r := by
  intro r hr
  rcases hd r hr with ⟨k, l, hk, hkl, rfl⟩ | rfl | rfl
  · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by lit_omega) ha hk
  · exact hp.c_d.sub_left (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ ha)
  · exact (hp.b_c.sub_right (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ ha)).symm

theorem ctx_bytes {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a n : Nat}
    (ha : a + n ≤ 632)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀) :
    bytesAt m' (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) n = bytesAt m (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) a) n :=
  VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame hf (VG.Proof.ChaCha20Poly1305.Arm.ctx_disj hp ha hd) (by lit_omega)

theorem ctx_state {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ stOff ∨ stOff + 64 ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨
      r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀) :
    stateAt m' (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = stateAt m (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) :=
  VG.Proof.ChaCha20Poly1305.Arm.stateAt_frame hf (VG.Proof.ChaCha20Poly1305.Arm.ctx_disj hp (a := stOff) (n := 64) (by simp [stOff]) hd)

/-- Before the frame in `open`. -/
structure PreFo (s₀ : State) (s : State) : Prop where
  inv : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s
  r0 : s.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₀
  r1 : s.gpr .r1 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ tagOff
  r12 : s.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₀ scrOff
  cnt : Proof.Poly1305.countArm s = BitVec.ofNat 64 (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀)).length
  repr : Repr s.mem (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀))
  data : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀
  st : stateAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀)

/-- The regions `macPad` writes, as `ctx_bytes` wants them. -/
theorem macR_hd (s₀ : State) {a n : Nat} (h : 128 ≤ a) (h' : padOff + 16 ≤ a ∨ a + n ≤ padOff) :
    ∀ r ∈ VG.Proof.ChaCha20Poly1305.Arm.macR s₀, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨
      r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  · exact .inl ⟨padOff, 16, by simp [padOff], h', rfl⟩

theorem openMain_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre false s₀) : WP isa openMain s₀ (VG.Proof.ChaCha20Poly1305.Arm.PreFo s₀) := by
  unfold openMain
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.block1_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ :=
    VG.Proof.ChaCha20Poly1305.Arm.data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 632, .inl ⟨(Nat.le_refl _), by rw [VG.Proof.ChaCha20Poly1305.Arm.sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have hd₂ : ∀ r ∈ [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 256, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ keyOff 32], ∃ k n, k + n ≤ 632 ∧ Region.Sub r (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) ∨
      r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 256, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
    · exact ⟨keyOff, 32, .inl ⟨by simp [keyOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
  have d₂ : bytesAt s₂.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ := by rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp f₂ hd₂, d₁]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.polyInit_ok hp h₂.inv h₂.key) fun s₃ ⟨i₃, k₃, r₃⟩ => ?_)
  have hd₀ : ∀ {a n : Nat}, 128 ≤ a → ∀ r ∈ [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ :=
    fun ha r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  have d₃ : bytesAt s₃.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₃.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩, d₂]
  have st₃ : stateAt s₃.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.ctx_state hp k₃.frame (hd₀ (by simp [stOff])), h₂.st]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.macPad_ok hp (p := .r8) (n := .r9) ⟨.inl rfl, .inl rfl⟩ (VG.Proof.ChaCha20Poly1305.Arm.srcA hp) i₃ i₃.regs.r8
    (by rw [i₃.regs.r9]; exact VG.Proof.ChaCha20Poly1305.Arm.hAL s₀)) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have hmac : ∀ r ∈ VG.Proof.ChaCha20Poly1305.Arm.macR s₀, ∃ k n, k + n ≤ 632 ∧ Region.Sub r (VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k n) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 128, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
    · exact ⟨padOff, 16, .inl ⟨by simp [padOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
  have d₄ : bytesAt s₄.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ := by rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₄.frame hmac, d₃]
  have st₄ : stateAt s₄.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.ctx_state hp k₄.frame (VG.Proof.ChaCha20Poly1305.Arm.macR_hd s₀ (by simp [stOff]) (by simp [stOff, padOff])), st₃]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.macPad_ok hp (p := .r10) (n := .r11) ⟨.inr rfl, .inr rfl⟩ (VG.Proof.ChaCha20Poly1305.Arm.srcD hp) i₄ i₄.regs.r10
    (by rw [i₄.regs.r11]; exact VG.Proof.ChaCha20Poly1305.Arm.hL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have d₅ : bytesAt s₅.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ := by rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₅.frame hmac, d₄]
  have st₅ : stateAt s₅.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.ctx_state hp k₅.frame (VG.Proof.ChaCha20Poly1305.Arm.macR_hd s₀ (by simp [stOff]) (by simp [stOff, padOff])), st₄]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.lengths_ok hp i₅) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have hl : ∀ {a n : Nat}, 128 ≤ a → (lenOff + 16 ≤ a ∨ a + n ≤ lenOff) → ∀ r ∈ [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ lenOff 16],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ :=
    fun ha ha' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
      · exact .inl ⟨lenOff, 16, by simp [lenOff], ha', rfl⟩
  have d₆ : bytesAt s₆.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀ := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k₆.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
      · exact ⟨lenOff, 16, .inl ⟨by simp [lenOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩, d₅]
  have st₆ : stateAt s₆.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.ctx_state hp k₆.frame (hl (by simp [stOff]) (by simp [stOff, lenOff])), st₅]
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.finArgs_ok i₆ (by decide) (VG.Proof.ChaCha20Poly1305.Arm.out_open i₆)) fun s₇ ⟨i₇, k₇, h0, h1, h12, hc⟩ => ?_
  have hlen : (VG.Proof.ChaCha20Poly1305.Arm.D s₀).length = VG.Proof.ChaCha20Poly1305.Arm.L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₇ := k₇.mem_eq
  refine ⟨i₇, h0, h1, h12, by rw [hc, VG.Proof.ChaCha20Poly1305.Arm.count_eq hlen], ?_, by rw [m₇, d₆], by rw [m₇, st₆]⟩
  rw [m₇]
  refine VG.Proof.ChaCha20Poly1305.Arm.mac_parts hlen r₃ r₄ (VG.Proof.ChaCha20Poly1305.Arm.aad_eq hp i₃) ?_ r₆
  rw [d₄] at r₅
  exact r₅

/-- After the frame in `open`. -/
structure PostFo (s₀ : State) (s : State) : Prop where
  inv : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s
  tag : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) tagOff) 16 = mac (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀))
  data : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = VG.Proof.ChaCha20Poly1305.Arm.D s₀
  st : stateAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) stOff) = Spec.ChaCha20.initState (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 0 (VG.Proof.ChaCha20Poly1305.Arm.N s₀)

theorem fin_hd (s₀ : State) {a n : Nat} (h : 128 ≤ a) (h' : tagOff + 16 ≤ a ∨ a + n ≤ tagOff)
    (h'' : scrOff + 128 ≤ a ∨ a + n ≤ scrOff) :
    ∀ r ∈ [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 128, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ tagOff 16, VG.Proof.ChaCha20Poly1305.Arm.sub s₀ scrOff 128, VG.Proof.ChaCha20Poly1305.Arm.belR s₀],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  · exact .inl ⟨tagOff, 16, by simp [tagOff], h', rfl⟩
  · exact .inl ⟨scrOff, 128, by simp [scrOff], h'', rfl⟩
  · exact .inr (.inr rfl)

theorem finalize_open_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre false s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.PreFo s₀ s) :
    WP isa finalize s (VG.Proof.ChaCha20Poly1305.Arm.PostFo s₀) := by
  have et := hp.addr_ptr (k := tagOff) (by simp [tagOff])
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.fin_ok hp h.inv (VG.Proof.ChaCha20Poly1305.Arm.outOk_tag hp) h.r0 h.r1 h.r12) fun s' ⟨k', _, _, t'⟩ => ?_
  rw [et] at k' t'
  refine ⟨h.inv.step k' (fun r hr => ?_) (fun r hr => ?_), t' _ _ h.repr h.cnt, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.ChaCha20Poly1305.Arm.sub_inv s₀ (by lit_omega)
    · exact VG.Proof.ChaCha20Poly1305.Arm.sub_inv s₀ (by simp [tagOff])
    · exact VG.Proof.ChaCha20Poly1305.Arm.sub_inv s₀ (by simp [scrOff])
    · exact ⟨VG.Proof.ChaCha20Poly1305.Arm.belR s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [savOff]) (by simp [savOff]) (by lit_omega)
    · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [savOff, tagOff]) (by simp [savOff]) (by simp [tagOff])
    · exact VG.Proof.ChaCha20Poly1305.Arm.sub_disj s₀ (by simp [savOff, scrOff]) (by simp [savOff]) (by simp [scrOff])
    · exact (hp.b_c.sub_right (VG.Proof.ChaCha20Poly1305.Arm.sub_ctx s₀ (by simp [savOff]))).symm
  · rw [VG.Proof.ChaCha20Poly1305.Arm.data_frame hp k'.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
      · exact ⟨tagOff, 16, .inl ⟨by simp [tagOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
      · exact ⟨scrOff, 128, .inl ⟨by simp [scrOff], VG.Proof.ChaCha20Poly1305.Arm.sub_self' _ _ _⟩⟩
      · exact ⟨0, 0, .inr rfl⟩, h.data]
  · rw [VG.Proof.ChaCha20Poly1305.Arm.ctx_state hp k'.frame (VG.Proof.ChaCha20Poly1305.Arm.fin_hd s₀ (by simp [stOff]) (by simp [stOff, tagOff])
      (by simp [stOff, scrOff])), h.st]

/-- `tag` is unchanged while the invariant holds. -/
theorem tag_eq0 {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) : bytesAt s.mem (VG.Proof.ChaCha20Poly1305.Arm.tp s₀) 16 = VG.Proof.ChaCha20Poly1305.Arm.T0 s₀ :=
  VG.Proof.ChaCha20Poly1305.Arm.bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_t.symm
    · exact hp.d_t.symm
    · exact hp.b_t.symm) (by omega)

theorem openEnd_ok {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre false s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.Arm.PostFo s₀ s) :
    WP isa openEnd s fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  unfold openEnd
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.crypt_ok hp h.inv h.st) fun s₁ ⟨i₁, k₁, c₁⟩ => ?_)
  have hc : ∀ {a n : Nat}, stOff + 64 ≤ a → a + n ≤ 632 → ∀ r ∈ [VG.Proof.ChaCha20Poly1305.Arm.sub s₀ 0 (stOff + 64), VG.Proof.ChaCha20Poly1305.Arm.dR s₀],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = VG.Proof.ChaCha20Poly1305.Arm.sub s₀ k l) ∨ r = VG.Proof.ChaCha20Poly1305.Arm.dR s₀ ∨ r = VG.Proof.ChaCha20Poly1305.Arm.belR s₀ :=
    fun ha _ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, stOff + 64, by simp [stOff], by omega, rfl⟩
      · exact .inr (.inl rfl)
  have t₁ : bytesAt s₁.mem (VG.Proof.ChaCha20Poly1305.Arm.off (VG.Proof.ChaCha20Poly1305.Arm.cx s₀) tagOff) 16 = mac (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀)) := by
    rw [VG.Proof.ChaCha20Poly1305.Arm.ctx_bytes hp k₁.frame (by simp [tagOff]) (hc (by simp [stOff, tagOff]) (by simp [tagOff])), h.tag]
  rw [h.data] at c₁
  refine WP.block_append (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.compare_ok hp i₁)
    fun s₂ ⟨r0₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  have i₂ : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s₂ := i₁.step0 ⟨fun r hr _ => g₂ r hr, sp₂, rd₂, wr₂, by rw [m₂]; exact Frame.refl _ _⟩
  refine WP.mono (VG.Proof.ChaCha20Poly1305.Arm.restore_ok hp i₂.regs.r7 i₂.saved i₂.rd i₂.wr) fun s₃ ⟨g₃, o₃, m₃, sp₃, _, _⟩ =>
    ⟨VG.Proof.ChaCha20Poly1305.Arm.abi_of g₃ (by rw [sp₃, i₂.sp]), ?_⟩
  have r0₃ : s₃.gpr .r0 = if mac (VG.Proof.ChaCha20Poly1305.Arm.otk s₀) (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀)) = VG.Proof.ChaCha20Poly1305.Arm.T0 s₀ then 1 else 0 := by
    rw [o₃ .r0 (by decide) (by decide), r0₂, t₁, VG.Proof.ChaCha20Poly1305.Arm.tag_eq0 hp i₁]
  have d₃ : bytesAt s₃.mem (VG.Proof.ChaCha20Poly1305.Arm.dp s₀) (VG.Proof.ChaCha20Poly1305.Arm.L s₀) = Spec.ChaCha20.encrypt (VG.Proof.ChaCha20Poly1305.Arm.K s₀) 1 (VG.Proof.ChaCha20Poly1305.Arm.N s₀) (VG.Proof.ChaCha20Poly1305.Arm.D s₀) := by
    rw [m₃, m₂, c₁]
  rw [VG.Proof.ChaCha20Poly1305.openArm, Contract.post_mk]
  rw [r0₃]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left hmac, d₃⟩
  next hn => exact ite_eq_right (decrypt_eq_none hn)

theorem open_correct {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre false s₀) :
    WP isa Impl.ChaCha20Poly1305.Arm.«open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.openMain_ok hp) fun _ h => WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.Arm.finalize_open_ok hp h)
    fun _ h' => VG.Proof.ChaCha20Poly1305.Arm.openEnd_ok hp h'))

end VG.Proof.ChaCha20Poly1305.Arm

end


/-!
# ChaCha20-Poly1305 on ARMv7: `Verified`

Correctness (above), constant time, and a state satisfying the precondition,
of the code with its working space as its last argument
(`sealScratchContract`, `openScratchContract`), and then of the functions,
which allocate it in a frame of 656 bytes on the stack and wipe it after the
code (`Verified.stackScratchWiped`).

Constant time relates two runs from states that agree on the public data
(`RelCT`), part by part. The taint analysis does not analyse frames, so it
runs on the code before the frame around `vg_poly1305_finalize_scratch`
(`sealMain`, `openMain`) and after it (`sealEnd`, `openEnd`), through the
callees' code: it knows `r7`–`r11` for public after each call because every
callee saves them in memory at known offsets of the context, which it
tracks, and restores them, and `r7` for the base of the context once it is
set from the callee's pointer that the callee keeps. The stack arguments
are public, and the one at `sp + 12` is the base of the context. The frame
itself leaks only addresses computed from the stack pointer, and
`vg_poly1305_finalize_scratch` is constant time (`RelCT.frame`,
`RelCT.call`), given what the correctness proof shows of the states on
either side of it in each run (`RelCT.wp`): the same stack pointer and
arguments, whose values are computed from public data only.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (macData)

variable {e : Bool}

/-! ## The writable regions -/

/-- The index of the context among the writable regions. -/
abbrev ci (enc : Bool) : Nat := if enc then 2 else 1

/-- Lower bounds on the lengths of the writable regions. -/
abbrev lensOf (enc : Bool) : List Nat := if enc then [0, 16, 632] else [0, 632]

theorem APre.wr_cases {s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s) {r : Region} (hr : r ∈ s.wr) :
    r = VG.Proof.ChaCha20Poly1305.Arm.dR s ∨ r = VG.Proof.ChaCha20Poly1305.Arm.ctxR s ∨ (e = true ∧ r = VG.Proof.ChaCha20Poly1305.Arm.tR s) := by
  cases e
  · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
    rw [hw] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.tR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
    rw [hw] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨rfl, rfl⟩)
    · exact .inr (.inl rfl)

theorem wr_facts {s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s) :
    List.Forall₂ (fun r l => l ≤ r.len) s.wr (VG.Proof.ChaCha20Poly1305.Arm.lensOf e) ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32 := by
  have hc := hp.fit_c; have hd := hp.fit_d; have ht := hp.fit_t
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · cases e
    · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
      rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.tR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
      rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · cases e
    · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
      rw [hw]
      exact List.Pairwise.cons (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.c_d.symm) (List.pairwise_singleton _ _)
    · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.tR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
      rw [hw]
      refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_) (List.pairwise_singleton _ _))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.d_t
        · exact hp.c_d.symm
      · simp only [List.mem_singleton] at hr; subst hr; exact hp.c_t.symm
  · rcases hp.wr_cases hr with rfl | rfl | ⟨-, rfl⟩ <;> simp only [VG.Proof.ChaCha20Poly1305.Arm.addr_toNat] <;> omega

/-- The stack arguments are outside the writable regions. -/
theorem arg_wr {s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s) : ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 16⟩ r := by
  have e' : (⟨State.addr s.sp, 16⟩ : Region) = VG.Proof.ChaCha20Poly1305.Arm.argR s := by simp [stackArgAddr]
  intro r hr
  rw [e']
  rcases hp.wr_cases hr with rfl | rfl | ⟨he, rfl⟩
  · exact hp.d_arg.symm
  · exact hp.c_arg.symm
  · cases he; exact (show (VG.Proof.ChaCha20Poly1305.Arm.tR s).Disjoint (VG.Proof.ChaCha20Poly1305.Arm.argR s) from hp.t_arg).symm

theorem wr_eq {s₁ s₂ : State} (h₁ : VG.Proof.ChaCha20Poly1305.Arm.APre e s₁) (h₂ : VG.Proof.ChaCha20Poly1305.Arm.APre e s₂) (hpub : VG.Proof.ChaCha20Poly1305.pubArm s₁ s₂) : s₁.wr = s₂.wr := by
  obtain ⟨-, -, -, -, -, a0, a1, a2, a3⟩ := hpub
  rw [h₁.wr, h₂.wr]
  simp only [VG.Proof.ChaCha20Poly1305.Arm.ctxR, VG.Proof.ChaCha20Poly1305.Arm.dR, VG.Proof.ChaCha20Poly1305.Arm.tR, VG.Proof.ChaCha20Poly1305.Arm.cx, VG.Proof.ChaCha20Poly1305.Arm.dp, VG.Proof.ChaCha20Poly1305.Arm.tp, VG.Proof.ChaCha20Poly1305.Arm.cP, VG.Proof.ChaCha20Poly1305.Arm.dP, VG.Proof.ChaCha20Poly1305.Arm.tP, VG.Proof.ChaCha20Poly1305.Arm.L, a0, a1, a2, a3]

theorem stackArgs_eq {s₁ s₂ : State} (hpub : VG.Proof.ChaCha20Poly1305.pubArm s₁ s₂) : ∀ i < 4, stackArg s₁ i = stackArg s₂ i := by
  obtain ⟨-, -, -, -, -, a0, a1, a2, a3⟩ := hpub
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3

/-- The stack arguments, from a state where the invariant holds. -/
theorem Inv.argEq {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s₀) (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) {i : Nat} (hi : i < 4) :
    stackArg s i = stackArg s₀ i := by
  rw [show stackArg s i = s.mem.readW (stackArgAddr s₀ i) 32 by simp only [stackArg, stackArgAddr, h.sp]]
  exact h.arg hp hi

/-! ## The taint on entry -/

/-- The initial taint: `r0`–`r3` (`key`, `nonce`, `aad`, `aad_len`) and the
stack arguments (`data`, `len`, `tag`, `work`) are public, and the last is
the base of the context. -/
def τ₀ (enc : Bool) : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := VG.Proof.ChaCha20Poly1305.Arm.lensOf enc, argLen := 16,
    argBases := [(12, VG.Proof.ChaCha20Poly1305.Arm.ci enc)] }

theorem wf₀ {s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre e s) : VG.Arm.Taint.Wf (VG.Proof.ChaCha20Poly1305.Arm.τ₀ e) s := by
  refine ⟨fun _ => VG.Proof.ChaCha20Poly1305.Arm.wr_facts hp, fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp.spfit, VG.Proof.ChaCha20Poly1305.Arm.arg_wr hp⟩,
    fun p hp' => ?_⟩
  simp only [VG.Proof.ChaCha20Poly1305.Arm.τ₀, List.mem_singleton] at hp'
  subst hp'
  refine ⟨Nat.le_refl _, ?_⟩
  cases e
  · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
    rw [VG.Arm.Taint.region, hw]; rfl
  · have hw : s.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s, VG.Proof.ChaCha20Poly1305.Arm.tR s, VG.Proof.ChaCha20Poly1305.Arm.ctxR s] := hp.wr
    rw [VG.Arm.Taint.region, hw]; rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : VG.Proof.ChaCha20Poly1305.Arm.APre e s₁) (h₂ : VG.Proof.ChaCha20Poly1305.Arm.APre e s₂) (hpub : VG.Proof.ChaCha20Poly1305.pubArm s₁ s₂) :
    VG.Arm.Taint.Agree (VG.Proof.ChaCha20Poly1305.Arm.τ₀ e) s₁ s₂ := by
  have hw := VG.Proof.ChaCha20Poly1305.Arm.wr_eq h₁ h₂ hpub
  have ha := VG.Proof.ChaCha20Poly1305.Arm.stackArgs_eq hpub
  obtain ⟨psp, p0, p1, p2, p3, -⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => hw, VG.Proof.ChaCha20Poly1305.Arm.wf₀ h₁, VG.Proof.ChaCha20Poly1305.Arm.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    argMem_of (j := 4) psp h₁.spfit ha⟩
  simp only [VG.Proof.ChaCha20Poly1305.Arm.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## The frame -/

theorem push_eq' {s a : State} (h : isa.push (.push [.r1, .r12]) s = some a) : a = pushed [.r1, .r12] s := by
  rw [push_pushed rfl (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

/-- `vg_poly1305_finalize_scratch`'s view of the state after the push, with the
regions given in terms of the stack pointer `sp`. -/
theorem finView_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) (P O Sc : BitVec 32) :
    (pushed [.r1, .r12] s).callEntry.withRegions [⟨State.addr sp - 8, 8⟩] (VG.Proof.ChaCha20Poly1305.Arm.finWr P O Sc) = VG.Proof.ChaCha20Poly1305.Arm.finView s P O Sc := by
  rw [← h]

/-- The frame around `vg_poly1305_finalize_scratch`, in two runs whose states before
it are `x₁` and `x₂`, with the same stack pointer, pointers (`out` is `O`)
and message length. -/
theorem frame_ct {s₁ s₂ : State} (hp₁ : VG.Proof.ChaCha20Poly1305.Arm.APre e s₁) (hp₂ : VG.Proof.ChaCha20Poly1305.Arm.APre e s₂) (hpub : VG.Proof.ChaCha20Poly1305.pubArm s₁ s₂)
    {O : State → BitVec 32} (ho₁ : VG.Proof.ChaCha20Poly1305.Arm.OutOk s₁ (O s₁)) (ho₂ : VG.Proof.ChaCha20Poly1305.Arm.OutOk s₂ (O s₂)) (hO : O s₂ = O s₁)
    {F : State → State → Prop}
    (hF : ∀ x₁ x₂, F x₁ x₂ → VG.Proof.ChaCha20Poly1305.Arm.Inv s₁ x₁ ∧ VG.Proof.ChaCha20Poly1305.Arm.Inv s₂ x₂ ∧ x₁.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₁ ∧ x₁.gpr .r1 = O s₁ ∧
      x₁.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₁ scrOff ∧ x₂.gpr .r0 = VG.Proof.ChaCha20Poly1305.Arm.cP s₂ ∧ x₂.gpr .r1 = O s₂ ∧
      x₂.gpr .r12 = VG.Proof.ChaCha20Poly1305.Arm.ptr s₂ scrOff ∧ Proof.Poly1305.countArm x₁ = Proof.Poly1305.countArm x₂) :
    RelCT isa F finalize fun _ _ => True := by
  obtain ⟨psp, -, -, -, -, -, -, -, a3⟩ := hpub
  refine RelCT.frame (fun x₁ x₂ h => by
    obtain ⟨i₁, i₂, -⟩ := hF x₁ x₂ h
    rw [i₁.sp, i₂.sp, psp]) ?_
  refine RelCT.call (k := Proof.Poly1305.finalizeArm) Proof.Poly1305.Arm.Fin.finalize_ok
    Proof.Poly1305.Arm.Fin.finalize_ct [⟨State.addr s₁.sp - 8, 8⟩]
    (VG.Proof.ChaCha20Poly1305.Arm.finWr (VG.Proof.ChaCha20Poly1305.Arm.cP s₁) (O s₁) (VG.Proof.ChaCha20Poly1305.Arm.ptr s₁ scrOff)) fun a b ⟨x₁, x₂, h, pa, pb⟩ => ?_
  obtain ⟨i₁, i₂, a0, a1, a12, b0, b1, b12, hc⟩ := hF x₁ x₂ h
  rw [VG.Proof.ChaCha20Poly1305.Arm.push_eq' pa, VG.Proof.ChaCha20Poly1305.Arm.push_eq' pb]
  have f₁ := VG.Proof.ChaCha20Poly1305.Arm.fin_args hp₁ i₁ ho₁ a0 a1 a12
  have f₂ := VG.Proof.ChaCha20Poly1305.Arm.fin_args hp₂ i₂ ho₂ b0 b1 b12
  have e2 : VG.Proof.ChaCha20Poly1305.Arm.cP s₂ = VG.Proof.ChaCha20Poly1305.Arm.cP s₁ := a3.symm
  have ep : ∀ k, VG.Proof.ChaCha20Poly1305.Arm.ptr s₂ k = VG.Proof.ChaCha20Poly1305.Arm.ptr s₁ k := fun k => by simp only [VG.Proof.ChaCha20Poly1305.Arm.ptr, e2]
  rw [ep, e2, hO] at f₂
  rw [VG.Proof.ChaCha20Poly1305.Arm.finView_eq i₁.sp, VG.Proof.ChaCha20Poly1305.Arm.finView_eq (i₂.sp.trans psp.symm)]
  refine ⟨f₁.pre, f₂.pre, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.ChaCha20Poly1305.Arm.fin_nsp, VG.Proof.ChaCha20Poly1305.Arm.fin_nsp, i₁.sp, i₂.sp, psp]
  · rw [VG.Proof.ChaCha20Poly1305.Arm.fin_ng _ _ _ _ .r0 (by decide), VG.Proof.ChaCha20Poly1305.Arm.fin_ng _ _ _ _ .r0 (by decide), a0, b0, e2]
  · have := (BitVec.append_32_inj hc).2
    rw [VG.Proof.ChaCha20Poly1305.Arm.fin_ng _ _ _ _ .r2 (by decide), VG.Proof.ChaCha20Poly1305.Arm.fin_ng _ _ _ _ .r2 (by decide), this]
  · have := (BitVec.append_32_inj hc).1
    rw [VG.Proof.ChaCha20Poly1305.Arm.fin_ng _ _ _ _ .r3 (by decide), VG.Proof.ChaCha20Poly1305.Arm.fin_ng _ _ _ _ .r3 (by decide), this]
  · rw [f₁.arg0 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp _ _ _ _) rfl, f₂.arg0 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp _ _ _ _) rfl]
  · rw [f₁.arg1 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp _ _ _ _) rfl, f₂.arg1 _ (VG.Proof.ChaCha20Poly1305.Arm.fin_nsp _ _ _ _) rfl]
  · have e : VG.Proof.ChaCha20Poly1305.Arm.finRd x₁ = [⟨State.addr s₁.sp - 8, 8⟩] := by simp [VG.Proof.ChaCha20Poly1305.Arm.finRd, i₁.sp]
    rw [← e]; exact f₁.cov
  · exact f₁.covW
  · have e : VG.Proof.ChaCha20Poly1305.Arm.finRd x₂ = [⟨State.addr s₁.sp - 8, 8⟩] := by simp [VG.Proof.ChaCha20Poly1305.Arm.finRd, i₂.sp, psp]
    rw [← e]; exact f₂.cov
  · exact f₂.covW

/-! ## After the frame -/

/-- `open`'s taint after the frame: the context (the base of the second
writable region), the data, its length and the stack arguments are public. -/
def τB : VG.Arm.Taint.T :=
  { regs := .ofList [.r7, .r10, .r11], flags := false, lens := VG.Proof.ChaCha20Poly1305.Arm.lensOf false, bases := [(.r7, 1)],
    argLen := 16 }

theorem wfB {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.Arm.APre false s₀) (h : VG.Proof.ChaCha20Poly1305.Arm.Inv s₀ s) : VG.Arm.Taint.Wf VG.Proof.ChaCha20Poly1305.Arm.τB s := by
  refine ⟨fun _ => by rw [h.wr]; exact VG.Proof.ChaCha20Poly1305.Arm.wr_facts hp, fun p hp' => ?_,
    fun _ => ⟨by rw [h.sp]; exact hp.spfit, by rw [h.sp, h.wr]; exact VG.Proof.ChaCha20Poly1305.Arm.arg_wr hp⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [VG.Proof.ChaCha20Poly1305.Arm.τB, List.mem_singleton] at hp'
  subst hp'
  have hw : s₀.wr = [VG.Proof.ChaCha20Poly1305.Arm.dR s₀, VG.Proof.ChaCha20Poly1305.Arm.ctxR s₀] := hp.wr
  rw [h.regs.r7, VG.Arm.Taint.region, h.wr, hw]; rfl

theorem agreeB {s₁ s₂ a b : State} (hp₁ : VG.Proof.ChaCha20Poly1305.Arm.APre false s₁) (hp₂ : VG.Proof.ChaCha20Poly1305.Arm.APre false s₂) (hpub : VG.Proof.ChaCha20Poly1305.pubArm s₁ s₂)
    (ha : VG.Proof.ChaCha20Poly1305.Arm.Inv s₁ a) (hb : VG.Proof.ChaCha20Poly1305.Arm.Inv s₂ b) : VG.Arm.Taint.Agree VG.Proof.ChaCha20Poly1305.Arm.τB a b := by
  have hw := VG.Proof.ChaCha20Poly1305.Arm.wr_eq hp₁ hp₂ hpub
  have hs := VG.Proof.ChaCha20Poly1305.Arm.stackArgs_eq hpub
  obtain ⟨psp, -, -, -, -, a0, a1, -, a3⟩ := hpub
  have hsp : a.sp = b.sp := by rw [ha.sp, hb.sp, psp]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => by rw [ha.wr, hb.wr, hw], VG.Proof.ChaCha20Poly1305.Arm.wfB hp₁ ha, VG.Proof.ChaCha20Poly1305.Arm.wfB hp₂ hb,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    argMem_of (j := 4) hsp (by rw [ha.sp]; exact hp₁.spfit) fun i hi => by
      rw [ha.argEq hp₁ hi, hb.argEq hp₂ hi]; exact hs i hi⟩
  simp only [VG.Proof.ChaCha20Poly1305.Arm.τB, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ha.regs.r7, hb.regs.r7, VG.Proof.ChaCha20Poly1305.Arm.cP, VG.Proof.ChaCha20Poly1305.Arm.cP, a3]
  · rw [ha.regs.r10, hb.regs.r10, VG.Proof.ChaCha20Poly1305.Arm.dP, VG.Proof.ChaCha20Poly1305.Arm.dP, a0]
  · rw [ha.regs.r11, hb.regs.r11, a1]

/-! ## Seal -/

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub Impl.ChaCha20Poly1305.Arm.«seal» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp₁ := APre.of s₁ h₁
  have hp₂ := APre.of s₂ h₂
  have hlen : (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₁) (VG.Proof.ChaCha20Poly1305.Arm.Ct s₁)).length = (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₂) (VG.Proof.ChaCha20Poly1305.Arm.Ct s₂)).length := by
    obtain ⟨-, -, -, -, p3, -, a1, -, -⟩ := hpub
    rw [VG.Proof.ChaCha20Poly1305.Arm.length_macData, VG.Proof.ChaCha20Poly1305.Arm.length_macData, VG.Proof.ChaCha20Poly1305.Arm.length_encrypt, VG.Proof.ChaCha20Poly1305.Arm.length_encrypt]
    simp only [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20Poly1305.Arm.AL, VG.Proof.ChaCha20Poly1305.Arm.L, p3, a1]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sealMain fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFs s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFs s₂ b :=
    (RelCT.taint (A := taint) (VG.Proof.ChaCha20Poly1305.Arm.τ₀ true) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact VG.Proof.ChaCha20Poly1305.Arm.agree₀ hp₁ hp₂ hpub) (by taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.ChaCha20Poly1305.Arm.sealMain_ok hp₁, VG.Proof.ChaCha20Poly1305.Arm.sealMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFs s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFs s₂ b) finalize
      fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFs s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFs s₂ b :=
    (VG.Proof.ChaCha20Poly1305.Arm.frame_ct hp₁ hp₂ hpub (O := VG.Proof.ChaCha20Poly1305.Arm.tP) (VG.Proof.ChaCha20Poly1305.Arm.outOk_tP hp₁) (VG.Proof.ChaCha20Poly1305.Arm.outOk_tP hp₂) hpub.2.2.2.2.2.2.2.1.symm
      fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨VG.Proof.ChaCha20Poly1305.Arm.finalize_seal_ok hp₁ h.2.1, VG.Proof.ChaCha20Poly1305.Arm.finalize_seal_ok hp₂ h.2.2⟩
  have B : RelCT isa (fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFs s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFs s₂ b) (.block sealEnd) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r7]) (fun a b h => VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.2.1.regs.r7, h.2.2.regs.r7, VG.Proof.ChaCha20Poly1305.Arm.cP, VG.Proof.ChaCha20Poly1305.Arm.cP, hpub.2.2.2.2.2.2.2.2]) (by taint_decide)
  exact ((A.seq (F.seq B)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Open -/

theorem open_ct : ConstantTime isa openArm.pre openArm.pub Impl.ChaCha20Poly1305.Arm.«open» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp₁ := APre.of s₁ h₁
  have hp₂ := APre.of s₂ h₂
  have hlen : (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₁) (VG.Proof.ChaCha20Poly1305.Arm.D s₁)).length = (macData (VG.Proof.ChaCha20Poly1305.Arm.A s₂) (VG.Proof.ChaCha20Poly1305.Arm.D s₂)).length := by
    obtain ⟨-, -, -, -, p3, -, a1, -, -⟩ := hpub
    rw [VG.Proof.ChaCha20Poly1305.Arm.length_macData, VG.Proof.ChaCha20Poly1305.Arm.length_macData]
    simp only [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20Poly1305.Arm.AL, VG.Proof.ChaCha20Poly1305.Arm.L, p3, a1]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) openMain fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFo s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFo s₂ b :=
    (RelCT.taint (A := taint) (VG.Proof.ChaCha20Poly1305.Arm.τ₀ false) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact VG.Proof.ChaCha20Poly1305.Arm.agree₀ hp₁ hp₂ hpub) (by taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.ChaCha20Poly1305.Arm.openMain_ok hp₁, VG.Proof.ChaCha20Poly1305.Arm.openMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFo s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PreFo s₂ b) finalize
      fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFo s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFo s₂ b :=
    (VG.Proof.ChaCha20Poly1305.Arm.frame_ct hp₁ hp₂ hpub (O := fun s => VG.Proof.ChaCha20Poly1305.Arm.ptr s tagOff) (VG.Proof.ChaCha20Poly1305.Arm.outOk_tag hp₁) (VG.Proof.ChaCha20Poly1305.Arm.outOk_tag hp₂)
      (by simp only [VG.Proof.ChaCha20Poly1305.Arm.ptr, VG.Proof.ChaCha20Poly1305.Arm.cP, hpub.2.2.2.2.2.2.2.2])
      fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨VG.Proof.ChaCha20Poly1305.Arm.finalize_open_ok hp₁ h.2.1, VG.Proof.ChaCha20Poly1305.Arm.finalize_open_ok hp₂ h.2.2⟩
  have B : RelCT isa (fun a b => True ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFo s₁ a ∧ VG.Proof.ChaCha20Poly1305.Arm.PostFo s₂ b) openEnd fun _ _ => True :=
    RelCT.taint (A := taint) VG.Proof.ChaCha20Poly1305.Arm.τB (fun a b h => VG.Proof.ChaCha20Poly1305.Arm.agreeB hp₁ hp₂ hpub h.2.1.inv h.2.2.inv) (by taint_decide)
  exact ((A.seq (F.seq B)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data): `key` at `0x1000`, `nonce` at `0x1100`, `aad` at `0x2000`, the stack
arguments at `0x5000`: `data` and `work` at 0, `tag` at `0x3000`. -/
def sealSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x1100 | .r2 => 0x2000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5009 then 0x30 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 16⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 632⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { VG.Proof.ChaCha20Poly1305.Arm.sealSat with
                 rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩, ⟨0x5000, 16⟩],
                 wr := [⟨0, 0⟩, ⟨0, 632⟩] }

theorem seal_ok (s : State) (hs : sealArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.Arm.«seal» s t s' ∧ abiPreserved s s' ∧
      sealArm.post s s' :=
  VG.Proof.ChaCha20Poly1305.Arm.seal_correct (APre.of s hs)

theorem open_ok (s : State) (hs : openArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.Arm.«open» s t s' ∧ abiPreserved s s' ∧
      openArm.post s s' :=
  VG.Proof.ChaCha20Poly1305.Arm.open_correct (APre.of s hs)

theorem seal_verified :
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.«seal» (sealScratchContract Arm.abi 79 8) :=
  Verified.of_correct VG.Proof.ChaCha20Poly1305.Arm.seal_ok VG.Proof.ChaCha20Poly1305.Arm.seal_ct (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealArm, Proof.ChaCha20Poly1305.preArm,
      Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.ChaCha20Poly1305.Arm.sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.ChaCha20Poly1305.Arm.sealSat)

/-- The postconditions match on `decrypt`; the result is the low word of
`r1:r0`. -/
theorem open_verified :
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.«open» (openScratchContract Arm.abi 79 8) :=
  Verified.of_correct VG.Proof.ChaCha20Poly1305.Arm.open_ok VG.Proof.ChaCha20Poly1305.Arm.open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        simp only [Proof.ChaCha20Poly1305.openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨(e _ _).trans h.1, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact (e _ _).trans h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
          [Proof.ChaCha20Poly1305.Arm.openSat, Proof.ChaCha20Poly1305.Arm.sealSat, Arm.stackArg,
            Arm.stackArgAddr, Mem.readW, Mem.read]
          using Proof.ChaCha20Poly1305.Arm.openSat }

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State :=
  { VG.Proof.ChaCha20Poly1305.Arm.sealSat with
                 rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 12⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.ChaCha20Poly1305.Arm.sealFrameSat

theorem seal_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«seal»)
      (Spec.ChaCha20Poly1305.sealContract Arm.abi 664) :=
  Arm.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 79) (post := Spec.ChaCha20Poly1305.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 656) (m := 3) (words := 158) VG.Proof.ChaCha20Poly1305.Arm.seal_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _) VG.Proof.ChaCha20Poly1305.Arm.sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { VG.Proof.ChaCha20Poly1305.Arm.sealSat with
                 rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩, ⟨0x5000, 12⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openContract Arm.abi 664).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.ChaCha20Poly1305.Arm.openFrameSat

theorem open_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«open»)
      (Spec.ChaCha20Poly1305.openContract Arm.abi 664) :=
  Arm.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 79) (post := Spec.ChaCha20Poly1305.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 656) (m := 3) (words := 158) VG.Proof.ChaCha20Poly1305.Arm.open_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (pre_local _ _) (openPost_local _) (openPost_out _) VG.Proof.ChaCha20Poly1305.Arm.openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.Arm

end
