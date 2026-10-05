import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.Arm.Frame
import VerifiedGarbage.Impl.AesCcm.Arm
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Frame
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Contract`. -/
section

/-!
# AES-CCM on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). `seal` and `open` call `vg_cmac_aes_update` and
`vg_aes_ctr32` in frames that push their two stack arguments below the stack
pointer, and `vg_cmac_aes_update`'s own frame uses the 8 bytes below that:
so the 16 bytes below the stack pointer (`bel16`) may not overlap any
buffer.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The 16 bytes below the stack pointer, which the calls use. -/
abbrev bel16 (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-- The arguments on the stack, `n` words of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 4 * n⟩

abbrev roundsOk (s : State) : Prop :=
  (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12],
tag = [sp + 16], tag_len = [sp + 20], work = [sp + 24])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 0), (VG.Proof.AesCcm.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 2), (VG.Proof.AesCcm.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 6), 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesCcm.Arm.args s 7) ∧ work.Disjoint (VG.Proof.AesCcm.Arm.args s 7) ∧
    (VG.Proof.AesCcm.Arm.bel16 s).Disjoint sch ∧ (VG.Proof.AesCcm.Arm.bel16 s).Disjoint nonce ∧ (VG.Proof.AesCcm.Arm.bel16 s).Disjoint aad ∧ (VG.Proof.AesCcm.Arm.bel16 s).Disjoint data ∧
    (VG.Proof.AesCcm.Arm.bel16 s).Disjoint work ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesCcm.Arm.arg s 0).toNat + (VG.Proof.AesCcm.Arm.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesCcm.Arm.arg s 2).toNat + (VG.Proof.AesCcm.Arm.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesCcm.Arm.arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 28 ≤ 2 ^ 32 ∧ VG.Proof.AesCcm.Arm.roundsOk s ∧
    valid (VG.Proof.AesCcm.Arm.arg s 5).toNat (s.gpr .r3).toNat (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat = true ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (VG.Proof.AesCcm.Arm.bel16 s).Disjoint tag ∧ (VG.Proof.AesCcm.Arm.arg s 4).toNat + (VG.Proof.AesCcm.Arm.arg s 5).toNat ≤ 2 ^ 32

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 0), (VG.Proof.AesCcm.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 2), (VG.Proof.AesCcm.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 6), 2560⟩
  s.rd = [sch, nonce, aad, VG.Proof.AesCcm.Arm.args s 7] ∧ s.wr = [data, tag, work] ∧ VG.Proof.AesCcm.Arm.oneLay s ∧ tag.Disjoint (VG.Proof.AesCcm.Arm.args s 7)

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 0), (VG.Proof.AesCcm.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 2), (VG.Proof.AesCcm.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 6), 2560⟩
  s.rd = [sch, nonce, aad, tag, VG.Proof.AesCcm.Arm.args s 7] ∧ s.wr = [data, work] ∧ VG.Proof.AesCcm.Arm.oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 7, VG.Proof.AesCcm.Arm.arg s₁ i = VG.Proof.AesCcm.Arm.arg s₂ i

/-- The cipher of the key schedule. -/
abbrev ciph (s : State) : Spec.Ccm.Cipher := VG.Spec.Ccm.ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- `vg_aes_ccm_seal`. -/
def sealArm : Contract isa where
  pre := VG.Proof.AesCcm.Arm.sealPre
  post s s' :=
    VG.Spec.Ccm.encryptWith (VG.Proof.AesCcm.Arm.ciph s) (VG.Proof.AesCcm.Arm.arg s 5).toNat
        (VG.Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 2)) (VG.Proof.AesCcm.Arm.arg s 3).toNat)
        (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 0)) (VG.Proof.AesCcm.Arm.arg s 1).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 2)) (VG.Proof.AesCcm.Arm.arg s 3).toNat, VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 4)) (VG.Proof.AesCcm.Arm.arg s 5).toNat)
  pub := VG.Proof.AesCcm.Arm.onePub

/-- What `vg_aes_ccm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  VG.Spec.Ccm.decryptWith (VG.Proof.AesCcm.Arm.ciph s) (VG.Proof.AesCcm.Arm.arg s 5).toNat
    (VG.Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 2)) (VG.Proof.AesCcm.Arm.arg s 3).toNat)
    (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 0)) (VG.Proof.AesCcm.Arm.arg s 1).toNat)
    (VG.Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 4)) (VG.Proof.AesCcm.Arm.arg s 5).toNat)

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesCcm.Arm.roundsOk s then [] else [if (VG.Proof.AesCcm.Arm.openRes s).isSome then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openArm : Contract isa where
  pre := VG.Proof.AesCcm.Arm.openPre
  post s s' :=
    match VG.Proof.AesCcm.Arm.openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 2)) (VG.Proof.AesCcm.Arm.arg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧ VG.Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 2)) (VG.Proof.AesCcm.Arm.arg s 3).toNat = VG.Spec.Ccm.zeros (VG.Proof.AesCcm.Arm.arg s 3).toNat
  pub s₁ s₂ := VG.Proof.AesCcm.Arm.onePub s₁ s₂ ∧ VG.Proof.AesCcm.Arm.openLeak s₁ = VG.Proof.AesCcm.Arm.openLeak s₂

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Env`. -/
section

/-!
# AES-CCM on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The key schedule (240 bytes
at `k`), the working space (2560 bytes at `w`) and the 16 bytes of stack
below `sp` that the calls use (`Lay`), all 32-bit pointers; what a state may
access (`Perm`); and the registers holding `k`, `w`, the number of rounds
and `q − 1`, and the stack pointer (`Env`). The pieces write the parts of
`W` in `mutR` (and the data, and the stack below `sp`), so our caller's
registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (covers_off in_off in_left covers_left covers_of_mem covers_prefix)

/-- The 16 bytes below `sp`. -/
abbrev blw (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 16, 16⟩

/-- The key schedule, `W` and the stack below `sp` used by the calls. -/
structure Lay (k w sp : BitVec 32) : Prop where
  kw : k.toNat + 240 ≤ 2 ^ 32
  ww : w.toNat + 2560 ≤ 2 ^ 32
  sp16 : 16 ≤ sp.toNat
  k_w : (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk_k : (VG.Proof.AesCcm.Arm.blw sp).Disjoint ⟨State.addr k, 240⟩
  stk_w : (VG.Proof.AesCcm.Arm.blw sp).Disjoint ⟨State.addr w, 2560⟩

/-- What a state may access. -/
structure Perm (k w : BitVec 32) (s : State) : Prop where
  k : Covers [⟨State.addr k, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨State.addr w, 2560⟩] s.wr

/-- The registers holding the rounds `R`, the key schedule, `q − 1` and `W`,
the stack pointer, and what the state may access. -/
structure Env (k w sp : BitVec 32) (R q1 : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  r9 : s.gpr .r9 = k
  r10 : s.gpr .r10 = BitVec.ofNat 32 q1
  r11 : s.gpr .r11 = w
  sp : s.sp = sp
  perm : VG.Proof.AesCcm.Arm.Perm k w s

theorem Perm.of_eq {k w : BitVec 32} {s s' : State} (h : VG.Proof.AesCcm.Arm.Perm k w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.Perm k w s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r8`–`r11`, `sp` and the permissions. -/
theorem Env.keep {k w sp : BitVec 32} {R q1 : Nat} {s s' : State} (h : VG.Proof.AesCcm.Arm.Env k w sp R q1 s)
    (hg : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.Env k w sp R q1 s' :=
  ⟨by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9], by rw [hg _ (by simp), h.r10],
    by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- After code that keeps the callee-saved registers (but `lr`). -/
theorem Env.of_saved {k w sp : BitVec 32} {R q1 : Nat} {s s' : State} (h : VG.Proof.AesCcm.Arm.Env k w sp R q1 s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.Env k w sp R q1 s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {k w sp : BitVec 32} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 2560) : State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d m : Nat} (h : a + n ≤ d ∨ d + m ≤ a) (ha : a + n ≤ 2560) (hd : d + m ≤ 2560) :
    (⟨State.addr w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, m⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem w0_w {n d m : Nat} (h : n ≤ d) (hd : d + m ≤ 2560) :
    (⟨State.addr w, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, m⟩ := by
  have := L.w_w (a := 0) (n := n) (d := d) (m := m) (.inl (by omega)) (by omega) hd
  simpa using this

theorem wN {d : Nat} (hd : d < 2560) : (w + BitVec.ofNat 32 d).toNat = w.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (VG.Proof.AesCcm.Arm.blw sp).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (VG.Proof.AesCcm.Arm.Lay.wSub ha)

theorem k_w' {a n : Nat} (ha : a + n ≤ 2560) :
    (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.k_w.sub_right (VG.Proof.AesCcm.Arm.Lay.wSub ha)

end Lay

namespace Perm

variable {k w : BitVec 32} {s : State} (P : VG.Proof.AesCcm.Arm.Perm k w s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (State.addr w + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (State.addr w + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr w + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at the 32-bit pointer `D` that the code may read,
apart from `W`, the key schedule and the stack below `sp`. -/
structure Buf (w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr)
  fit : D.toNat + n ≤ 2 ^ 32
  w : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (VG.Proof.AesCcm.Arm.blw sp).Disjoint ⟨State.addr D, n⟩

namespace Buf

variable {w sp : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesCcm.Arm.Buf w sp s D n)
include h

theorem lt32 : n ≤ 2 ^ 32 := by have := h.fit; omega

theorem lt : n < 2 ^ 64 := by have := h.fit; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.Buf w sp s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- Byte `j` of the buffer, for `j < n`, as a 64-bit address. -/
theorem addr {j : Nat} (hj : j < n) : State.addr (D + BitVec.ofNat 32 j) = State.addr D + BitVec.ofNat 64 j :=
  addr_add (by have := h.fit; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesCcm.Arm.Buf w sp s D k where
  rd := covers_prefix h.rd hk
  fit := by have := h.fit; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : VG.Proof.AesCcm.Arm.Buf w sp s (D + BitVec.ofNat 32 j) k := by
  have ha := h.addr (j := j) (by omega)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]; exact covers_off h.rd hjk h.lt
  · rw [h.toNat_add (by omega)]; have := h.fit; omega
  · rw [ha]; exact h.w.sub_left hs
  · rw [ha]; exact h.stk.sub_right hs

end Buf

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Compare`. -/
section

/-!
# AES-CCM on ARMv7: checking a received tag (`recv`, `cmp o`)

Untrusted: everything here is checked by Lean. These are AES-GCM's pieces
(`Proof/AesGcm/Arm/Compare.lean`), with AES-CCM's environment: `recv` pads
the `r6` bytes of the received tag at `tag` with zeros at `W + 256`
(`recv_ok`); `cmp o` pads the first `r6` bytes of the tag at `W + o` at
`W + 240` and leaves 1 in `r0` if they are the received ones, 0 if not
(`cmp_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok covers_left bytesAt_frame length_bytesAt
  bytesAt_writeBytes_prefix writeBytes_frame' store4_zero_tail bytes_words words_eq_iff cmp_value runBlock_app_of
  Keeps add_ofNat_assoc add_ofNat_zero mem_store store4_eq gpr_store rd_store wr_store sp_store z_store c_store
  gpr_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags z_subFlags c_subFlags store32_eq store8_eq
  encodable_of_decide sepW)

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- A copy of `tl` bytes from `W + o` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {S : BitVec 32} {o d tl : Nat}
    (hod : o + 16 ≤ d ∨ d + 16 ≤ o) (ho : o + 16 ≤ 2560) (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (hSa : State.addr S = State.addr w + BitVec.ofNat 64 o) (hSn : S.toNat = w.toNat + o) {m₀ : Mem}
    (hm : s.mem = store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (hr1 : s.gpr .r1 = S)
    (hr2 : s.gpr .r2 = w + BitVec.ofNat 32 d) (hr3 : s.gpr .r3 = BitVec.ofNat 32 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 d) 16 =
        bytesAt m₀ (State.addr w + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ s'.mem ∧ LoopOut s S (w + BitVec.ofNat 32 d) tl s' := by
  have eD := L.wA (d := d) (by omega)
  have ww := L.ww
  have lp : LoopPre s S (w + BitVec.ofNat 32 d) tl := by
    refine ⟨hr1, hr2, hr3, h1, by omega, by omega, by rw [L.wN (by omega)]; omega, ?_, ?_, ?_⟩
    · rw [hSa]; exact covers_left (he.perm.wC (by omega))
    · rw [eD]; exact he.perm.wC (by omega)
    · rw [hSa, eD]; exact L.w_w (by omega) (by omega) (by omega)
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm', lo⟩ => ?_
  rw [hm, hSa, eD] at hm'
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) :=
    Cmac.frame_store4 _ _ _ _ _
  have hx : bytesAt (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (State.addr w + BitVec.ofNat 64 o) tl =
      bytesAt m₀ (State.addr w + BitVec.ofNat 64 o) tl :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by omega) (by omega)) (by omega)
  rw [hx] at hm'
  have hlen := VG.Proof.AesGcm.Arm.length_bytesAt m₀ (State.addr w + BitVec.ofNat 64 o) tl
  refine ⟨?_, ?_, lo⟩
  · rw [hm', bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, store4_zero_tail _ _ h16]
  · rw [hm']
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- `zero16 d`: the 16 bytes at `W + d` zeroed. -/
theorem zero16_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {d : Nat} (hd : d + 16 ≤ 2560) (ed₁ : d + 12 < 4096) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 d) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r0 = 0 := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show d + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show d + 4 + 4 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show d + 8 + 4 ≤ 2560 by omega)
  have w₃ := he.perm.wW (show d + 12 + 4 ≤ 2560 by omega)
  have e₀ := L.wA (d := d) (by omega)
  have e₁ := L.wA (d := d + 4) (by omega)
  have e₂ := L.wA (d := d + 8) (by omega)
  have e₃ := L.wA (d := d + 12) (by omega)
  have o₀ : d < 4096 := by omega
  have o₁ : d + 4 < 4096 := by omega
  have o₂ : d + 8 < 4096 := by omega
  refine ⟨_, by simp only [zero16]; arun [h11, e₀, e₁, e₂, e₃, w₀, w₁, w₂, w₃, o₀, o₁, o₂, ed₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · intro r a; simp [gpr_setReg, a]
  · rfl
  · rfl
  · rfl
  · simp [gpr_setReg]

/-- `cmpTail`: `r0` is 1 iff the 16 bytes at `W + 240` and `W + 256` are equal. -/
theorem cmpTail_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) :
    ∃ s', runBlock isa cmpTail s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 240) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 240 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 244 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 248 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 252 + 4 ≤ 2560 by decide)
  have q₀ := he.perm.wR (show 256 + 4 ≤ 2560 by decide)
  have q₁ := he.perm.wR (show 260 + 4 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 264 + 4 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 268 + 4 ≤ 2560 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (240 + 4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (256 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)] s₂ =
      some s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s₂.gpr r) ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - ((s₂.gpr .r0 ||| (BitVec.ofNat 32 0 - s₂.gpr .r0)) >>> 31) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · intro r x y; simp [gpr_setReg, x, y]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show cmpTail = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

/-- A copy of `tl` bytes from `S`, apart from `W + d`, to `W + d`, which
holds 16 zero bytes. -/
theorem padCopyAny_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {S : BitVec 32} {d tl : Nat}
    (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hSr : Covers [⟨State.addr S, tl⟩] (s.rd ++ s.wr))
    (hSf : S.toNat + tl ≤ 2 ^ 32) (hSd : (⟨State.addr S, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 16⟩)
    {m₀ : Mem} (hm : s.mem = store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (hr1 : s.gpr .r1 = S)
    (hr2 : s.gpr .r2 = w + BitVec.ofNat 32 d) (hr3 : s.gpr .r3 = BitVec.ofNat 32 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 d) 16 =
        bytesAt m₀ (State.addr S) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ s'.mem ∧ LoopOut s S (w + BitVec.ofNat 32 d) tl s' := by
  have eD := L.wA (d := d) (by omega)
  have ww := L.ww
  have lp : LoopPre s S (w + BitVec.ofNat 32 d) tl := by
    refine ⟨hr1, hr2, hr3, h1, by omega, hSf, by rw [L.wN (by omega)]; omega, hSr, ?_, ?_⟩
    · rw [eD]; exact he.perm.wC (by omega)
    · rw [eD]; exact hSd.sub_right (Region.sub_prefix h16)
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm', lo⟩ => ?_
  rw [hm, eD] at hm'
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) :=
    Cmac.frame_store4 _ _ _ _ _
  have hx : bytesAt (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (State.addr S) tl =
      bytesAt m₀ (State.addr S) tl :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega)
  rw [hx] at hm'
  have hlen := VG.Proof.AesGcm.Arm.length_bytesAt m₀ (State.addr S) tl
  refine ⟨?_, ?_, lo⟩
  · rw [hm', bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, store4_zero_tail _ _ h16]
  · rw [hm']
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- `recv` (AES-GCM's): the received tag, the `r6` bytes at `T` (the stack
argument at `sp + 16`), padded with zeros at `W + 256`. -/
theorem recv_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {T : BitVec 32} {tl : Nat}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hTr : Covers [⟨State.addr T, tl⟩] (s.rd ++ s.wr)) (hTf : T.toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa recv s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr T) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₀, run₀, h1₀, g₀, k₀⟩ : ∃ s₀, runBlock isa [.ldrSp .r1 16] s = some s₀ ∧ s₀.gpr .r1 = T ∧
      (∀ r, r ≠ .r1 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by arun [hTi, hTv], ?_, ?_, ?_⟩
    · simp [gpr_setReg, hTv]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₀ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₀ _ (by decide)) k₀.sp k₀.rd k₀.wr
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := VG.Proof.AesCcm.Arm.zero16_ok L he₀ (d := rO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he₀.r11]
  obtain ⟨s₂, run₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r11 rO, .mov .r3 (.reg .r6)] s₁ = some s₂ ∧
      s₂.gpr .r2 = w + BitVec.ofNat 32 256 ∧ s₂.gpr .r3 = BitVec.ofNat 32 tl ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [rO]; arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), g₀ .r6 (by decide), h6]
    · intro r x y; simp [gpr_setReg, x, y]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have run : runBlock isa (.ldrSp .r1 16 :: zero16 rO ++ [addI .r2 .r11 rO, .mov .r3 (.reg .r6)]) s = some s₂ :=
    runBlock_app_of (a := [.ldrSp .r1 16]) run₀ (runBlock_app_of run₁ run₂)
  refine WP.seq (WP.of_runBlock ⟨s₂, run, ?_⟩)
  have he₂ := he₀.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have h1₂ : s₂.gpr .r1 = T := by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h1₀]
  have hTr₂ : Covers [⟨State.addr T, tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [k₂.rd, k₂.wr, rd₁, wr₁, k₀.rd, k₀.wr]; exact hTr
  refine WP.mono (VG.Proof.AesCcm.Arm.padCopyAny_ok L he₂ (d := 256) (by decide) h1 h16 hTr₂ hTf hTd (m₀ := s.mem)
    (by rw [k₂.mem, hm₁, k₀.mem]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_
  refine ⟨hb, hf, fun r a b d e f => ?_, lo.rd.trans (k₂.rd.trans (rd₁.trans k₀.rd)),
    lo.wr.trans (k₂.wr.trans (wr₁.trans k₀.wr)), lo.sp.trans (k₂.sp.trans (sp₁.trans k₀.sp))⟩
  rw [lo.other r a b d e f, g₂ r d e, g₁ r a, g₀ r b]

/-- `cmp o`: the first `r6` bytes of the tag at `W + o`, padded with zeros at
`W + 240`, compared with the received tag at `W + 256`. -/
theorem cmp_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {o : Nat} (ho : o = 0 ∨ o = 112) {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa (cmp o) s fun s' => s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := VG.Proof.AesCcm.Arm.zero16_ok L he (d := vO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have eo : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 o, addI .r2 .r11 vO,
      .mov .r3 (.reg .r6)] s₁ = some s₂ ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 o ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 240 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [vO]; arun [eo], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), h6]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, runBlock_app_of run₁ run₂, ?_⟩)
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.padCopy_ok L he₂ (o := o) (d := 240) (by omega) (by omega) (by decide) h1 h16
    (L.wA (by omega)) (L.wN (by omega)) (m₀ := s.mem) (by rw [k₂.mem, hm₁]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := VG.Proof.AesCcm.Arm.cmpTail_ok L he₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_, ?_, fun r a b d e f => ?_, k₄.rd.trans (lo.rd.trans (k₂.rd.trans rd₁)),
    k₄.wr.trans (lo.wr.trans (k₂.wr.trans wr₁)), k₄.sp.trans (lo.sp.trans (k₂.sp.trans sp₁))⟩
  · have h256 : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 :=
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [h0₄, hb, h256]
  · rw [k₄.mem]; exact hf
  · rw [g₄ r a b d, lo.other r a b d e f, g₂ r b d e, g₁ r a]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Words`. -/
section

/-!
# AES-CCM on ARMv7: words as bytes

Untrusted: everything here is checked by Lean. The bytes (`le4`, least
significant first) of the words the pieces store: a byte-reversed integer
is its big-endian bytes (`le4_rev_ofNat`), and shifts by 16 move two bytes
(`le4_shr16`, `le4_shl16`), which `header` uses for the encodings of the
length of the associated data.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.Cmac (le4)

theorem le4_eq (a : BitVec 32) :
    le4 a = [a.extractLsb' 0 8, a.extractLsb' 8 8, a.extractLsb' 16 8, a.extractLsb' 24 8] := rfl

theorem le4_rev (a : BitVec 32) : le4 (rev a) = (le4 a).reverse := by
  have e : ∀ k < 4, (rev a).extractLsb' (8 * k) 8 = a.extractLsb' (8 * (3 - k)) 8 := fun k hk => by
    ext j hj
    simp only [BitVec.getElem_extractLsb']
    exact rev_bit _ hk hj
  rw [VG.Proof.AesCcm.Arm.le4_eq, VG.Proof.AesCcm.Arm.le4_eq, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rfl

theorem extract_ofNat {i k : Nat} :
    (BitVec.ofNat 32 i).extractLsb' k 8 = BitVec.ofNat 8 (i % 2 ^ 32 / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem le4_ofNat {i : Nat} (hi : i < 2 ^ 32) : le4 (BitVec.ofNat 32 i) = (Spec.Ccm.be 4 i).reverse := by
  rw [VG.Proof.AesCcm.Arm.le4_eq, VG.Proof.AesCcm.Arm.extract_ofNat, VG.Proof.AesCcm.Arm.extract_ofNat, VG.Proof.AesCcm.Arm.extract_ofNat,
    VG.Proof.AesCcm.Arm.extract_ofNat, Nat.mod_eq_of_lt hi]
  simp [Spec.Ccm.be, List.range_succ]

/-- A byte-reversed integer is its big-endian bytes. -/
theorem le4_rev_ofNat {i : Nat} (hi : i < 2 ^ 32) : le4 (rev (BitVec.ofNat 32 i)) = Spec.Ccm.be 4 i := by
  rw [VG.Proof.AesCcm.Arm.le4_rev, VG.Proof.AesCcm.Arm.le4_ofNat hi, List.reverse_reverse]

theorem le4_shr16 (a : BitVec 32) : le4 (a >>> 16) = (le4 a).drop 2 ++ Spec.Ccm.zeros 2 := by
  have e : ∀ k < 4, (a >>> 16).extractLsb' (8 * k) 8 =
      if k < 2 then a.extractLsb' (8 * (k + 2)) 8 else 0 := fun k hk => by
    ext j hj
    simp only [BitVec.getElem_extractLsb']
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [BitVec.getLsbD_ushiftRight] <;>
      first | rfl | (apply BitVec.getLsbD_of_ge; omega) | (congr 1; omega)
  rw [VG.Proof.AesCcm.Arm.le4_eq (a >>> 16), e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), VG.Proof.AesCcm.Arm.le4_eq]
  rfl

theorem le4_shl16 (a : BitVec 32) : le4 (a <<< 16) = Spec.Ccm.zeros 2 ++ (le4 a).take 2 := by
  have e : ∀ k < 4, (a <<< 16).extractLsb' (8 * k) 8 =
      if k < 2 then 0 else a.extractLsb' (8 * (k - 2)) 8 := fun k hk => by
    ext j hj
    simp only [BitVec.getElem_extractLsb']
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [BitVec.getLsbD_shiftLeft] <;>
      first | rfl | (intro; omega) |
        (rw [decide_eq_true (by omega : 24 + j < 32), decide_eq_false (by omega : ¬ 24 + j < 16)]
         simp only [Bool.true_and, Bool.not_false]; congr 1; omega)
  rw [VG.Proof.AesCcm.Arm.le4_eq (a <<< 16), e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), VG.Proof.AesCcm.Arm.le4_eq]
  rfl

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Ctrs`. -/
section

/-!
# AES-CCM on ARMv7: `Ctr₀` (`ctrs`)

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte (and to `r10`) and copies
the nonce after it: `Ctr₀` (`ctrs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok covers_left bytesAt_frame
  mem_store store8_eq store32_eq gpr_store rd_store wr_store sp_store encodable_of_decide)

theorem store4_zero_bytes' (m : Mem) (p : Addr) : bytesAt (store4 m p 0 0 0 0) p 16 = Spec.Ccm.zeros 16 := by
  rw [Proof.Cmac.bytesAt_store4]; decide

/-- The bytes of `Ctr₀`, as `ctrs` builds them. -/
theorem ctr0_list (xs : List Byte) (h13 : xs.length ≤ 13) :
    ((BitVec.ofNat 8 (14 - xs.length) :: (Spec.Ccm.zeros 16).drop 1).take 1 ++ xs ++
      (BitVec.ofNat 8 (14 - xs.length) :: (Spec.Ccm.zeros 16).drop 1).drop (1 + xs.length)) =
      Spec.Ccm.ctrBlock xs 0 := by
  rw [Spec.Ccm.ctrBlock, be_zero, show 15 - xs.length - 1 = 14 - xs.length by omega,
    show 1 + xs.length = xs.length + 1 by omega, List.drop_succ_cons, List.take_succ_cons, List.take_zero]
  simp only [Spec.Ccm.zeros, List.drop_replicate, List.cons_append, List.nil_append]

theorem setWidth_ofNat8 {x : Nat} (_h : x < 256) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega)]

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 32 by omega)]
  omega

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- `ctrs`: `Ctr₀` for the `nl`-byte nonce at `N` in the block at `W + 48`,
and `q − 1` in `r10`. -/
theorem ctrs_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {N : BitVec 32} {nl : Nat} (hN : VG.Proof.AesCcm.Arm.Buf w sp s N nl)
    (h2 : s.gpr .r2 = N) (h3 : s.gpr .r3 = BitVec.ofNat 32 nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa ctrs s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 48) 16 =
        Spec.Ccm.ctrBlock (bytesAt s.mem (State.addr N) nl) 0 ∧
      s'.gpr .r10 = BitVec.ofNat 32 (14 - nl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := VG.Proof.AesCcm.Arm.zero16_ok L he (d := c0O) (by decide) (by decide)
  simp only [c0O] at hm₁
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have wB := (he.perm.of_eq rd₁ wr₁).wW (show 48 + 1 ≤ 2560 by decide)
  have e48 := L.wA (d := 48) (by decide)
  have e49 := L.wA (d := 49) (by decide)
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, h10₂, hm₂, g₂, rd₂, wr₂, sp₂⟩ : ∃ s₂, runBlock isa [.mov .r10 (imm 14),
      .dp .sub .r10 .r10 (.reg .r3), .strb .r10 .r11 c0O, .mov .r1 (.reg .r2), addI .r2 .r11 (c0O + 1)] s₁ = some s₂ ∧
      s₂.gpr .r1 = N ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 49 ∧ s₂.gpr .r3 = BitVec.ofNat 32 nl ∧
      s₂.gpr .r10 = BitVec.ofNat 32 (14 - nl) ∧
      s₂.mem = s₁.mem.writeW (State.addr w + BitVec.ofNat 64 48) (BitVec.ofNat 8 (14 - nl)) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r10 → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      s₂.sp = s₁.sp := by
    have g3 : s₁.gpr .r3 = BitVec.ofNat 32 nl := by rw [g₁ _ (by decide), h3]
    have e14 : BitVec.ofNat 32 14 - BitVec.ofNat 32 nl = BitVec.ofNat 32 (14 - nl) :=
      VG.Proof.AesCcm.Arm.sub_ofNat32 (by omega) (by decide)
    refine ⟨_, by simp only [c0O]; arun [h11, g3, e48, wB], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, g₁ .r2 (by decide), h2]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g3]
    · simp [gpr_setReg, e14]
    · simp [mem_setReg, gpr_setReg, e14, VG.Proof.AesCcm.Arm.setWidth_ofNat8 (show 14 - nl < 256 by omega)]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  have hN₂ : VG.Proof.AesCcm.Arm.Buf w sp s₂ N nl := hN.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have lp : LoopPre s₂ N (w + BitVec.ofNat 32 49) nl := by
    refine ⟨h1₂, h2₂, h3₂, by omega, by omega, hN.fit, by rw [L.wN (by decide)]; have := L.ww; omega,
      hN₂.rd, ?_, ?_⟩
    · rw [e49]; exact (he.perm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])).wC (by omega)
    · rw [e49]; exact hN.w.sub_right (Lay.wSub (by omega))
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show (zero16 c0O ++ [.mov .r10 (imm 14), .dp .sub .r10 .r10 (.reg .r3), .strb .r10 .r11 c0O,
      .mov .r1 (.reg .r2), addI .r2 .r11 (c0O + 1)]) = zero16 c0O ++ [.mov .r10 (imm 14),
      .dp .sub .r10 .r10 (.reg .r3), .strb .r10 .r11 c0O, .mov .r1 (.reg .r2), addI .r2 .r11 (c0O + 1)] from rfl]
    exact Proof.AesGcm.Arm.runBlock_app_of run₁ run₂, ?_⟩)
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  -- The nonce is as on entry: only `W + 48` was written.
  have fW : Frame [⟨State.addr w + BitVec.ofNat 64 48, 16⟩] s.mem s₂.mem := by
    rw [hm₂, hm₁]
    refine (Proof.Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have nN : bytesAt s₂.mem (State.addr N) nl = bytesAt s.mem (State.addr N) nl :=
    bytesAt_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hN.w.sub_right (Lay.wSub (by decide))) (by omega)
  rw [nN, e49] at hm₃
  have hlen := length_bytesAt s.mem (State.addr N) nl
  refine ⟨?_, ?_, ?_, ?_, lo.rd.trans (rd₂.trans rd₁), lo.wr.trans (wr₂.trans wr₁), lo.sp.trans (sp₂.trans sp₁)⟩
  · rw [hm₃, show State.addr w + BitVec.ofNat 64 49 = (State.addr w + BitVec.ofNat 64 48) + BitVec.ofNat 64 1 by
      rw [Offset.add_add]]
    rw [bytesAt_writeBytes_at _ _ _ (by rw [hlen]; omega) (by decide), hm₂,
      bytesAt_writeW8_base _ _ _ (by decide) (by decide), hm₁, VG.Proof.AesCcm.Arm.store4_zero_bytes']
    have := VG.Proof.AesCcm.Arm.ctr0_list (bytesAt s.mem (State.addr N) nl) (by rw [hlen]; exact h13)
    rw [hlen] at this
    rw [hlen]; exact this
  · rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h10₂]
  · rw [hm₃]
    refine fW.trans ((VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨State.addr w + BitVec.ofNat 64 49, nl⟩) ?_).sub
      fun r hr => ?_)
    · rw [hlen]; exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  · intro r a b c d e f
    rw [lo.other r a b c d f, g₂ r b c e, g₁ r a]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.CtrAt`. -/
section

/-!
# AES-CCM on ARMv7: a counter block `Ctrᵢ` (`ctrAt`)

Untrusted: everything here is checked by Lean. `ctrAt` copies `Ctr₀` from
`W + 48` to `W + 64`, its last word ORed with `[i]₃₂` (`rev` of `i`, in
`r0`): `Ctrᵢ`, for `i < 2^(8 min(q, 4))` (`ctrAt_ok`,
`Proof.AesCcm.ctrBlock_split`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (mem_store store32_eq gpr_store rd_store wr_store sp_store encodable_of_decide sepW
  bytes_words store4_eq add_ofNat_assoc)

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- `ctrAt`: `Ctrᵢ` at `W + 64`, from `Ctr₀` at `W + 48`. -/
theorem ctrAt_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (h13 : nonce.length ≤ 13) (hc : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {i : Nat} (h0 : s.gpr .r0 = BitVec.ofNat 32 i) (hi : i < 256 ^ min (15 - nonce.length) 4) :
    ∃ s', runBlock isa ctrAt s = some s' ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have hi4 : i < 2 ^ 32 := Nat.lt_of_lt_of_le hi (by
    rw [show (2 : Nat) ^ 32 = 256 ^ 4 from rfl]; exact Nat.pow_le_pow_right (by decide) (by omega))
  have r₀ := he.perm.wR (show 48 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 52 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 56 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 60 + 4 ≤ 2560 by decide)
  have w₀ := he.perm.wW (show 64 + 4 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 68 + 4 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 72 + 4 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 76 + 4 ≤ 2560 by decide)
  have q : ∀ a d, a + 4 ≤ d → d + 4 ≤ 2560 →
      (⟨State.addr w + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ => L.w_w (.inl h₁) (by omega) h₂
  have p₁ := fun m v => sepW (m := m) (v := v) (q 52 64 (by decide) (by decide))
  have p₂ := fun m v => sepW (m := m) (v := v) (q 56 64 (by decide) (by decide))
  have p₃ := fun m v => sepW (m := m) (v := v) (q 56 68 (by decide) (by decide))
  have p₄ := fun m v => sepW (m := m) (v := v) (q 60 64 (by decide) (by decide))
  have p₅ := fun m v => sepW (m := m) (v := v) (q 60 68 (by decide) (by decide))
  have p₆ := fun m v => sepW (m := m) (v := v) (q 60 72 (by decide) (by decide))
  have e := fun d (hd : d < 2560) => L.wA (d := d) hd
  let m := s.mem
  let W := State.addr w
  have hm : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = store4 m (W + BitVec.ofNat 64 64) (m.readW (W + BitVec.ofNat 64 48) 32)
        (m.readW (W + BitVec.ofNat 64 52) 32) (m.readW (W + BitVec.ofNat 64 56) 32)
        (m.readW (W + BitVec.ofNat 64 60) 32 ||| rev (BitVec.ofNat 32 i)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [ctrAt, c0O, c1O]; arun [h11, h0, e, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃,
      p₄, p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc, m, W]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals exact ⟨rfl, rfl, rfl⟩
  obtain ⟨s', run, hm', g, rd, wr, sp⟩ := hm
  refine ⟨s', run, ?_, by rw [hm']; exact Proof.Cmac.frame_store4 _ _ _ _ _, g, rd, wr, sp⟩
  -- The words of `Ctr₀`.
  have hw := hc
  rw [bytes_words] at hw
  simp only [add_ofNat_assoc] at hw
  have l := Proof.Cmac.length_le4
  have hl : (le4 (m.readW (W + BitVec.ofNat 64 48) 32) ++ le4 (m.readW (W + BitVec.ofNat 64 52) 32) ++
      le4 (m.readW (W + BitVec.ofNat 64 56) 32)).length = 12 := by simp [l]
  rw [hm', Proof.Cmac.bytesAt_store4, ctrBlock_split h7 h13 hi, ← hw, le4_or, VG.Proof.AesCcm.Arm.le4_rev_ofNat hi4,
    List.take_left' hl, List.drop_left' hl]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Callee`. -/
section

/-!
# AES-CCM on ARMv7: the calls of `vg_cmac_aes_update`

Untrusted: everything here is checked by Lean. As streaming AES-CMAC's
(`Proof/CmacAes/Stream/Arm/Call.lean`, `upd_call`, `upd_rel`), but with the
two stack arguments pushed from `r12` (the number of blocks) and `lr` (the
working space), which `seal` and `open` do not keep across calls: what a
call needs (`UArgs`), what it leaves (`UPost`), and that two calls with the
same arguments leak the same (`upd_rel`). The calls of `vg_aes_ctr32` are
AES-GCM's (`Proof.AesGcm.Arm.ctr_call`, `ctr_rel`).
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.CmacAes.Stream.Arm (view blw16 view_gpr view_sp view_arg0 view_arg1 view_argAddr view_blw spA
  slot_sub push_frame cov_push covW_push WP.frameCallF RelCT.frameCall stackUse_update uRd uWr)
open VG.Proof.CmacAes.Arm (toNat_rounds)

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`, with `n` in `r12` and `S` in `lr`, to push. -/
structure UArgs (s : State) (W C D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 32
  hsp : 16 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  dc : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (blw16 s).Disjoint ⟨State.addr W, 240⟩
  bd : (blw16 s).Disjoint ⟨State.addr D, 16 * n⟩
  bc : (blw16 s).Disjoint ⟨State.addr C, 16⟩
  bs : (blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩, blw16 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr C) 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16) (Spec.Cmac.blocksAt s.mem (State.addr D) 16 n)

theorem UArgs.pre {s : State} {W C D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesCcm.Arm.UArgs s W C D S R n) :
    Proof.CmacAes.Arm.updateArm.pre (view .r12 .lr s (uRd s W D n) (uWr C S)) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega)
  have hb := view_blw (ra := .r12) (rb := .lr) (rd := uRd s W D n) (wr := uWr C S) h.hsp
  have hslot : Region.Sub ⟨stackArgAddr (view .r12 .lr s (uRd s W D n) (uWr C S)) 0, 8⟩ (blw16 s) := by
    rw [view_argAddr h.hsp]; exact slot_sub
  simp only [Proof.CmacAes.Arm.updateArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, hR, hN, State.withRegions_rd, State.withRegions_wr]
  rw [view_argAddr h.hsp] at hslot
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, (h.bc.sub_left slot_sub).symm,
    (h.bs.sub_left slot_sub).symm, h.bw.sub_left hb, h.bd.sub_left hb, h.bc.sub_left hb, h.bs.sub_left hb,
    h.fW, h.fC, h.fD, h.fS, ?_, ?_, h.rounds⟩
  · rw [view_sp, hspv]; omega
  · rw [view_sp, hspv]; have := s.sp.isLt; omega

theorem upd_call {s : State} {W C D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesCcm.Arm.UArgs s W C D S R n) :
    WP isa Impl.AesCcm.Arm.updFrame s (VG.Proof.AesCcm.Arm.UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.updateArm) (fun _ hs => Proof.CmacAes.Arm.update_wp hs)
    stackUse_update rfl h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bc
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := push_frame h.hsp .r12 .lr
  have keep : ∀ {p : Addr} {k : Nat}, (blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  simp only [Proof.CmacAes.Arm.updateArm, Proof.CmacAes.Arm.ciphAt, view_arg0 h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, hR, hN, State.withRegions_mem, State.callEntry_mem] at hpost
  rw [hm, hpost, keep (h.bw.sub_right (Region.sub_prefix hRb)) (by omega), keep h.bc (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep (h.bd.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega

theorem upd_rel {W C D S sp₀ : BitVec 32} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.Arm.UArgs s₁ W C D S R n ∧ VG.Proof.AesCcm.Arm.UArgs s₂ W C D S R n ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Impl.AesCcm.Arm.updFrame fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.updateArm) (rd := [⟨State.addr W, 240⟩,
    ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := uWr C S)
    (fun _ hs => Proof.CmacAes.Arm.update_wp hs) Proof.CmacAes.Arm.update_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : uRd s₁ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₁]
  have r₂ : uRd s₂ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := cov_push (ra := .r12) (rb := .lr) h₁.hsp h₁.reads h₁.writes
  have c₂ := cov_push (ra := .r12) (rb := .lr) h₂.hsp h₂.reads h₂.writes
  rw [e₁] at c₁
  rw [e₂] at c₂
  have := h₁.hsp
  refine ⟨e₁.trans e₂.symm, by omega, by have := h₂.hsp; omega, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂,
    covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.updateArm, view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide),
    view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12,
    h₂.lr, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Tag`. -/
section

/-!
# AES-CCM on ARMv7: the tag (`tag y`)

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32`
take the key schedule, the counter block at `W + 64` and the working space at
`W + 384` from the environment (`ctrCall_of`), and blocks apart from those.
`tag y` makes `Ctr₀` at `W + 64` and calls `vg_aes_ctr32` on the MAC state at
`W + y`, one block: the state XORed with `CIPH_K(Ctr₀)`, CCM's keystream
from `Ctr₀` (`tag_ok`), whose first `t` bytes are the MAC encrypted
(`Proof.AesCcm.take_xorFrom_zero`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below mem_store gpr_store rd_store wr_store sp_store
  encodable_of_decide runBlock_app_of covers_left covers_of_mem covers_cons bytesAt_frame)
open VG.Proof.AesCcm (xorFrom ctr32_ccm)

theorem below_blw (sp : BitVec 32) : Region.Sub (below sp) (VG.Proof.AesCcm.Arm.blw sp) :=
  Offset.sub_below (State.addr sp) (a := 8) (b := 16) (by decide) (by decide)

/-- The working space of the callees, at `W + 384`. -/
abbrev scrR (w : BitVec 32) : Region := ⟨State.addr w + BitVec.ofNat 64 384, 2176⟩

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- A call of `vg_aes_ctr32` with the key schedule, the counter block at
`W + 64`, `n` blocks at `D` and the working space at `W + 384`. -/
theorem ctrCall_of {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32}
    {n : Nat} (h0 : s.gpr .r0 = k) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 64)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 384)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (dK : (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (dC : (⟨State.addr w + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 384, 2048⟩)
    (dB : (VG.Proof.AesCcm.Arm.blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (wD : Covers [⟨State.addr D, 16 * n⟩] s.wr) :
    CtrCall s k (w + BitVec.ofNat 32 64) D (w + BitVec.ofNat 32 384) R n := by
  have e64 := L.wA (d := 64) (by decide)
  have e384 := L.wA (d := 384) (by decide)
  have hsp := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hsp]; have := L.sp16; omega, L.kw,
    by rw [L.wN (by decide)]; have := L.ww; omega, fD, by rw [L.wN (by decide)]; have := L.ww; omega, ?_, dK,
    ?_, by rw [e64]; exact dC, ?_, by rw [e384]; exact dS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e64]; exact L.k_w' (by decide)
  · rw [e384]; exact L.k_w' (by decide)
  · rw [e64, e384]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [hsp]; exact L.stk_k.sub_left (VG.Proof.AesCcm.Arm.below_blw sp)
  · rw [hsp, e64]; exact (L.stk_w' (by decide)).sub_left (VG.Proof.AesCcm.Arm.below_blw sp)
  · rw [hsp]; exact dB.sub_left (VG.Proof.AesCcm.Arm.below_blw sp)
  · rw [hsp, e384]; exact (L.stk_w' (by decide)).sub_left (VG.Proof.AesCcm.Arm.below_blw sp)
  · exact he.perm.k
  · rw [e64, e384]
    exact covers_cons (he.perm.wC (by decide)) (covers_cons wD (he.perm.wC (by decide)))

/-- `Ctr₀` at `W + 64`, and the arguments of the call in `tag y`. -/
theorem tagArgs_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    ∃ s₃, runBlock isa (([.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] : List Instr) ++ ctrAt ++ ctrArgs ++
        ([VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)] : List Instr)) s = some s₃ ∧
      CtrCall s₃ k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 y) (w + BitVec.ofNat 32 384) R 1 ∧
      VG.Proof.AesCcm.Arm.Env k w sp R q1 s₃ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₃.gpr r = s.gpr r) ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr ∧ s₃.sp = s.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  have h8 := he.r8; have h9 := he.r9; have h11 := he.r11
  -- `r0 := 0`.
  obtain ⟨s₁, run₁, h0₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] s = some s₁ ∧
      s₁.gpr .r0 = BitVec.ofNat 32 0 ∧ (∀ r, r ≠ .r0 → s₁.gpr r = s.gpr r) ∧
      (s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp) := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.2.2.2 k₁.2.1 k₁.2.2.1
  obtain ⟨s₂, run₂, hc₂, f₂, g₂, rd₂, wr₂, sp₂⟩ := VG.Proof.AesCcm.Arm.ctrAt_ok L he₁ h7 h13 (by rw [k₁.1]; exact hc0) h0₁
    (Nat.pow_pos (by decide))
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) sp₂ rd₂ wr₂
  have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
  obtain ⟨s₃, run₃, a0, a1, a2, a3, a12, alr, g₃, k₃⟩ : ∃ s₃, runBlock isa (ctrArgs ++
      [VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)]) s₂ = some s₃ ∧
      s₃.gpr .r0 = k ∧ s₃.gpr .r1 = BitVec.ofNat 32 R ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 64 ∧
      s₃.gpr .r3 = w + BitVec.ofNat 32 y ∧ s₃.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₃.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₃.gpr r = s₂.gpr r) ∧
      (s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.sp = s₂.sp) := by
    refine ⟨_, by simp only [ctrArgs, c1O, scrO]; arun [he₂.r9, he₂.r8, he₂.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₂.r9]
    · simp [gpr_setReg, he₂.r8]
    · simp [gpr_setReg, he₂.r11]
    · simp [gpr_setReg, he₂.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₂.r11]
    · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) k₃.2.2.2 k₃.2.1 k₃.2.2.1
  have eY := L.wA (d := y) (by omega)
  have hqc : (⟨State.addr w + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16 * 1⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have C₃ := VG.Proof.AesCcm.Arm.ctrCall_of L he₃ hR (n := 1) a0 a1 a2 a3 a12 alr (by rw [L.wN (by omega)]; have := L.ww; omega)
    (by rw [eY]; exact L.k_w' (by omega)) (by rw [eY]; exact hqc)
    (by rw [eY]; exact L.w_w (.inl (by omega)) (by omega) (by decide))
    (by rw [eY]; exact L.stk_w' (by omega)) (by rw [eY]; exact he₃.perm.wC (by omega))
  refine ⟨s₃, by
    rw [show [.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] ++ ctrAt ++ ctrArgs ++
      [VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)] =
      [.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] ++ (ctrAt ++ (ctrArgs ++
      [VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)])) by simp]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃), C₃, he₃, fun r a b c d e f => by rw [g₃ r a b c d e f, g₂ r a b, g₁ r a],
    by rw [k₃.2.1, rd₂, k₁.2.1], by rw [k₃.2.2.1, wr₂, k₁.2.2.1], by rw [k₃.2.2.2, sp₂, k₁.2.2.2],
    by rw [k₃.1, ← k₁.1]; exact f₂, by rw [k₃.1]; exact hc₂⟩

/-- The MAC state at `W + y` XORed with `CIPH_K(Ctr₀)`. -/
theorem tag_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (tag y) s fun s' => VG.Proof.AesCcm.Arm.Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩, ⟨State.addr w + BitVec.ofNat 64 y, 16⟩, VG.Proof.AesCcm.Arm.scrR w,
        VG.Proof.AesCcm.Arm.blw sp] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem (State.addr k) R) nonce 0
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16) := by
  obtain ⟨s₃, run₃, C₃, he₃, g₃, rd₃, wr₃, sp₃, f₀₃, hc₂⟩ := VG.Proof.AesCcm.Arm.tagArgs_ok L he hR h7 h13 hc0 hy
  have eY := L.wA (d := y) (by omega)
  have hqc : (⟨State.addr w + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16 * 1⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (ctr_call C₃) fun s₄ h => ?_
  have hsp₃ : s₃.sp = sp := he₃.sp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  -- Memory before the call: only `W + 64` changed.
  have hK₃ : Spec.Ccm.ctxCiph s₃.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R := by
    simp only [Spec.Ccm.ctxCiph]
    rw [bytesAt_frame f₀₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w' (by decide)).sub_left (Region.sub_prefix hRb)) (by omega)]
  have hY₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 y) 16 = bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
    bytesAt_frame f₀₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hqc.symm) (by decide)
  refine ⟨he₃.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, rd₃], by rw [h.wr, wr₃], fun r hr hlr => ?_, ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h.saved r hr hlr, g₃ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · have f₄ := h.frame
    rw [hsp₃, State.addr, ← State.addr, show State.addr (w + BitVec.ofNat 32 64) = _ from L.wA (by decide),
      eY, show State.addr (w + BitVec.ofNat 32 384) = _ from L.wA (by decide)] at f₄
    refine (f₀₃.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (f₄.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.AesCcm.Arm.scrR w, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.AesCcm.Arm.blw sp, by simp, VG.Proof.AesCcm.Arm.below_blw sp⟩
  · have hc := ctr32_ccm (m := s₃.mem) (m' := s₄.mem) (K := State.addr k) (C := State.addr (w + BitVec.ofNat 32 64))
      (D := State.addr (w + BitVec.ofNat 32 y)) (R := R) (nonce := nonce) (by omega) (j := 0) (k := 1)
      (fun i hi => by
        rw [show i = 0 by omega, Nat.zero_add]
        show Spec.Gcm.ofBytes _ = _
        rw [L.wA (by decide), hc₂]) h.out
    rw [Nat.mul_one, eY] at hc
    rw [hc, hK₃, hY₃]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Absorb`. -/
section

/-!
# AES-CCM on ARMv7: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` take the key schedule, the MAC state at `W + y` and
the working space at `W + 384` from the environment (`updCall_of`).
`updBlock y` chains `B` (at `W + 32`) into the MAC state (`updBlock_ok`);
`absorbPad y` chains the `len` bytes at `P`, padded with zeros to whole
blocks: its whole blocks in one call (`absorbWhole_ok`), then its last
`len mod 16` bytes copied into the zeroed `B` (`absorbTail_ok`); together,
the blocks of the padded string (`absorbPad_ok`,
`Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok covers_cons covers_left bytesAt_frame
  runBlock_app_of and15 shr4 toNat32 ofNat_sub32 z_cmp eval_eq' Keeps z_subFlags gpr_subFlags)
open VG.Proof.CmacAes.Stream.Arm (blw16)
open VG.Proof.AesCcm (ctxCiph_frame bytesAt_prefix bytesAt_suffix bytesAt_writeBytes_base length_bytesAt)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B`, the
working space of the functions called and the stack below `sp`. -/
abbrev macR (w sp : BitVec 32) (y : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 y, 16⟩, ⟨State.addr w + BitVec.ofNat 64 32, 16⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp]

theorem blw16_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) : blw16 s = VG.Proof.AesCcm.Arm.blw sp := by
  subst h; rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- What `absorbPad`'s pieces keep: the environment, the registers holding
the string, and what they write. -/
structure Absorbed (k w sp : BitVec 32) (R q1 : Nat) (s : State) (y : Nat) (P : BitVec 32) (len : Nat)
    (Y : List Byte) (s' : State) : Prop where
  env : VG.Proof.AesCcm.Arm.Env k w sp R q1 s'
  r4 : s'.gpr .r4 = P
  r5 : s'.gpr .r5 = BitVec.ofNat 32 len
  frame : Frame (VG.Proof.AesCcm.Arm.macR w sp y) s.mem s'.mem
  out : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- A call of `vg_cmac_aes_update` with the key schedule, the MAC state at
`W + y`, `n` blocks at `D` and the working space at `W + 384`. -/
theorem updCall_of {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y + 16 ≤ 384) {D : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) (fD : D.toNat + 16 * n ≤ 2 ^ 32)
    (dC : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint (VG.Proof.AesCcm.Arm.scrR w))
    (dB : (VG.Proof.AesCcm.Arm.blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (rD : Covers [⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr))
    (h0 : s.gpr .r0 = k) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 y)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 384) :
    VG.Proof.AesCcm.Arm.UArgs s k (w + BitVec.ofNat 32 y) D (w + BitVec.ofNat 32 384) R n := by
  have eY := L.wA (d := y) (by omega)
  have e384 := L.wA (d := 384) (by decide)
  have hb := VG.Proof.AesCcm.Arm.blw16_eq he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, hn, by rw [he.sp]; exact L.sp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    L.kw, ?_, fD, ?_, covers_cons he.perm.k rD, ?_⟩
  · rw [eY]; exact L.k_w' (by omega)
  · rw [e384]; exact L.k_w' (by decide)
  · rw [eY]; exact dC
  · rw [e384]; exact dS
  · rw [eY, e384]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [hb]; exact L.stk_k
  · rw [hb]; exact dB
  · rw [hb, eY]; exact L.stk_w' (by omega)
  · rw [hb, e384]; exact L.stk_w' (by decide)
  · rw [L.wN (by omega)]; have := L.ww; omega
  · rw [L.wN (by decide)]; have := L.ww; omega
  · rw [eY, e384]; exact covers_cons (he.perm.wC (by omega)) (he.perm.wC (by decide))

/-- The arguments of the call in `updBlock y`. -/
theorem updBlockArgs_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) : ∃ s₁, runBlock isa (updArgs y ++ [addI .r3 .r11 bO, .mov .r12 (imm 1)]) s = some s₁ ∧
      VG.Proof.AesCcm.Arm.UArgs s₁ k (w + BitVec.ofNat 32 y) (w + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 384) R 1 ∧
      VG.Proof.AesCcm.Arm.Env k w sp R q1 s₁ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
  obtain ⟨s₁, run₁, a0, a1, a2, a3, a12, alr, g₁, k₁⟩ : ∃ s₁, runBlock isa (updArgs y ++
      [addI .r3 .r11 bO, .mov .r12 (imm 1)]) s = some s₁ ∧
      s₁.gpr .r0 = k ∧ s₁.gpr .r1 = BitVec.ofNat 32 R ∧ s₁.gpr .r2 = w + BitVec.ofNat 32 y ∧
      s₁.gpr .r3 = w + BitVec.ofNat 32 32 ∧ s₁.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₁.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [updArgs, bO, scrO]; arun [he.r9, he.r8, he.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r9]
    · simp [gpr_setReg, he.r8]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he.r11]
    · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have e32 := L.wA (d := 32) (by decide)
  have eY := L.wA (d := y) (by omega)
  have dYB : (⟨State.addr w + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have U := VG.Proof.AesCcm.Arm.updCall_of L he₁ hR (y := y) (by omega) (D := w + BitVec.ofNat 32 32) (n := 1) (by decide)
    (by rw [L.wN (by decide)]; have := L.ww; omega) (by rw [e32]; exact dYB)
    (by rw [e32]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [e32]; exact L.stk_w' (by decide)) (by rw [e32]; exact covers_left (he₁.perm.wC (by decide)))
    a0 a1 a2 a3 a12 alr
  exact ⟨s₁, run₁, U, he₁, g₁, k₁⟩

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (updBlock y) s fun s' => VG.Proof.AesCcm.Arm.Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 y, 16⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16) [bytesAt s.mem (State.addr w + BitVec.ofNat 64 32) 16] := by
  obtain ⟨s₁, run₁, U, he₁, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.updBlockArgs_ok L he hR hy
  have e32 := L.wA (d := 32) (by decide)
  have eY := L.wA (d := y) (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (VG.Proof.AesCcm.Arm.upd_call U) fun s₂ h => ?_
  refine ⟨he₁.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, k₁.rd], by rw [h.wr, k₁.wr], fun r hr hlr => ?_,
    ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h.saved r hr hlr, g₁ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · have f := h.frame
    rw [VG.Proof.AesCcm.Arm.blw16_eq (k₁.sp.trans he.sp), eY, L.wA (d := 384) (by decide), k₁.mem] at f
    exact f
  · have o := h.out
    rw [eY, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
      (Proof.Cmac.bytesAt_length _ _ _), k₁.mem, e32] at o
    rw [o]; rfl

omit L in
theorem sub_mac {y : Nat} {r : Region} (hr : r ∈ VG.Proof.AesCcm.Arm.macR w sp y) : ∃ r' ∈ VG.Proof.AesCcm.Arm.macR w sp y, Region.Sub r r' :=
  ⟨r, hr, fun _ h => h⟩

omit L in
/-- `r12 = r5 / 16`, and `Z` for no whole blocks. -/
theorem split16_ok {s : State} {len : Nat} (hl : len < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 32 (len / 16) ∧ s₁.z = decide (len / 16 = 0) ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, VG.Proof.AesGcm.Arm.shr4 hl]
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, VG.Proof.AesGcm.Arm.shr4 hl]
    rw [z_cmp (by omega) (by decide)]
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- `r6 = r5 mod 16`, and `Z` for no last bytes. -/
theorem split15_ok {s : State} {len : Nat} (hl : len < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    ∃ s₁, runBlock isa [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)] s = some s₁ ∧
      s₁.gpr .r6 = BitVec.ofNat 32 (len % 16) ∧ s₁.z = decide (len % 16 = 0) ∧
      (∀ r, r ≠ .r6 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  have hand := VG.Proof.AesGcm.Arm.and15 (BitVec.ofNat 32 len)
  rw [toNat32 hl] at hand
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, imm, hand]
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, imm, hand]
    rw [z_cmp (by omega) (by decide)]
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The arguments of the call in `absorbWhole y`, for `nb` blocks at `P`. -/
theorem absArgs_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {nb : Nat} (hq : VG.Proof.AesCcm.Arm.Buf w sp s P (16 * nb)) (hn : 16 * nb < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h12 : s.gpr .r12 = BitVec.ofNat 32 nb) :
    ∃ s₂, runBlock isa (updArgs y ++ ([.mov .r3 (.reg .r4)] : List Instr)) s = some s₂ ∧
      VG.Proof.AesCcm.Arm.UArgs s₂ k (w + BitVec.ofNat 32 y) P (w + BitVec.ofNat 32 384) R nb ∧ VG.Proof.AesCcm.Arm.Env k w sp R q1 s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
  obtain ⟨s₂, run₂, a0, a1, a2, a3, alr, g₂, k₂⟩ : ∃ s₂, runBlock isa (updArgs y ++ [.mov .r3 (.reg .r4)]) s =
      some s₂ ∧ s₂.gpr .r0 = k ∧ s₂.gpr .r1 = BitVec.ofNat 32 R ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 y ∧
      s₂.gpr .r3 = P ∧ s₂.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
    have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
    refine ⟨_, by simp only [updArgs, scrO]; arun [he.r9, he.r8, he.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r9]
    · simp [gpr_setReg, he.r8]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg, h4]
    · simp [gpr_setReg, he.r11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) k₂.sp k₂.rd k₂.wr
  exact ⟨s₂, run₂, VG.Proof.AesCcm.Arm.updCall_of L he₂ hR (y := y) (by omega) (D := P) (n := nb) hn hq.fit
    (hq.w.sub_right (Lay.wSub (by omega))) (hq.w.sub_right (Lay.wSub (by decide))) hq.stk
    (by rw [k₂.rd, k₂.wr]; exact hq.rd) a0 a1 a2 a3
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h12]) alr, he₂, g₂, k₂⟩

/-- The whole blocks of the string. -/
theorem absorbWhole_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → VG.Proof.AesCcm.Arm.Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbWhole y) s (VG.Proof.AesCcm.Arm.Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 ((bytesAt s.mem (State.addr P) len).take (16 * (len / 16)))))) := by
  obtain ⟨s₁, run₁, h12₁, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split16_ok hl h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (len / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5],
      by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    rw [k₁.mem, h0, Nat.mul_zero, List.take_zero]; rfl
  · have h0 : len / 16 ≠ 0 := by simpa using hf
    have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
    have hq := ((hP (by omega)).take hb).of_eq k₁.rd k₁.wr
    obtain ⟨s₂, run₂, U, he₂, g₂, k₂⟩ := VG.Proof.AesCcm.Arm.absArgs_ok L he₁ hR hy hq (by omega) (by rw [g₁ _ (by decide), h4]) h12₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.mono (VG.Proof.AesCcm.Arm.upd_call U) fun s₃ h => ⟨he₂.of_saved h.saved h.sp h.rd h.wr, ?_, ?_, ?_, ?_,
      by rw [h.rd, k₂.rd, k₁.rd], by rw [h.wr, k₂.wr, k₁.wr]⟩
    · rw [h.saved _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₁ _ (by decide), h4]
    · rw [h.saved _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₁ _ (by decide), h5]
    · have f := h.frame
      rw [VG.Proof.AesCcm.Arm.blw16_eq (k₂.sp.trans (k₁.sp.trans he.sp)), L.wA (d := y) (by omega), L.wA (d := 384) (by decide),
        k₂.mem, k₁.mem] at f
      exact f.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesCcm.Arm.sub_mac (by simp)
    · have o := h.out
      rw [L.wA (d := y) (by omega), Proof.Cmac.Stream.blocksAt_eq, k₂.mem, k₁.mem, bytesAt_prefix _ _ hb] at o
      rw [o]; rfl

/-- `B` zeroed, and the arguments of the copy of the last `len mod 16` bytes
at `P` into it. -/
theorem tailPre_ok {s₁ : State} (he₁ : VG.Proof.AesCcm.Arm.Env k w sp R q1 s₁) {P : BitVec 32} {len : Nat}
    (hP : len ≠ 0 → VG.Proof.AesCcm.Arm.Buf w sp s₁ P len) (hl : len < 2 ^ 32) (h0 : len % 16 ≠ 0) (h4₁ : s₁.gpr .r4 = P)
    (h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 len) (h6₁ : s₁.gpr .r6 = BitVec.ofNat 32 (len % 16)) :
    ∃ s₃, runBlock isa (zero16 bO ++ ([.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
        addI .r2 .r11 bO, .mov .r3 (.reg .r6)] : List Instr)) s₁ = some s₃ ∧
      s₃.mem = Proof.Cmac.store4 s₁.mem (State.addr w + BitVec.ofNat 64 32) 0 0 0 0 ∧
      LoopPre s₃ (P + BitVec.ofNat 32 (16 * (len / 16))) (w + BitVec.ofNat 32 32) (len % 16) ∧
      VG.Proof.AesCcm.Arm.Env k w sp R q1 s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s₁.gpr r) ∧
      s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr ∧ s₃.sp = s₁.sp := by
  obtain ⟨s₂, run₂, hm₂, g₂, rd₂, wr₂, sp₂, -⟩ := VG.Proof.AesCcm.Arm.zero16_ok L he₁ (d := bO) (by decide) (by decide)
  simp only [bO] at hm₂
  have hj : 16 * (len / 16) + len % 16 = len := by omega
  have hsub : BitVec.ofNat 32 len - BitVec.ofNat 32 (len % 16) = BitVec.ofNat 32 (16 * (len / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hl]; congr 1; omega
  obtain ⟨s₃, run₃, a1, a2, a3, g₃, k₃⟩ : ∃ s₃, runBlock isa [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
      addI .r2 .r11 bO, .mov .r3 (.reg .r6)] s₂ = some s₃ ∧
      s₃.gpr .r1 = P + BitVec.ofNat 32 (16 * (len / 16)) ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 32 ∧
      s₃.gpr .r3 = BitVec.ofNat 32 (len % 16) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    have r4₂ : s₂.gpr .r4 = P := by rw [g₂ _ (by decide), h4₁]
    have r5₂ : s₂.gpr .r5 = BitVec.ofNat 32 len := by rw [g₂ _ (by decide), h5₁]
    have r6₂ : s₂.gpr .r6 = BitVec.ofNat 32 (len % 16) := by rw [g₂ _ (by decide), h6₁]
    have r11₂ : s₂.gpr .r11 = w := by rw [g₂ _ (by decide), he₁.r11]
    refine ⟨_, by simp only [bO]; arun [r11₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, r4₂, r5₂, r6₂, hsub, BitVec.add_comm]
    · simp [gpr_setReg, r11₂]
    · simp [gpr_setReg, r6₂]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₃ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide)]) (k₃.sp.trans sp₂)
    (k₃.rd.trans rd₂) (k₃.wr.trans wr₂)
  have hT := ((hP (by omega)).sub (j := 16 * (len / 16)) (k := len % 16) (by omega) (by omega)).of_eq (s' := s₃)
    (by rw [k₃.rd, rd₂]) (by rw [k₃.wr, wr₂])
  have e32 := L.wA (d := 32) (by decide)
  have eT := (hP (by omega)).addr (j := 16 * (len / 16)) (by omega)
  have lp : LoopPre s₃ (P + BitVec.ofNat 32 (16 * (len / 16))) (w + BitVec.ofNat 32 32) (len % 16) := by
    refine ⟨a1, a2, a3, by omega, by omega, hT.fit, by rw [L.wN (by decide)]; have := L.ww; omega, hT.rd, ?_, ?_⟩
    · rw [e32]; exact he₃.perm.wC (by omega)
    · rw [e32]; exact hT.w.sub_right (Lay.wSub (by omega))
  exact ⟨s₃, by
    rw [show zero16 bO ++ [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4), addI .r2 .r11 bO,
      .mov .r3 (.reg .r6)] = zero16 bO ++ ([.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
      addI .r2 .r11 bO, .mov .r3 (.reg .r6)] : List Instr) from rfl]
    exact runBlock_app_of run₂ run₃, by rw [k₃.mem, hm₂], lp, he₃, fun r a b c d => by rw [g₃ r b c d, g₂ r a],
    by rw [k₃.rd, rd₂], by rw [k₃.wr, wr₂], by rw [k₃.sp, sp₂]⟩

/-- The last bytes of the string, padded with zeros in `B`. -/
theorem absorbTail_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → VG.Proof.AesCcm.Arm.Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbTail y) s (VG.Proof.AesCcm.Arm.Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (VG.Proof.AesCcm.Arm.tailBlocks (bytesAt s.mem (State.addr P) len)))) := by
  have hxl := length_bytesAt s.mem (State.addr P) len
  obtain ⟨s₁, run₁, h6₁, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split15_ok hl h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (len % 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5],
      by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    simp only [k₁.mem, VG.Proof.AesCcm.Arm.tailBlocks, hxl, h0, ↓reduceIte]; rfl
  · have h0 : len % 16 ≠ 0 := by simpa using hf
    obtain ⟨s₃, run₃, hm₃, lp, he₃, g₃, rd₃, wr₃, sp₃⟩ := VG.Proof.AesCcm.Arm.tailPre_ok L he₁ (fun h => (hP h).of_eq k₁.rd k₁.wr) hl
      h0 (by rw [g₁ _ (by decide), h4]) (by rw [g₁ _ (by decide), h5]) h6₁
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have hT := ((hP (by omega)).sub (j := 16 * (len / 16)) (k := len % 16) (by omega) (by omega)).of_eq (s' := s₃)
      (by rw [rd₃, k₁.rd]) (by rw [wr₃, k₁.wr])
    have e32 := L.wA (d := 32) (by decide)
    have eT := (hP (by omega)).addr (j := 16 * (len / 16)) (by omega)
    refine WP.seq (WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, lo⟩ => ?_)
    have he₄ := he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr
    rw [e32, eT] at hm₄
    -- What was written: only `B`.
    have fZ : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem := by
      rw [hm₃, k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have fB : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
      rw [hm₄]
      exact fZ.trans (VG.WriteBytes.writeBytes_frame _ _ _ (by
        rw [length_bytesAt]
        exact Offset.contains _ (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide)))
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    have hK₄ : Spec.Ccm.ctxCiph s₄.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R :=
      ctxCiph_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have hY₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
      bytesAt_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    have hB₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem (State.addr P) len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
      have hs₂ : bytesAt s₃.mem (State.addr P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
          (bytesAt s.mem (State.addr P) len).drop (16 * (len / 16)) := by
        rw [bytesAt_frame fZ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [← eT]
            exact hT.w.sub_right (Lay.wSub (by decide))) (by omega),
          show len % 16 = len - 16 * (len / 16) by omega, bytesAt_suffix _ _ (by omega)]
      have hz : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
        rw [hm₃]; exact VG.Proof.AesCcm.Arm.store4_zero_bytes' _ _
      rw [hm₄, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega) (by decide), hs₂, hz,
        List.length_drop, hxl]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      congr 2
      omega
    refine WP.mono (VG.Proof.AesCcm.Arm.updBlock_ok L he₄ hR hy) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ =>
      ⟨he₅, ?_, ?_, ?_, ?_, by rw [rd₅, lo.rd, rd₃, k₁.rd], by rw [wr₅, lo.wr, wr₃, k₁.wr]⟩
    · rw [g₅ _ (by decide) (by decide), lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₃ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h4]
    · rw [g₅ _ (by decide) (by decide), lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₃ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h5]
    · refine (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.Arm.sub_mac (by simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesCcm.Arm.sub_mac (by simp)
    · rw [o₅, hY₄, hB₄, hK₄]
      simp only [VG.Proof.AesCcm.Arm.tailBlocks, hxl, h0, ↓reduceIte]

omit L in
/-- A buffer missing `W` and the stack below `sp` keeps its bytes. -/
theorem buf_kept {s : State} {P : BitVec 32} {len : Nat} (hP : VG.Proof.AesCcm.Arm.Buf w sp s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.Arm.macR w sp y) m m') :
    bytesAt m' (State.addr P) len = bytesAt m (State.addr P) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem k_macR {y : Nat} (hy : y + 16 ≤ 2560) : ∀ r ∈ VG.Proof.AesCcm.Arm.macR w sp y, (⟨State.addr k, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w' hy
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.stk_k.symm

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → VG.Proof.AesCcm.Arm.Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbPad y) s (VG.Proof.AesCcm.Arm.Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem (State.addr P) len))))) := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.absorbWhole_ok L he hR hy hP hl h4 h5) fun s₁ A₁ => ?_)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.Arm.absorbTail_ok L A₁.env hR hy (fun h => (hP h).of_eq A₁.rd A₁.wr) hl A₁.r4 A₁.r5) fun s₂ A₂ =>
    ⟨A₂.env, A₂.r4, A₂.r5, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  have hk : bytesAt s₁.mem (State.addr P) len = bytesAt s.mem (State.addr P) len := by
    rcases Nat.eq_zero_or_pos len with e | e
    · subst e; rfl
    · exact VG.Proof.AesCcm.Arm.buf_kept (hP (by omega)) (by omega) A₁.frame
  rw [A₂.out, A₁.out, hk, ctxCiph_frame A₁.frame (VG.Proof.AesCcm.Arm.k_macR L (by omega)) hRb,
    ← Proof.Cmac.chain_append, Proof.AesCcm.blocks_pad16, length_bytesAt, VG.Proof.AesCcm.Arm.tailBlocks, length_bytesAt]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Header`. -/
section

/-!
# AES-CCM on ARMv7: the encoding of the length of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `0 < a < 2³²` (A.2.2) at its start:
`[a]₁₆` or `0xff ‖ 0xfe ‖ [a]₃₂`, from the byte-reversed `a` shifted
(`header_ok`); its length is in `r6`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Impl.AesGcm.Arm (imm addI zero16)
open VG.Proof.AesGcm.Arm (bytesAt_frame runBlock_app_of toNat32 eval_eq' Keeps z_subFlags gpr_subFlags
  c_subFlags adc_c gpr_store mem_store)
open VG.Proof.AesCcm (hdrLen bytesAt_writeW32_at bytesAt_writeW32_base be_split length_be)

theorem encodeLen_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) : Spec.Ccm.encodeLen a = Spec.Ccm.be 2 a := by
  simp [Spec.Ccm.encodeLen, h]

theorem encodeLen_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xfe] ++ Spec.Ccm.be 4 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem le4_feff : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe, 0, 0] := by decide

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`r5`) at its start, and its length in `r6`. -/
theorem header_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa header s fun s' => VG.Proof.AesCcm.Arm.Env k w sp R q1 s' ∧ s'.gpr .r6 = BitVec.ofNat 32 (hdrLen a) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      (s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) ∧ Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := VG.Proof.AesCcm.Arm.zero16_ok L he (d := bO) (by decide) (by decide)
  simp only [bO] at hm₁
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 a := by rw [g₁ _ (by decide), h5]
  obtain ⟨s₂, run₂, hz₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] s₁ = some s₂ ∧
      s₂.z = !decide (65280 ≤ a) ∧ (∀ r, r ≠ .r0 → r ≠ .r12 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [z_subFlags, c_subFlags, gpr_setReg, gpr_subFlags, z_setReg, c_setReg, ite_true, ite_false,
        reduceCtorEq, h5₁, toNat32 ha, imm, show (BitVec.ofNat 32 65280).toNat = 65280 from rfl]
      cases decide (65280 ≤ a) <;> rfl
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have hz : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [k₂.mem, hm₁]; exact VG.Proof.AesCcm.Arm.store4_zero_bytes' _ _
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [k₂.mem, hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)])
    (k₂.sp.trans sp₁) (k₂.rd.trans rd₁) (k₂.wr.trans wr₁)
  have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 a := by rw [g₂ _ (by decide) (by decide), h5₁]
  have h11 := he₂.r11
  have e32 := L.wA (d := 32) (by decide)
  have e36 := L.wA (d := 36) (by decide)
  have w₀ := he₂.perm.wW (show 32 + 4 ≤ 2560 by decide)
  have w₁ := he₂.perm.wW (show 36 + 4 ≤ 2560 by decide)
  have cB : ∀ d n, 32 ≤ d → d + n ≤ 48 →
      (⟨State.addr w + BitVec.ofNat 64 32, 16⟩ : Region).Contains (State.addr w + BitVec.ofNat 64 d) n :=
    fun d n h₁ h₂ => Offset.contains _ h₁ (by omega) (by decide)
  have kg : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r a b c d e => by
    rw [g₂ r a e, g₁ r a]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show zero16 bO ++ [.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0), .mov .r12 (imm 0),
      .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] = zero16 bO ++ ([.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] : List Instr) from rfl]
    exact runBlock_app_of run₁ run₂, ?_⟩)
  have hrev := VG.Proof.AesCcm.Arm.le4_rev_ofNat ha
  refine WP.ite (!decide (65280 ≤ a)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · -- `[a]₁₆`.
    have h₁ : a < 2 ^ 16 - 2 ^ 8 := by simp at ht; omega
    refine WP.of_runBlock ⟨_, by simp only [bO]; arun [h11, e32, w₀], ?_⟩
    refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_,
      ⟨k₂.rd.trans rd₁, k₂.wr.trans wr₁, k₂.sp.trans sp₁⟩, ?_, ?_⟩
    · simp [gpr_setReg, hdrLen, h₁]
    · intro r a b c d e; simp only [gpr_store, gpr_setReg, a, d, ite_false]; exact kg r a b c d e
    · simp only [mem_store, mem_setReg]
      exact fz.writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))
    · simp only [mem_store, gpr_store, mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂]
      rw [bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz, VG.Proof.AesCcm.Arm.le4_shr16, hrev,
        be_split (q := 2) (by decide) (by omega), VG.Proof.AesCcm.Arm.encodeLen_lo h₁, show hdrLen a = 2 by simp [hdrLen, h₁]]
      simp [Spec.Ccm.zeros, List.drop_append_of_le_length, length_be]
  · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
    have h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by simp at hf; omega
    refine WP.of_runBlock ⟨_, by simp only [bO]; arun [h11, e32, e36, w₀, w₁], ?_⟩
    refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_,
      ⟨k₂.rd.trans rd₁, k₂.wr.trans wr₁, k₂.sp.trans sp₁⟩, ?_, ?_⟩
    · simp [gpr_setReg, hdrLen, h₁, ha]
    · intro r a b c d e; simp only [gpr_store, gpr_setReg, a, b, c, d, ite_false]; exact kg r a b c d e
    · simp only [mem_store, mem_setReg]
      exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (cB 36 4 (by decide) (by decide))
    · simp only [mem_store, gpr_store, mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂]
      rw [show State.addr w + BitVec.ofNat 64 36 = State.addr w + BitVec.ofNat 64 32 + BitVec.ofNat 64 4 by
          rw [Offset.add_add],
        bytesAt_writeW32_at _ _ _ (by decide) (by decide), bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz,
        Proof.AesCcm.le4_or, VG.Proof.AesCcm.Arm.le4_shl16, VG.Proof.AesCcm.Arm.le4_shr16, hrev, VG.Proof.AesCcm.Arm.encodeLen_mid h₁ ha,
        show hdrLen a = 6 by simp [hdrLen, h₁, ha]]
      have hl4 := length_be 4 a
      have hfe : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe, 0, 0] := VG.Proof.AesCcm.Arm.le4_feff
      rcases hb : Spec.Ccm.be 4 a with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
        rw [hb] at hl4 <;> simp at hl4
      simp [Spec.Ccm.zeros, List.replicate, hfe]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Aad`. -/
section

/-!
# AES-CCM on ARMv7: the associated data (`aad y`)

Untrusted: everything here is checked by Lean. The pieces read the stack
arguments, which the writes of the pieces miss, as on entry (`Stk`).
`aadHead y` chains the first block of the formatted associated data: the
encoding of its length followed by as many of its bytes as fit, padded
(`aadHead_ok`); `aad y` that block and the rest of the associated data,
padded, if there is any (`aad_ok`): the blocks `adataBlocks`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop minLen)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok bytesAt_frame toNat32 ofNat_sub32 z_cmp eval_eq' Keeps
  z_subFlags gpr_subFlags minLen_ok add32_ofNat_assoc ArgsKeep)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks ctxCiph_frame bytesAt_prefix bytesAt_suffix
  bytesAt_writeBytes_at length_bytesAt)

/-- The stack arguments of `s` are those of the entry state `s₀`, apart from
`W` and the stack below `sp`. -/
structure Stk (w : BitVec 32) (s₀ s : State) : Prop where
  keep : ArgsKeep 7 s₀ s
  fit : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32
  rd : VG.Proof.AesCcm.Arm.args s₀ 7 ∈ s₀.rd
  aw : (VG.Proof.AesCcm.Arm.args s₀ 7).Disjoint ⟨State.addr w, 2560⟩

namespace Stk

variable {w : BitVec 32} {s₀ s : State} (h : VG.Proof.AesCcm.Arm.Stk w s₀ s)
include h

/-- Argument `i`, at offset `4 i`. -/
theorem «at» (i : Nat) {off : Nat} (hi : i < 7) (hoff : 4 * i = off) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 = stackArg s₀ i :=
  h.keep.at h.fit h.rd i hi hoff

/-- Argument `i` is apart from `W`. -/
theorem slot_w (i : Nat) {off : Nat} (hi : i < 7) (hoff : 4 * i = off) {d n : Nat} (hd : d + n ≤ 2560) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 off), 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, n⟩ := by
  subst hoff
  have := h.fit
  have e : State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
    rw [h.keep.sp, Proof.AesGcm.Arm.argAddr_zero]; exact addr_add (by omega)
  rw [e]
  exact (h.aw.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub hd)

theorem of_eq {s' : State} (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.Stk w s₀ s' :=
  { h with keep := h.keep.of_eq hm hsp hrd hwr }

/-- After code that writes regions apart from the arguments. -/
theorem frame {s' : State} {rs : List Region} (hfr : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (VG.Proof.AesCcm.Arm.args s₀ 7).Disjoint r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesCcm.Arm.Stk w s₀ s' :=
  { h with keep := h.keep.frame h.fit hfr hd hsp hrd hwr }

/-- The stack below `sp` is apart from the arguments. -/
theorem blw_args {sp : BitVec 32} (hsp : s₀.sp = sp) : (VG.Proof.AesCcm.Arm.args s₀ 7).Disjoint (VG.Proof.AesCcm.Arm.blw sp) := by
  have := h.fit
  subst hsp
  simp only [VG.Proof.AesCcm.Arm.args, Proof.AesGcm.Arm.argAddr_zero]
  exact Offset.base_disjoint_below (State.addr s₀.sp) (n := 16) (k := 4 * 7) (by omega)

/-- After code that writes the MAC's regions. -/
theorem mac {sp : BitVec 32} (hsp₀ : s₀.sp = sp) {y : Nat} (hy : y + 16 ≤ 2560) {s' : State}
    (hfr : Frame (VG.Proof.AesCcm.Arm.macR w sp y) s.mem s'.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesCcm.Arm.Stk w s₀ s' :=
  h.frame hfr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.aw.sub_right (Lay.wSub hy)
    · exact h.aw.sub_right (Lay.wSub (by decide))
    · exact h.aw.sub_right (Lay.wSub (by decide))
    · exact h.blw_args hsp₀) hsp hrd hwr

end Stk

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => VG.Proof.AesCcm.Arm.seq_assoc3 h)

/-- What a piece of the MAC leaves: the environment, what it writes, the
MAC state `Y` at `W + y`, and the permissions. -/
structure MacStep (k w sp : BitVec 32) (R q1 : Nat) (s : State) (y : Nat) (Y : List Byte) (s' : State) :
    Prop where
  env : VG.Proof.AesCcm.Arm.Env k w sp R q1 s'
  frame : Frame (VG.Proof.AesCcm.Arm.macR w sp y) s.mem s'.mem
  out : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- The encoding of the length and the first bytes of the associated data,
padded, in `B`; `r4` and `r5` the rest. -/
theorem aadHeadPre_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) {A : BitVec 32} {a : Nat} (hA : VG.Proof.AesCcm.Arm.Buf w sp s A a)
    (ha0 : 0 < a) (ha : a < 2 ^ 32) (h4 : s.gpr .r4 = A) (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa (.seq header (.seq minLen (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r11 bO,
        .dp .add .r2 .r2 (.reg .r6), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]) copyLoop))) s
      fun s₄ => VG.Proof.AesCcm.Arm.Env k w sp R q1 s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
        Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem ∧
        s₄.gpr .r4 = A + BitVec.ofNat 32 (headLen a) ∧ s₄.gpr .r5 = BitVec.ofNat 32 (a - headLen a) ∧
        bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
          Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a)) := by
  have hh := Proof.AesCcm.hdrLen_le a
  have hh26 : hdrLen a = 2 ∨ hdrLen a = 6 := by
    unfold hdrLen; by_cases h : a < 2 ^ 16 - 2 ^ 8 <;> simp [h, ha]
  have hh2 : 2 ≤ hdrLen a := by omega
  have hh6 : hdrLen a ≤ 6 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.header_ok L he ha0 ha h5) fun s₁ ⟨he₁, h6₁, g₁, ⟨rd₁, wr₁, sp₁⟩, f₁, hB₁⟩ => ?_)
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 a := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  have h4₁ : s₁.gpr .r4 = A := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  refine WP.seq (WP.mono (minLen_ok s₁ h6₁ h5₁ (by omega) ha) fun s₂ ⟨h3₂, g₂, k₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = headLen a := by unfold headLen; omega
  rw [hn1] at h3₂
  have hn1' : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) k₂.sp k₂.rd k₂.wr
  have h11 := he₂.r11
  obtain ⟨s₃, run₃, a1, a2, a3, a4, a5, g₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (.reg .r4), addI .r2 .r11 bO,
      .dp .add .r2 .r2 (.reg .r6), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)] s₂ = some s₃ ∧
      s₃.gpr .r1 = A ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 (32 + hdrLen a) ∧
      s₃.gpr .r3 = BitVec.ofNat 32 (headLen a) ∧ s₃.gpr .r4 = A + BitVec.ofNat 32 (headLen a) ∧
      s₃.gpr .r5 = BitVec.ofNat 32 (a - headLen a) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    have h4₂ : s₂.gpr .r4 = A := by rw [g₂ _ (by decide) (by decide), h4₁]
    have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 a := by rw [g₂ _ (by decide) (by decide), h5₁]
    have h6₂ : s₂.gpr .r6 = BitVec.ofNat 32 (hdrLen a) := by rw [g₂ _ (by decide) (by decide), h6₁]
    refine ⟨_, by simp only [bO]; arun [h11], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h4₂]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h11, h6₂, imm, add32_ofNat_assoc]
    · simp [gpr_setReg, h3₂]
    · simp [gpr_setReg, h4₂, h3₂]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂, h3₂]
      exact ofNat_sub32 hn1'.2.1 ha
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide) (by decide))
    k₃.sp k₃.rd k₃.wr
  have hA₃ := (hA.take hn1'.2.1).of_eq (s' := s₃) (by rw [k₃.rd, k₂.rd, rd₁]) (by rw [k₃.wr, k₂.wr, wr₁])
  have eB := L.wA (d := 32 + hdrLen a) (by omega)
  have lp : LoopPre s₃ A (w + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) := by
    refine ⟨a1, a2, a3, hn1'.1, by omega, hA₃.fit, by rw [L.wN (by omega)]; have := L.ww; omega, hA₃.rd, ?_, ?_⟩
    · rw [eB]; exact he₃.perm.wC (by omega)
    · rw [eB]; exact hA₃.w.sub_right (Lay.wSub (by omega))
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, lo⟩ => ?_
  have he₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  rw [eB] at hm₄
  have fC : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains _ (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have fB : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← k₂.mem, ← k₃.mem] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem (State.addr A) (headLen a) = (bytesAt s.mem (State.addr A) a).take (headLen a) := by
    rw [k₃.mem, k₂.mem, bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right (Lay.wSub (by decide))) (by omega),
      bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem (State.addr A) a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega
    rw [hm₄, show State.addr w + BitVec.ofNat 64 (32 + hdrLen a) =
        State.addr w + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by rw [Offset.add_add],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hAk, k₃.mem,
      k₂.mem, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega)
  exact ⟨he₄, by rw [lo.rd, k₃.rd, k₂.rd, rd₁], by rw [lo.wr, k₃.wr, k₂.wr, wr₁], fB,
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), a4],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), a5], hB₄⟩

/-- The first block of the associated data. -/
theorem aadHead_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {A : BitVec 32} {a : Nat} (hA : VG.Proof.AesCcm.Arm.Buf w sp s A a) (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (h4 : s.gpr .r4 = A) (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa (aadHead y) s (VG.Proof.AesCcm.Arm.Absorbed k w sp R q1 s y (A + BitVec.ofNat 32 (headLen a)) (a - headLen a)
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a))])) := by
  refine VG.Proof.AesCcm.Arm.seq_assoc4 (WP.seq (WP.mono (VG.Proof.AesCcm.Arm.aadHeadPre_ok L he hA ha0 ha h4 h5)
    fun s₄ ⟨he₄, rd₄, wr₄, fB, h4₄, h5₄, hB₄⟩ => ?_))
  have hY₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 y) 16 =
      bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
    bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.Arm.updBlock_ok L he₄ hR hy) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ =>
    ⟨he₅, ?_, ?_, (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_), ?_, by rw [rd₅, rd₄],
      by rw [wr₅, wr₄]⟩
  · rw [g₅ _ (by decide) (by decide), h4₄]
  · rw [g₅ _ (by decide) (by decide), h5₄]
  · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.Arm.sub_mac (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesCcm.Arm.sub_mac (by simp)
  · rw [o₅, hY₄, hB₄, ctxCiph_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb]

omit L in
/-- `r4` and `r5` the associated data and its length, and `Z` for none. -/
theorem aadLd_ok {s₀ s : State} (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s) {A : BitVec 32} {al : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (hal : al < 2 ^ 32) :
    ∃ s₁, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .cmp .r5 (imm 0)] s = some s₁ ∧ s₁.gpr .r4 = A ∧
      s₁.gpr .r5 = BitVec.ofNat 32 al ∧ s₁.z = decide (al = 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  obtain ⟨i0, v0⟩ := hk.at 0 (by decide) (show 4 * 0 = 0 from rfl)
  obtain ⟨i1, v1⟩ := hk.at 1 (by decide) (show 4 * 1 = 4 from rfl)
  refine ⟨_, by arun [i0, v0, i1, v1], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v0, eA]
  · simp [gpr_setReg, v1, eal]
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v1, eal, imm]
    rw [z_cmp hal (by decide)]
  · intro r a b; simp [gpr_setReg, a, b]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- `r4` and `r5` the data and its length. -/
theorem dataLd_ok {s₀ s : State} (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s) {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D)
    (en : stackArg s₀ 3 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12] s = some s₁ ∧ s₁.gpr .r4 = D ∧
      s₁.gpr .r5 = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  obtain ⟨i2, v2⟩ := hk.at 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  refine ⟨_, by arun [i2, v2, i3, v3], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2, eD]
  · simp [gpr_setReg, v3, en]
  · intro r a b; simp [gpr_setReg, a, b]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The associated data, formatted and chained. -/
theorem aad_ok {s₀ s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s) {A : BitVec 32} {al : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (hal : al < 2 ^ 32) (hA : VG.Proof.AesCcm.Arm.Buf w sp s A al) :
    WP isa (aad y) s (VG.Proof.AesCcm.Arm.MacStep k w sp R q1 s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem (State.addr A) al)))) := by
  obtain ⟨s₁, run₁, h4₁, h5₁, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.aadLd_ok hk eA eal hal
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hA₁ := hA.of_eq k₁.rd k₁.wr
  refine WP.ite (decide (al = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    simp only [k₁.mem, adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : al ≠ 0 := by simpa using hf
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.aadHead_ok L he₁ hR hy hA₁ (by omega) hal h4₁ h5₁) fun s₂ A₂ => ?_)
    have hn1 : headLen al ≤ al := by unfold headLen; omega
    have hT : al - headLen al ≠ 0 → VG.Proof.AesCcm.Arm.Buf w sp s₂ (A + BitVec.ofNat 32 (headLen al)) (al - headLen al) :=
      fun e => (hA.sub (j := headLen al) (k := al - headLen al) (by omega) (by omega)).of_eq
        (by rw [A₂.rd, k₁.rd]) (by rw [A₂.wr, k₁.wr])
    refine WP.mono (VG.Proof.AesCcm.Arm.absorbPad_ok L A₂.env hR hy hT (by omega) A₂.r4 A₂.r5) fun s₃ A₃ =>
      ⟨A₃.env, by rw [← k₁.mem]; exact A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd, k₁.rd],
        by rw [A₃.wr, A₂.wr, k₁.wr]⟩
    have eT : bytesAt s₂.mem (State.addr (A + BitVec.ofNat 32 (headLen al))) (al - headLen al) =
        (bytesAt s.mem (State.addr A) al).drop (headLen al) := by
      rcases Nat.eq_zero_or_pos (al - headLen al) with e | e
      · rw [e, List.drop_eq_nil_of_le (by rw [length_bytesAt]; omega)]; rfl
      · rw [hA.addr (j := headLen al) (by omega), bytesAt_suffix _ _ hn1, VG.Proof.AesCcm.Arm.buf_kept hA₁ (by omega) A₂.frame,
          k₁.mem]
    rw [A₃.out, A₂.out, eT, ctxCiph_frame A₂.frame (VG.Proof.AesCcm.Arm.k_macR L (by omega)) hRb, k₁.mem, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.B0`. -/
section

/-!
# AES-CCM on ARMv7: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `flagsCode` computes the
flags `64 [a > 0] + 4 (t − 2) + q − 1` (which is A.2.1's for an even `t`);
`b0Block y` writes `B₀` to `W + 32` from `Ctr₀`, its first byte `q − 1`
replaced by the flags (`le4_flags`) and `[p]₃₂` ORed into its last word, and
zeroes the MAC state at `W + y`; `b0 y` then chains `B₀` into it (`b0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Impl.AesGcm.Arm (imm addI zero16)
open VG.Proof.AesGcm.Arm (bytesAt_frame runBlock_app_of toNat32 ofNat_sub32 ofNat_add32 z_cmp eval_eq' Keeps
  z_subFlags gpr_subFlags mem_store gpr_store store4_eq add_ofNat_assoc bytes_words sepW)
open VG.Proof.AesCcm (ctxCiph_frame ctrBlock_split length_bytesAt)

/-- The first word of `Ctr₀`, its first byte `c` replaced by `f`. -/
theorem le4_flags (x : BitVec 32) {c f : Nat} (hc : c < 256) (hf : f < 256)
    (h0 : x.extractLsb' 0 8 = BitVec.ofNat 8 c) :
    le4 ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f) = BitVec.ofNat 8 f :: (le4 x).drop 1 := by
  have hi : ∀ o j, 8 ≤ o → o + j < 32 → (BitVec.ofNat 32 c).getLsbD (o + j) = false ∧
      (BitVec.ofNat 32 f).getLsbD (o + j) = false := fun o j h₁ h₂ => by
    have hp : 256 ≤ 2 ^ (o + j) := Nat.pow_le_pow_right (n := 2) (i := 8) (by decide) (by omega)
    simp only [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hf hp), Bool.and_false, and_self]
  have ek : ∀ o, 8 ≤ o → o + 8 ≤ 32 →
      ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f).extractLsb' o 8 = x.extractLsb' o 8 := fun o h₁ h₂ => by
    ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_xor, (hi o j h₁ (by omega)).1,
      (hi o j h₁ (by omega)).2, Bool.xor_false, Bool.or_false]
  have e0 : ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f).extractLsb' 0 8 = BitVec.ofNat 8 f := by
    ext j hj
    have hx := congrArg (fun b : BitVec 8 => b.getLsbD j) h0
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.zero_add,
      BitVec.getLsbD_ofNat] at hx
    simp only [BitVec.getElem_extractLsb', Nat.zero_add, BitVec.getLsbD_or,
      BitVec.getLsbD_xor, hx, BitVec.getLsbD_ofNat, show j < 32 by omega, decide_true, Bool.true_and,
      Bool.xor_self, Bool.false_or]
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]; simp [hj]
  rw [VG.Proof.AesCcm.Arm.le4_eq, VG.Proof.AesCcm.Arm.le4_eq, e0, ek 8 (by decide) (by decide), ek 16 (by decide) (by decide),
    ek 24 (by decide) (by decide)]
  rfl

theorem flags_val {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl)
    (h13 : nl ≤ 13) :
    BitVec.ofNat 8 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) = Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega, ite_false, Nat.zero_add]; omega
  · simp only [h, ite_false, show al > 0 by omega, ite_true]; omega

theorem shl2 {n : Nat} (hn : n < 2 ^ 30) : BitVec.ofNat 32 n <<< 2 = BitVec.ofNat 32 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The bytes of `B₀`, as `b0Block` builds them from `Ctr₀`. -/
theorem b0_bytes {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {w₀ w₁ w₂ w₃ : BitVec 32}
    (hc : le4 w₀ ++ le4 w₁ ++ le4 w₂ ++ le4 w₃ = Spec.Ccm.ctrBlock nonce 0) {n f : Nat} (hf : f < 256)
    (hn : n < 256 ^ min (15 - nonce.length) 4) (hn4 : n < 2 ^ 32) :
    le4 ((w₀ ^^^ BitVec.ofNat 32 (14 - nonce.length)) ||| BitVec.ofNat 32 f) ++ le4 w₁ ++ le4 w₂ ++
      le4 (w₃ ||| rev (BitVec.ofNat 32 n)) = BitVec.ofNat 8 f :: (Spec.Ccm.ctrBlock nonce n).drop 1 := by
  have l := Proof.Cmac.length_le4
  have h0 : w₀.extractLsb' 0 8 = BitVec.ofNat 8 (14 - nonce.length) := by
    have := congrArg List.head? hc
    rw [VG.Proof.AesCcm.Arm.le4_eq w₀] at this
    simp only [List.cons_append, List.head?_cons, Spec.Ccm.ctrBlock, Option.some.injEq] at this
    rw [this]; congr 1; omega
  rw [VG.Proof.AesCcm.Arm.le4_flags w₀ (by omega) hf h0]
  have hl : (le4 w₀ ++ le4 w₁ ++ le4 w₂).length = 12 := by simp [l]
  rw [ctrBlock_split h7 h13 hn, ← hc, Proof.AesCcm.le4_or, VG.Proof.AesCcm.Arm.le4_rev_ofNat hn4, List.take_left' hl,
    List.drop_left' hl]
  rw [VG.Proof.AesCcm.Arm.le4_eq w₀]; rfl

section
variable {k w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

omit L in
/-- The flags of `B₀` in `r0`. -/
theorem flags_ok {s₀ s : State} {nl : Nat} (he : VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s) (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s) {tl al : Nat}
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (h13 : nl ≤ 13) (hal : al < 2 ^ 32) :
    WP isa flagsCode s fun s' =>
      s'.gpr .r0 = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨i5, v5⟩ := hk.at 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨i1, v1⟩ := hk.at 1 (by decide) (show 4 * 1 = 4 from rfl)
  have h10 := he.r10
  obtain ⟨s₁, run₁, h0₁, hz, g₁, k₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r0 20, .mov .r0 (.shifted .r0 .lsl 2),
      .dp .sub .r0 .r0 (imm 8), .dp .add .r0 .r0 (.reg .r10), .ldrSp .r1 4, .cmp .r1 (imm 0)] s = some s₁ ∧
      s₁.gpr .r0 = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl)) ∧ s₁.z = decide (al = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [i5, v5, i1, v1], ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v5, etl, h10, imm,
        VG.Proof.AesCcm.Arm.shl2 (show tl < 2 ^ 30 by omega), ofNat_sub32 (show 8 ≤ 4 * tl by omega) (show 4 * tl < 2 ^ 32 by omega),
        ofNat_add32]
      congr 1; omega
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v1, eal, imm]
      rw [z_cmp hal (by decide)]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (al = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := by simpa using ht
    exact WP.block_nil ⟨by rw [h0₁, h0]; rfl, g₁, k₁⟩
  · have h0 : al ≠ 0 := by simpa using hf
    refine Proof.AesGcm.Arm.WP.run (Q := fun s' => s' = s₁.setReg .r0 (s₁.gpr .r0 + BitVec.ofNat 32 64)) ⟨_, by arun [], rfl⟩
      fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r a b => ?_, k₁.trans ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_setReg_self, h0₁, ofNat_add32, h0, ite_false]
    · simp only [gpr_setReg, a, ite_false]; exact g₁ r a b

/-- `B₀` in `B` and the MAC state at `W + y` zeroed. -/
theorem b0Pre_ok {s₀ s : State} {nl : Nat} (he : VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s) (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s)
    {tl al n : Nat} (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (en : stackArg s₀ 3 = BitVec.ofNat 32 n) {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl)
    (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32)
    (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (.seq flagsCode (.block (b0Block y))) s fun s' =>
      VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩, ⟨State.addr w + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.flags_ok he hk etl eal ht4 ht16 h13 hal) fun s₁ ⟨h0₁, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  obtain ⟨i3, v3⟩ := hk₁.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  have h10 := he₁.r10
  have h11 := he₁.r11
  have r₀ := he₁.perm.wR (show 48 + 4 ≤ 2560 by decide)
  have r₁ := he₁.perm.wR (show 52 + 4 ≤ 2560 by decide)
  have r₂ := he₁.perm.wR (show 56 + 4 ≤ 2560 by decide)
  have r₃ := he₁.perm.wR (show 60 + 4 ≤ 2560 by decide)
  have w₀ := he₁.perm.wW (show 32 + 4 ≤ 2560 by decide)
  have w₁ := he₁.perm.wW (show 36 + 4 ≤ 2560 by decide)
  have w₂ := he₁.perm.wW (show 40 + 4 ≤ 2560 by decide)
  have w₃ := he₁.perm.wW (show 44 + 4 ≤ 2560 by decide)
  have q : ∀ a d, a + 4 ≤ d ∨ d + 4 ≤ a → a + 4 ≤ 2560 → d + 4 ≤ 2560 →
      (⟨State.addr w + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ h₃ => L.w_w h₁ h₂ h₃
  have p₁ := fun m v => sepW (m := m) (v := v) (q 52 32 (by decide) (by decide) (by decide))
  have p₂ := fun m v => sepW (m := m) (v := v) (q 56 32 (by decide) (by decide) (by decide))
  have p₃ := fun m v => sepW (m := m) (v := v) (q 56 36 (by decide) (by decide) (by decide))
  have p₄ := fun m v => sepW (m := m) (v := v) (q 60 32 (by decide) (by decide) (by decide))
  have p₅ := fun m v => sepW (m := m) (v := v) (q 60 36 (by decide) (by decide) (by decide))
  have p₆ := fun m v => sepW (m := m) (v := v) (q 60 40 (by decide) (by decide) (by decide))
  have e := fun d (hd : d < 2560) => L.wA (d := d) hd
  have p₇ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 32) (by decide))
  have p₈ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 36) (by decide))
  have p₉ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 40) (by decide))
  let m := s₁.mem
  let W := State.addr w
  let f := 4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64
  have hf : f < 256 := by simp only [f]; split <;> omega
  obtain ⟨s₂, run₂, hm₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldr .r1 .r11 c0O, .dp .eor .r1 .r1 (.reg .r10),
      .dp .orr .r1 .r1 (.reg .r0), .str .r1 .r11 bO, .ldr .r1 .r11 (c0O + 4), .str .r1 .r11 (bO + 4),
      .ldr .r1 .r11 (c0O + 8), .str .r1 .r11 (bO + 8), .ldr .r1 .r11 (c0O + 12), .ldrSp .r2 12, .rev .r2 .r2,
      .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r11 (bO + 12)] s₁ = some s₂ ∧
      s₂.mem = store4 m (W + BitVec.ofNat 64 32)
        ((m.readW (W + BitVec.ofNat 64 48) 32 ^^^ BitVec.ofNat 32 (14 - nl)) ||| BitVec.ofNat 32 f)
        (m.readW (W + BitVec.ofNat 64 52) 32) (m.readW (W + BitVec.ofNat 64 56) 32)
        (m.readW (W + BitVec.ofNat 64 60) 32 ||| rev (BitVec.ofNat 32 n)) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧ (s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp) := by
    refine ⟨_, by simp only [c0O, bO]; arun [h10, h11, i3, v3, e, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃,
      p₄, p₅, p₆, p₇, p₈, p₉], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h10, h0₁, v3, en,
        store4_eq, add_ofNat_assoc, m, W, f]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) k₂.2.2 k₂.1 k₂.2.1
  obtain ⟨s₃, run₃, hm₃, g₃, rd₃, wr₃, sp₃, -⟩ := VG.Proof.AesCcm.Arm.zero16_ok L he₂ (d := y) (by omega) (by omega)
  refine WP.of_runBlock ⟨s₃, by
    rw [show b0Block y = [.ldr .r1 .r11 c0O, .dp .eor .r1 .r1 (.reg .r10),
      .dp .orr .r1 .r1 (.reg .r0), .str .r1 .r11 bO, .ldr .r1 .r11 (c0O + 4), .str .r1 .r11 (bO + 4),
      .ldr .r1 .r11 (c0O + 8), .str .r1 .r11 (bO + 8), .ldr .r1 .r11 (c0O + 12), .ldrSp .r2 12, .rev .r2 .r2,
      .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r11 (bO + 12)] ++ zero16 y from rfl]
    exact runBlock_app_of run₂ run₃, ?_⟩
  have dY : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂, show m = s.mem from k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have f₃ : Frame [⟨W + BitVec.ofNat 64 y, 16⟩] s₂.mem s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) sp₃ rd₃ wr₃,
    by rw [rd₃, k₂.1, k₁.rd], by rw [wr₃, k₂.2.1, k₁.wr], by rw [sp₃, k₂.2.2, k₁.sp],
    (f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_), ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · rw [hm₃]; exact VG.Proof.AesCcm.Arm.store4_zero_bytes' _ _
  · rw [bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dY) (by decide),
      hm₂, Proof.Cmac.bytesAt_store4]
    have hw := hc0
    rw [bytes_words] at hw
    simp only [add_ofNat_assoc] at hw
    rw [← k₁.mem] at hw
    have hnm : n < 256 ^ min (15 - nonce.length) 4 := by
      rw [hnl]
      rcases Nat.le_total (15 - nl) 4 with h | h
      · rw [Nat.min_eq_left h]; exact hn
      · rw [Nat.min_eq_right h]; exact Nat.lt_of_lt_of_le hn4 (by decide)
    have hb := VG.Proof.AesCcm.Arm.b0_bytes (f := f) (by omega) (by omega) hw hf hnm hn4
    rw [hnl] at hb
    rw [hb]
    simp only [Spec.Ccm.b0, Spec.Ccm.ctrBlock, List.drop_succ_cons, List.drop_zero, hnl, f]
    rw [VG.Proof.AesCcm.Arm.flags_val ht4 ht16 hte h7 h13, List.cons_append, List.drop_succ_cons, List.drop_zero, List.cons_append]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Mac`. -/
section

/-!
# AES-CCM on ARMv7: the MAC (`mac y`)

Untrusted: everything here is checked by Lean. `b0 y` chains `B₀` into a
zeroed MAC state at `W + y` (`b0_ok`); `mac y` then chains the formatted
associated data and the payload padded: CBC-MAC of the formatted blocks
(`mac_ok`), whose first `t` bytes are CCM's MAC (`Proof.AesCcm.mac_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (Keeps)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt format_eq)

section
variable {k w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok {s₀ s : State} {nl : Nat} (he : VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s) (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {tl al n : Nat} (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) {nonce : List Byte}
    (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (b0 y) s (VG.Proof.AesCcm.Arm.MacStep k w sp R (14 - nl) s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n])) := by
  refine VG.Proof.AesCcm.Arm.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.Arm.b0Pre_ok L he hk etl eal en hnl h7 h13 ht4 ht16 hte hal hn4 hn hc0 hy)
    fun s₃ ⟨he₃, rd₃, wr₃, _, f₃, hz, hB⟩ => ?_))
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.Arm.updBlock_ok L he₃ hR hy) fun s₄ ⟨he₄, rd₄, wr₄, _, f₄, o₄⟩ =>
    ⟨he₄, ?_, ?_, by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩
  · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact VG.Proof.AesCcm.Arm.sub_mac (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesCcm.Arm.sub_mac (by simp)
  · rw [o₄, hz, hB, ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w' (by decide)
      · exact L.k_w' (by omega)) hRb]

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok {s₀ s : State} {nl : Nat} (he : VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s) (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s) (hsp₀ : s₀.sp = sp)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {A D : BitVec 32} {tl al n : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) {nonce : List Byte}
    (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) (hA : VG.Proof.AesCcm.Arm.Buf w sp s A al) (hD : VG.Proof.AesCcm.Arm.Buf w sp s D n) :
    WP isa (VG.Impl.AesCcm.Arm.mac y) s (VG.Proof.AesCcm.Arm.MacStep k w sp R (14 - nl) s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem (State.addr A) al) (bytesAt s.mem (State.addr D) n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.b0_ok L he hk hR etl eal en hnl h7 h13 ht4 ht16 hte hal hn4 hn hc0 hy)
    fun s₁ M₁ => ?_)
  have hk₁ := hk.mac hsp₀ hy16 M₁.frame (by rw [M₁.env.sp, he.sp]) M₁.rd M₁.wr
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.aad_ok L M₁.env hR hy hk₁ eA eal hal (hA.of_eq M₁.rd M₁.wr)) fun s₂ M₂ => ?_)
  have hk₂ := hk₁.mac hsp₀ hy16 M₂.frame (by rw [M₂.env.sp, M₁.env.sp]) M₂.rd M₂.wr
  obtain ⟨s₃, run₃, h4₃, h5₃, g₃, k₃⟩ := VG.Proof.AesCcm.Arm.dataLd_ok hk₂ eD en
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := M₂.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) k₃.sp k₃.rd k₃.wr
  have rd₃ : s₃.rd = s.rd := by rw [k₃.rd, M₂.rd, M₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [k₃.wr, M₂.wr, M₁.wr]
  refine WP.mono (VG.Proof.AesCcm.Arm.absorbPad_ok L he₃ hR hy (fun _ => hD.of_eq rd₃ wr₃) hn4 h4₃ h5₃) fun s₄ A₄ => ?_
  have f₂ : Frame (VG.Proof.AesCcm.Arm.macR w sp y) s.mem s₂.mem := M₁.frame.trans M₂.frame
  have f₃ : Frame (VG.Proof.AesCcm.Arm.macR w sp y) s.mem s₃.mem := by rw [k₃.mem]; exact f₂
  have hkm := VG.Proof.AesCcm.Arm.k_macR L hy16
  refine ⟨A₄.env, f₃.trans A₄.frame, ?_, by rw [A₄.rd, rd₃], by rw [A₄.wr, wr₃]⟩
  have hl : nonce.length ≤ 15 := by omega
  rw [A₄.out, k₃.mem, M₂.out, M₁.out, ctxCiph_frame f₂ hkm hRb, ctxCiph_frame M₁.frame hkm hRb,
    VG.Proof.AesCcm.Arm.buf_kept hD hy16 f₂, VG.Proof.AesCcm.Arm.buf_kept hA hy16 M₁.frame, format_eq tl hl, length_bytesAt, length_bytesAt,
    Proof.Cmac.chain_append, Proof.Cmac.chain_append]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Crypt`. -/
section

/-!
# AES-CCM on ARMv7: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctrWhole` XORs the whole
blocks of the data with the keystream from `Ctr₁`, by one call of
`vg_aes_ctr32` from `Ctr₁` at `W + 64`, whose counters do not wrap around
(`ctrWhole_ok`, `Proof.AesCcm.ctr32_ccm`); `ctrTail` the last bytes with the
first bytes of `CIPH_K(Ctrⱼ)` for the block `j` after them, computed by
`vg_aes_ctr32` on a zero block at `W + 80` (`ctrTail_ok`). Together, the
data XORed with CCM's keystream from `Ctr₁` (`ctr_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 xorLoop ctrFrame)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre xorLoop_ok xorBytes bytesAt_frame runBlock_app_of and15 shr4 toNat32
  ofNat_sub32 ofNat_add32 z_cmp eval_eq' Keeps z_subFlags gpr_subFlags covers_prefix covers_off covers_left
  ctr_call CtrPost CtrCall add32_ofNat_assoc)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom ctr32_ccm repeat_inc32_ctrBlock xorFrom_zeros
  xorFrom_tail xorFrom_append BlockCipher bytesAt_prefix bytesAt_writeBytes_base)

/-- The data: `n` bytes at `D` that the code may write, apart from `W`, the
key schedule and the stack below `sp`. -/
structure Dat (k w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  buf : VG.Proof.AesCcm.Arm.Buf w sp s D n
  wr : Covers [⟨State.addr D, n⟩] s.wr
  k : (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr D, n⟩

theorem Dat.of_eq {k w sp : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesCcm.Arm.Dat k w sp s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.Dat k w sp s' D n :=
  ⟨h.buf.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.k⟩

/-- What `ctr` writes: the counter block and the keystream block at
`W + 64`, the working space of the functions called, the stack below `sp`
and the data. -/
abbrev ctrR (w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp, ⟨State.addr D, n⟩]

theorem pow_q {q : Nat} (h : 2 ≤ q) : 256 ^ q = 256 * 256 ^ (q - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp)
include L

/-- `Ctr₁` at `W + 64`, and the arguments of the call in `ctrWhole`, for the
`n / 16` whole blocks of the data at `D`. -/
theorem ctrWholeArgs_ok {s₁ : State} (he₁ : VG.Proof.AesCcm.Arm.Env k w sp R q1 s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0₁ : bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (hD : VG.Proof.AesCcm.Arm.Dat k w sp s₁ D n) (h4₁ : s₁.gpr .r4 = D)
    (h12₁ : s₁.gpr .r12 = BitVec.ofNat 32 (n / 16)) :
    ∃ s₄, runBlock isa (([.mov .r0 (imm 1)] : List Instr) ++ ctrAt ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr)) s₁ = some s₄ ∧
      CtrCall s₄ k (w + BitVec.ofNat 32 64) D (w + BitVec.ofNat 32 384) R (n / 16) ∧ VG.Proof.AesCcm.Arm.Env k w sp R q1 s₄ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₄.gpr r = s₁.gpr r) ∧
      s₄.rd = s₁.rd ∧ s₄.wr = s₁.wr ∧ s₄.sp = s₁.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s₁.mem s₄.mem ∧
      bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 1 := by
  have hq2 : 2 ≤ 15 - nonce.length := by omega
  have hp := VG.Proof.AesCcm.Arm.pow_q hq2
  obtain ⟨s₂, run₂, h0₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.mov .r0 (imm 1)] s₁ = some s₂ ∧
      s₂.gpr .r0 = BitVec.ofNat 32 1 ∧ (∀ r, r ≠ .r0 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) k₂.sp k₂.rd k₂.wr
  have hm2 : 1 < 256 ^ min (15 - nonce.length) 4 := Nat.one_lt_pow (by omega) (by decide)
  obtain ⟨s₃, run₃, hc₃, f₃, g₃, rd₃, wr₃, sp₃⟩ := VG.Proof.AesCcm.Arm.ctrAt_ok L he₂ h7 h13
    (by rw [k₂.mem]; exact hc0₁) h0₂ hm2
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) sp₃ rd₃ wr₃
  obtain ⟨s₄, run₄, a0, a1, a2, a3, a12, alr, g₄, k₄⟩ : ∃ s₄, runBlock isa (ctrArgs ++ [.mov .r3 (.reg .r4)]) s₃ =
      some s₄ ∧ s₄.gpr .r0 = k ∧ s₄.gpr .r1 = BitVec.ofNat 32 R ∧ s₄.gpr .r2 = w + BitVec.ofNat 32 64 ∧
      s₄.gpr .r3 = D ∧ s₄.gpr .r12 = BitVec.ofNat 32 (n / 16) ∧ s₄.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₄.gpr r = s₃.gpr r) ∧ Keeps s₃ s₄ := by
    have r4₃ : s₃.gpr .r4 = D := by
      rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), h4₁]
    have r12₃ : s₃.gpr .r12 = BitVec.ofNat 32 (n / 16) := by
      rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), h12₁]
    refine ⟨_, by simp only [ctrArgs, c1O, scrO]; arun [he₃.r9, he₃.r8, he₃.r11], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₃.r9]
    · simp [gpr_setReg, he₃.r8]
    · simp [gpr_setReg, he₃.r11]
    · simp [gpr_setReg, r4₃]
    · simp [gpr_setReg, r12₃]
    · simp [gpr_setReg, he₃.r11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) k₄.sp k₄.rd k₄.wr
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hq := hD.buf.take hb
  have e64 := L.wA (d := 64) (by decide)
  have C₄ := VG.Proof.AesCcm.Arm.ctrCall_of L he₄ hR (D := D) (n := n / 16) a0 a1 a2 a3 a12 alr hq.fit
    (hD.k.sub_right (Region.sub_prefix hb)) (hq.w.sub_right (Lay.wSub (by decide))).symm
    (hq.w.sub_right (Lay.wSub (by decide))) hq.stk
    (by rw [k₄.wr, wr₃, k₂.wr]; exact covers_prefix hD.wr hb)
  refine ⟨s₄, by
    rw [show [.mov .r0 (imm 1)] ++ ctrAt ++ ctrArgs ++ [.mov .r3 (.reg .r4)] =
      [.mov .r0 (imm 1)] ++ (ctrAt ++ (ctrArgs ++ [.mov .r3 (.reg .r4)])) by simp]
    exact runBlock_app_of run₂ (runBlock_app_of run₃ run₄), C₄, he₄, fun r a b c d e => by rw [g₄ r a b c d e, g₃ r a b, g₂ r a],
    by rw [k₄.rd, rd₃, k₂.rd], by rw [k₄.wr, wr₃, k₂.wr], by rw [k₄.sp, sp₃, k₂.sp],
    by rw [k₄.mem, ← k₂.mem]; exact f₃, by rw [k₄.mem]; exact hc₃⟩

/-- The whole blocks of the data, from `Ctr₁`. -/
theorem ctrWhole_ok {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (hD : VG.Proof.AesCcm.Arm.Dat k w sp s D n) (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa ctrWhole s fun s' => VG.Proof.AesCcm.Arm.Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp, ⟨State.addr D, 16 * (n / 16)⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) (16 * (n / 16)) =
        xorFrom (Spec.Ccm.ctxCiph s.mem (State.addr k) R) nonce 1 (bytesAt s.mem (State.addr D) (16 * (n / 16))) := by
  obtain ⟨s₁, run₁, h12₁, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split16_ok hn4 h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (n / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, k₁.rd, k₁.wr, fun r hr _ => g₁ r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      by rw [k₁.mem]; exact Frame.refl _ _, ?_⟩
    rw [k₁.mem, h0]; rfl
  · have h0 : n / 16 ≠ 0 := by simpa using hf
    obtain ⟨s₄, run₄, C₄, he₄, g₄, rd₄, wr₄, sp₄, f₀₄', hc₄⟩ := VG.Proof.AesCcm.Arm.ctrWholeArgs_ok L he₁ hR h7 h13
      (by rw [k₁.mem]; exact hc0) (hD.of_eq k₁.rd k₁.wr) (by rw [g₁ _ (by decide), h4]) h12₁
    have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
    have hq := hD.buf.take hb
    have e64 := L.wA (d := 64) (by decide)
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    refine WP.mono (ctr_call C₄) fun s₅ h => ?_
    have hsp₄ : s₄.sp = sp := he₄.sp
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    -- Memory before the call: only `W + 64` changed.
    have f₀₄ : Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s.mem s₄.mem := by
      rw [← k₁.mem]; exact f₀₄'
    have hK₄ : Spec.Ccm.ctxCiph s₄.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R :=
      ctxCiph_frame f₀₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have hD₄ : bytesAt s₄.mem (State.addr D) (16 * (n / 16)) = bytesAt s.mem (State.addr D) (16 * (n / 16)) :=
      bytesAt_frame f₀₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hq.w.sub_right (Lay.wSub (by decide)))
        (by have := hq.lt; omega)
    refine ⟨he₄.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, rd₄, k₁.rd],
      by rw [h.wr, wr₄, k₁.wr], fun r hr hlr => ?_, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h.saved r hr hlr, g₄ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 hlr, g₁ r a.2.2.2.2]
    · have f₅ := h.frame
      rw [hsp₄, e64, L.wA (d := 384) (by decide)] at f₅
      refine (f₀₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨VG.Proof.AesCcm.Arm.scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨VG.Proof.AesCcm.Arm.blw sp, by simp, VG.Proof.AesCcm.Arm.below_blw sp⟩
    · have hc := ctr32_ccm (m := s₄.mem) (m' := s₅.mem) (K := State.addr k) (C := State.addr (w + BitVec.ofNat 32 64))
        (D := State.addr D) (R := R) (nonce := nonce) (by omega) (j := 1) (k := n / 16)
        (fun i hi => by
          have e : Spec.Gcm.blockAt s₄.mem (State.addr (w + BitVec.ofNat 32 64)) =
              Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce 1) := by
            show Spec.Gcm.ofBytes _ = _
            rw [e64, hc₄]
          rw [e]
          exact repeat_inc32_ctrBlock h7 h13 (j := 1) (k := n / 16) (by omega) (by omega) i hi) h.out
      rw [hc, hK₄, hD₄]

/-- `Ctrⱼ` at `W + 64` for the block `j` after the whole ones, a zero block at
`W + 80`, and the arguments of the call in `ctrTail`. -/
theorem ctrTailArgs_ok {s₁ : State} (he₁ : VG.Proof.AesCcm.Arm.Env k w sp R q1 s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0₁ : bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {n : Nat} (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32) (h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₅, runBlock isa (zero16 ksO ++ ([.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] : List Instr) ++ ctrAt ++
        ctrArgs ++ ([addI .r3 .r11 ksO, .mov .r12 (imm 1)] : List Instr)) s₁ = some s₅ ∧
      CtrCall s₅ k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 80) (w + BitVec.ofNat 32 384) R 1 ∧
      VG.Proof.AesCcm.Arm.Env k w sp R q1 s₅ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s₁.gpr r) ∧
      s₅.rd = s₁.rd ∧ s₅.wr = s₁.wr ∧ s₅.sp = s₁.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩] s₁.mem s₅.mem ∧
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (n / 16 + 1) ∧
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 := by
  have hq2 : 2 ≤ 15 - nonce.length := by omega
  have hp := VG.Proof.AesCcm.Arm.pow_q hq2
  have hj : n / 16 + 1 < 256 ^ min (15 - nonce.length) 4 := by
    rcases Nat.le_total (15 - nonce.length) 4 with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; show n / 16 + 1 < 4294967296; omega
  obtain ⟨s₂, run₂, hm₂, g₂, rd₂, wr₂, sp₂, -⟩ := VG.Proof.AesCcm.Arm.zero16_ok L he₁ (d := ksO) (by decide) (by decide)
  simp only [ksO] at hm₂
  obtain ⟨s₃, run₃, h0₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] s₂ =
      some s₃ ∧ s₃.gpr .r0 = BitVec.ofNat 32 (n / 16 + 1) ∧ (∀ r, r ≠ .r0 → s₃.gpr r = s₂.gpr r) ∧
      Keeps s₂ s₃ := by
    have r5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n := by rw [g₂ _ (by decide), h5₁]
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, r5₂, VG.Proof.AesGcm.Arm.shr4 hn4, imm, ofNat_add32]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₃ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [g₃ _ (by decide), g₂ _ (by decide)])
    (k₃.sp.trans sp₂) (k₃.rd.trans rd₂) (k₃.wr.trans wr₂)
  have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 80, 16⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have hc₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [k₃.mem, bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]; exact hc0₁
  obtain ⟨s₄, run₄, hc₄, f₄, g₄, rd₄, wr₄, sp₄⟩ := VG.Proof.AesCcm.Arm.ctrAt_ok L he₃ h7 h13 hc₃ h0₃ hj
  have he₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) sp₄ rd₄ wr₄
  obtain ⟨s₅, run₅, a0, a1, a2, a3, a12, alr, g₅, k₅⟩ : ∃ s₅, runBlock isa (ctrArgs ++
      [addI .r3 .r11 ksO, .mov .r12 (imm 1)]) s₄ = some s₅ ∧
      s₅.gpr .r0 = k ∧ s₅.gpr .r1 = BitVec.ofNat 32 R ∧ s₅.gpr .r2 = w + BitVec.ofNat 32 64 ∧
      s₅.gpr .r3 = w + BitVec.ofNat 32 80 ∧ s₅.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₅.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s₄.gpr r) ∧
      Keeps s₄ s₅ := by
    refine ⟨_, by simp only [ctrArgs, c1O, scrO, ksO]; arun [he₄.r9, he₄.r8, he₄.r11], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · simp [gpr_setReg, he₄.r9]
    · simp [gpr_setReg, he₄.r8]
    · simp [gpr_setReg, he₄.r11]
    · simp [gpr_setReg, he₄.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₄.r11]
    · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) k₅.sp k₅.rd k₅.wr
  have e64 := L.wA (d := 64) (by decide)
  have e80 := L.wA (d := 80) (by decide)
  have C₅ := VG.Proof.AesCcm.Arm.ctrCall_of L he₅ hR (D := w + BitVec.ofNat 32 80) (n := 1) a0 a1 a2 a3 a12 alr
    (by rw [L.wN (by decide)]; have := L.ww; omega) (by rw [e80]; exact L.k_w' (by decide))
    (by rw [e80]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [e80]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [e80]; exact L.stk_w' (by decide)) (by rw [e80]; exact he₅.perm.wC (by decide))
  refine ⟨s₅, by
    rw [show zero16 ksO ++ [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++ ctrAt ++ ctrArgs ++
      [addI .r3 .r11 ksO, .mov .r12 (imm 1)] = zero16 ksO ++ ([.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++
      (ctrAt ++ (ctrArgs ++ [addI .r3 .r11 ksO, .mov .r12 (imm 1)]))) by simp]
    exact runBlock_app_of run₂ (runBlock_app_of run₃ (runBlock_app_of run₄ run₅)), C₅, he₅, fun r a b c d e f => by rw [g₅ r a b c d e f, g₄ r a b, g₃ r a, g₂ r a],
    by rw [k₅.rd, rd₄, k₃.rd, rd₂], by rw [k₅.wr, wr₄, k₃.wr, wr₂], by rw [k₅.sp, sp₄, k₃.sp, sp₂], ?_,
    by rw [k₅.mem]; exact hc₄, ?_⟩
  · rw [k₅.mem]
    refine (f₂.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · rw [← k₃.mem]
      exact f₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · rw [k₅.mem, bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), k₃.mem, hm₂]
    exact VG.Proof.AesCcm.Arm.store4_zero_bytes' _ _

/-- The last bytes of the data, with `CIPH_K(Ctrⱼ)` for the block `j` after
the whole ones. -/
theorem ctrTail_ok {t : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 t) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (hD : VG.Proof.AesCcm.Arm.Dat k w sp t D n) (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32)
    (h4 : t.gpr .r4 = D) (h5 : t.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa ctrTail t fun t' => VG.Proof.AesCcm.Arm.Env k w sp R q1 t' ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ preserved, r ≠ .r6 → r ≠ .lr → t'.gpr r = t.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp,
        ⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] t.mem t'.mem ∧
      bytesAt t'.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
        xorFrom (Spec.Ccm.ctxCiph t.mem (State.addr k) R) nonce (1 + n / 16)
          (bytesAt t.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) := by
  obtain ⟨s₁, run₁, h6₁, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split15_ok hn4 h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (n % 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, k₁.rd, k₁.wr, fun r hr h6 _ => g₁ r h6, by rw [k₁.mem]; exact Frame.refl _ _, ?_⟩
    rw [k₁.mem, h0]; rfl
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    obtain ⟨s₅, run₅, C₅, he₅, g₅, rd₅, wr₅, sp₅, f₀₅', hc₄, hz₅⟩ := VG.Proof.AesCcm.Arm.ctrTailArgs_ok L he₁ hR h7 h13
      (by rw [k₁.mem]; exact hc0) hn hn4 (by rw [g₁ _ (by decide), h5])
    have e64 := L.wA (d := 64) (by decide)
    have e80 := L.wA (d := 80) (by decide)
    refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
    refine WP.seq (WP.mono (ctr_call C₅) fun s₆ h => ?_)
    have he₆ := he₅.of_saved h.saved h.sp h.rd h.wr
    have hsp₅ : s₅.sp = sp := he₅.sp
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    have g₆ : ∀ r ∈ preserved, r ≠ .r6 → r ≠ .lr → s₆.gpr r = t.gpr r := fun r hr h6 hlr => by
      have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h.saved r hr hlr, g₅ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr, g₁ r h6]
    -- Memory before the call: `W + 64` and `W + 80` changed.
    have f₀₅ : Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩] t.mem s₅.mem := by
      rw [← k₁.mem]; exact f₀₅'
    have hK₅ : Spec.Ccm.ctxCiph s₅.mem (State.addr k) R = Spec.Ccm.ctxCiph t.mem (State.addr k) R :=
      ctxCiph_frame f₀₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have hBC : BlockCipher (Spec.Ccm.ctxCiph t.mem (State.addr k) R) := fun x => Proof.Cmac.aesWith_length _ _ x
    have hks : bytesAt s₆.mem (State.addr w + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph t.mem (State.addr k) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1)) := by
      have hx := ctr32_ccm (m := s₅.mem) (m' := s₆.mem) (K := State.addr k) (C := State.addr (w + BitVec.ofNat 32 64))
        (D := State.addr (w + BitVec.ofNat 32 80)) (R := R) (nonce := nonce) (by omega) (j := n / 16 + 1) (k := 1)
        (fun i hi => by
          rw [show i = 0 by omega, Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [e64, hc₄]) h.out
      rw [Nat.mul_one, e80] at hx
      rw [hx, hz₅, hK₅, xorFrom_zeros hBC]
    -- The arguments of the XOR.
    have h11 := he₆.r11
    have hb : 16 * (n / 16) < n := by omega
    have eD := hD.buf.addr (j := 16 * (n / 16)) hb
    obtain ⟨s₇, run₇, a1₇, a2₇, a3₇, g₇, k₇⟩ : ∃ s₇, runBlock isa [addI .r1 .r11 ksO, .dp .sub .r2 .r5 (.reg .r6),
        .dp .add .r2 .r2 (.reg .r4), .mov .r3 (.reg .r6)] s₆ = some s₇ ∧
        s₇.gpr .r1 = w + BitVec.ofNat 32 80 ∧ s₇.gpr .r2 = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
        s₇.gpr .r3 = BitVec.ofNat 32 (n % 16) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₇.gpr r = s₆.gpr r) ∧ Keeps s₆ s₇ := by
      have r4₆ : s₆.gpr .r4 = D := by rw [g₆ _ (by decide) (by decide) (by decide), h4]
      have r5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n := by rw [g₆ _ (by decide) (by decide) (by decide), h5]
      have r6₆ : s₆.gpr .r6 = BitVec.ofNat 32 (n % 16) := by
        rw [h.saved _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h6₁]
      have hsub : BitVec.ofNat 32 n - BitVec.ofNat 32 (n % 16) = BitVec.ofNat 32 (16 * (n / 16)) := by
        rw [ofNat_sub32 (Nat.mod_le _ _) hn4]; congr 1; omega
      refine ⟨_, by simp only [ksO]; arun [h11], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h11]
      · simp [gpr_setReg, r4₆, r5₆, r6₆, hsub, BitVec.add_comm]
      · simp [gpr_setReg, r6₆]
      · intro r a b c; simp [gpr_setReg, a, b, c]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
    have hT := (hD.buf.sub (j := 16 * (n / 16)) (k := n % 16) (by omega) (by omega))
    have hTw := hT.w
    have hTs := hT.stk
    rw [eD] at hTw hTs
    have wr₇ : s₇.wr = t.wr := by rw [k₇.wr, h.wr, wr₅, k₁.wr]
    have rd₇ : s₇.rd = t.rd := by rw [k₇.rd, h.rd, rd₅, k₁.rd]
    have lp : LoopPre s₇ (w + BitVec.ofNat 32 80) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨a1₇, a2₇, a3₇, by omega, by omega, by rw [L.wN (by decide)]; have := L.ww; omega, hT.fit, ?_, ?_, ?_⟩
      · rw [e80]; exact covers_left ((he₆.perm.of_eq k₇.rd k₇.wr).wC (by omega))
      · rw [wr₇, eD]; exact covers_off hD.wr (by omega) hD.buf.lt
      · rw [e80, eD]; exact (hTw.sub_right (Lay.wSub (by omega))).symm
    refine WP.mono (xorLoop_ok s₇ lp) fun s₈ ⟨hm₈, lo⟩ => ?_
    rw [e80, eD] at hm₈
    have hxl : (xorBytes s₇.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16)))
        (State.addr w + BitVec.ofNat 64 80) (n % 16)).length = n % 16 := by
      simp [xorBytes, length_bytesAt]
    -- What was written.
    have fC : Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp] t.mem s₇.mem := by
      have fc := h.frame
      rw [hsp₅, e64, e80, L.wA (d := 384) (by decide)] at fc
      rw [k₇.mem]
      refine (f₀₅.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨VG.Proof.AesCcm.Arm.scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨VG.Proof.AesCcm.Arm.blw sp, by simp, VG.Proof.AesCcm.Arm.below_blw sp⟩
    have fw : Frame [⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] s₇.mem s₈.mem := by
      rw [hm₈]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
    refine ⟨he₆.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
            g₇ _ (by decide) (by decide) (by decide)]) (lo.sp.trans k₇.sp) (lo.rd.trans k₇.rd) (lo.wr.trans k₇.wr),
      by rw [lo.rd, rd₇], by rw [lo.wr, wr₇], fun r hr h6 hlr => ?_, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [lo.other r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2, g₇ r a.2.1 a.2.2.1 a.2.2.2.1, g₆ r hr h6 hlr]
    · refine (fC.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · have h₂ : bytesAt s₇.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
          bytesAt t.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
        bytesAt_frame fC (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hTw.sub_right (Lay.wSub (by decide))
          · exact hTw.sub_right (Lay.wSub (by decide))
          · exact hTs.symm) (by omega)
      have hk₇ : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 80) (n % 16) =
          (Spec.Ccm.ctxCiph t.mem (State.addr k) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1))).take (n % 16) := by
        rw [bytesAt_prefix _ _ (show n % 16 ≤ 16 by omega), k₇.mem, hks]
      have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph t.mem (State.addr k) R) nonce (n / 16 + 1)
        (d := bytesAt t.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
        (by rw [length_bytesAt]; omega)
      rw [length_bytesAt, hBC] at ht
      have ht' := ht.resolve_right (by omega)
      rw [hm₈, bytesAt_writeBytes_base _ _ _ (by rw [hxl]) (by omega), hxl, List.drop_eq_nil_of_le
        (by rw [length_bytesAt]), List.append_nil, xorBytes, h₂, hk₇, ht', Nat.add_comm 1]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok {s₀ s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (hD : VG.Proof.AesCcm.Arm.Dat k w sp s D n) (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32) :
    WP isa VG.Impl.AesCcm.Arm.ctr s fun s' => VG.Proof.AesCcm.Arm.Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (VG.Proof.AesCcm.Arm.ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n =
        xorFrom (Spec.Ccm.ctxCiph s.mem (State.addr k) R) nonce 1 (bytesAt s.mem (State.addr D) n) := by
  obtain ⟨s₁, run₁, h4₁, h5₁, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.dataLd_ok hk eD en
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hD₁ := hD.of_eq k₁.rd k₁.wr
  rw [← k₁.mem] at hc0
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.ctrWhole_ok L he₁ hR h7 h13 hc0 hD₁ hn hn4 h4₁ h5₁) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_)
  have hDw := hD.buf.w
  have hDs := hD.buf.stk
  have dP : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp],
      (⟨State.addr D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 a, l⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hDw.sub_left hs).sub_right (Lay.wSub (by decide))
    · exact (hDw.sub_left hs).sub_right (Lay.wSub (by decide))
    · exact (hDs.sub_right hs).symm
  have kD : ∀ r ∈ [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, VG.Proof.AesCcm.Arm.scrR w, VG.Proof.AesCcm.Arm.blw sp, ⟨State.addr D, 16 * (n / 16)⟩],
      (⟨State.addr k, 240⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.stk_k.symm
    · exact hD.k.sub_right (Region.sub_prefix hb)
  have hc₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm
      · exact (hDw.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)) |>.symm) (by decide)]
    exact hc0
  have r4₂ : s₂.gpr .r4 = D := by rw [g₂ _ (by decide) (by decide), h4₁]
  have r5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n := by rw [g₂ _ (by decide) (by decide), h5₁]
  refine WP.mono (VG.Proof.AesCcm.Arm.ctrTail_ok L he₂ hR h7 h13 hc₂ (hD₁.of_eq rd₂ wr₂) hn hn4 r4₂ r5₂)
    fun s₃ ⟨he₃, rd₃, wr₃, g₃, f₃, o₃⟩ => ?_
  have f₁₂ : Frame (VG.Proof.AesCcm.Arm.ctrR w sp D n) s.mem s₂.mem := by
    rw [← k₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr D, n⟩, by simp, Region.sub_prefix hb⟩
  refine ⟨he₃, by rw [rd₃, rd₂, k₁.rd], by rw [wr₃, wr₂, k₁.wr], fun r hr h4 h5 h6 hlr => ?_,
    f₁₂.trans (f₃.sub fun r hr => ?_), ?_⟩
  · rw [g₃ r hr h6 hlr, g₂ r hr hlr, g₁ r h4 h5]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨State.addr D, n⟩, by simp, Offset.sub_base _ (by omega)⟩
  · have hs : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16
    have hK₂ : Spec.Ccm.ctxCiph s₂.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R := by
      rw [ctxCiph_frame f₂ kD hRb, k₁.mem]
    -- The whole blocks, which the tail keeps.
    have h₁ : bytesAt s₃.mem (State.addr D) (16 * (n / 16)) = bytesAt s₂.mem (State.addr D) (16 * (n / 16)) :=
      bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hDw.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide))
        · exact (hDw.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide))
        · exact (hDs.sub_right (Region.sub_prefix hb)).symm
        · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hD.buf.lt; omega)) (by have := hD.buf.lt; omega)
    -- The rest, which the whole blocks keep.
    have h₂ : bytesAt s₂.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
        bytesAt s.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
      rw [bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dP (by omega) _ (List.mem_cons_self ..)
        · exact dP (by omega) _ (by simp)
        · exact dP (by omega) _ (by simp)
        · exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hD.buf.lt; omega)) (by omega), k₁.mem]
    have split : ∀ m : Mem, bytesAt m (State.addr D) n = bytesAt m (State.addr D) (16 * (n / 16)) ++
        bytesAt m (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := fun m => by
      conv => lhs; rw [← hs]
      exact Proof.Cmac.Stream.bytesAt_append _ _ _ _
    rw [split, split, h₁, o₂, o₃, hK₂, h₂, k₁.mem, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1]

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Args`. -/
section

/-!
# AES-CCM on ARMv7: the arguments, and what the pieces write

Untrusted: everything here is checked by Lean. What the contracts'
preconditions give about the arguments (`Args`, `TagB`, `args_of_seal`,
`args_of_open`), and the regions
the pieces after the entry write (`mutR`: `W` but for our caller's saved
registers, the stack below `sp` and the data), which miss the saved
registers, the key schedule, the stack arguments, the nonce and the
associated data.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (covers_left covers_of_mem savedR bytesAt_frame ArgsKeep)

/-- What the arguments of `seal` and `open` are. -/
structure Args (s : State) (k w N A D : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : VG.Proof.AesCcm.Arm.Lay k w s.sp
  perm : VG.Proof.AesCcm.Arm.Perm k w s
  stk : VG.Proof.AesCcm.Arm.Stk w s s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : VG.Proof.AesCcm.Arm.Buf w s.sp s N nl
  aad : VG.Proof.AesCcm.Arm.Buf w s.sp s A al
  data : VG.Proof.AesCcm.Arm.Dat k w s.sp s D n
  nd : (⟨State.addr N, nl⟩ : Region).Disjoint ⟨State.addr D, n⟩
  ad : (⟨State.addr A, al⟩ : Region).Disjoint ⟨State.addr D, n⟩
  da : (⟨State.addr D, n⟩ : Region).Disjoint (VG.Proof.AesCcm.Arm.args s 7)
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  n32 : n < 2 ^ 32
  al32 : al < 2 ^ 32

/-- The tag, the `tl` bytes at `T`: apart from the data, `W` and the stack
below `sp`. -/
structure TagB (w sp D : BitVec 32) (n : Nat) (T : BitVec 32) (tl : Nat) : Prop where
  d : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr D, n⟩
  w : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (VG.Proof.AesCcm.Arm.blw sp).Disjoint ⟨State.addr T, tl⟩
  wrap : T.toNat + tl ≤ 2 ^ 32

/-- `Args` and `TagB` from the layout, with the buffers covered as each
function's permissions say. -/
theorem args_of_lay {s : State} (h : VG.Proof.AesCcm.Arm.oneLay s)
    (hk : Covers [⟨State.addr (s.gpr .r0), 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨State.addr (VG.Proof.AesCcm.Arm.arg s 0), (VG.Proof.AesCcm.Arm.arg s 1).toNat⟩] (s.rd ++ s.wr)) (ha : VG.Proof.AesCcm.Arm.args s 7 ∈ s.rd)
    (hD : Covers [⟨State.addr (VG.Proof.AesCcm.Arm.arg s 2), (VG.Proof.AesCcm.Arm.arg s 3).toNat⟩] s.wr) (hW : Covers [⟨State.addr (VG.Proof.AesCcm.Arm.arg s 6), 2560⟩] s.wr) :
    VG.Proof.AesCcm.Arm.Args s (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 5).toNat ∧
      VG.Proof.AesCcm.Arm.TagB (VG.Proof.AesCcm.Arm.arg s 6) s.sp (VG.Proof.AesCcm.Arm.arg s 2) (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 4) (VG.Proof.AesCcm.Arm.arg s 5).toNat := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5, sp16, sp28, hR,
    hv, t1, t2, t3, t4⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact ⟨{
    lay := ⟨f1, f5, sp16, d2, b1, b5⟩
    perm := ⟨hk, hW⟩
    stk := ⟨ArgsKeep.refl 7 s, sp28, ha, d9.symm⟩
    rounds := hR
    nonce := ⟨hN, f2, d4, b2⟩
    aad := ⟨hA, f3, d6, b3⟩
    data := ⟨⟨covers_left hD, f4, d7, b4⟩, hD, d1⟩
    nd := d3
    ad := d5
    da := d8
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    n32 := BitVec.isLt _
    al32 := BitVec.isLt _ }, ⟨t1, t2, t3, t4⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : VG.Proof.AesCcm.Arm.sealPre s) :
    (VG.Proof.AesCcm.Arm.Args s (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 5).toNat ∧
      VG.Proof.AesCcm.Arm.TagB (VG.Proof.AesCcm.Arm.arg s 6) s.sp (VG.Proof.AesCcm.Arm.arg s 2) (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 4) (VG.Proof.AesCcm.Arm.arg s 5).toNat) ∧
      Covers [⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩] s.wr ∧
      (⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩ : Region).Disjoint (VG.Proof.AesCcm.Arm.args s 7) := by
  obtain ⟨hrd, hwr, hl, ht⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 0), (VG.Proof.AesCcm.Arm.arg s 1).toNat⟩, VG.Proof.AesCcm.Arm.args s 7], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (VG.Proof.AesCcm.Arm.arg s 2), (VG.Proof.AesCcm.Arm.arg s 3).toNat⟩ : Region), ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩,
      ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 6), 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesCcm.Arm.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (by rw [hrd]; simp)
    (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp), ht⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : VG.Proof.AesCcm.Arm.openPre s) :
    (VG.Proof.AesCcm.Arm.Args s (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 5).toNat ∧
      VG.Proof.AesCcm.Arm.TagB (VG.Proof.AesCcm.Arm.arg s 6) s.sp (VG.Proof.AesCcm.Arm.arg s 2) (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 4) (VG.Proof.AesCcm.Arm.arg s 5).toNat) ∧
      Covers [⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 0), (VG.Proof.AesCcm.Arm.arg s 1).toNat⟩, ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 4), (VG.Proof.AesCcm.Arm.arg s 5).toNat⟩, VG.Proof.AesCcm.Arm.args s 7],
      Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (VG.Proof.AesCcm.Arm.arg s 2), (VG.Proof.AesCcm.Arm.arg s 3).toNat⟩ : Region), ⟨State.addr (VG.Proof.AesCcm.Arm.arg s 6), 2560⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesCcm.Arm.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (by rw [hrd]; simp)
    (mwr _ (by simp)) (mwr _ (by simp)), mrd _ (by simp)⟩

/-- What the pieces after the entry write: `W` but for the saved registers,
the stack below `sp` and the data. -/
abbrev mutR (w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr w, 128⟩, ⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, VG.Proof.AesCcm.Arm.blw sp, ⟨State.addr D, n⟩]

theorem w_mut {w sp D : BitVec 32} {n a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, Region.Sub ⟨State.addr w + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega)⟩

theorem blw_mut {w sp D : BitVec 32} {n : Nat} : ∃ r' ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, Region.Sub (VG.Proof.AesCcm.Arm.blw sp) r' :=
  ⟨_, by simp, fun _ h => h⟩

theorem macR_mut {w sp D : BitVec 32} {n y : Nat} (hy : y = 0 ∨ y = 112) :
    ∀ r ∈ VG.Proof.AesCcm.Arm.macR w sp y, ∃ r' ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesCcm.Arm.w_mut (.inl (by omega))
  · exact VG.Proof.AesCcm.Arm.w_mut (.inl (by decide))
  · exact VG.Proof.AesCcm.Arm.w_mut (.inr ⟨by decide, by decide⟩)
  · exact VG.Proof.AesCcm.Arm.blw_mut

theorem ctrR_mut {w sp D : BitVec 32} {n : Nat} : ∀ r ∈ VG.Proof.AesCcm.Arm.ctrR w sp D n, ∃ r' ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesCcm.Arm.w_mut (.inl (by decide))
  · exact VG.Proof.AesCcm.Arm.w_mut (.inr ⟨by decide, by decide⟩)
  · exact VG.Proof.AesCcm.Arm.blw_mut
  · exact ⟨_, by simp, fun _ h => h⟩

section
variable {s : State} {k w N A D : BitVec 32} {R nl al n tl : Nat} (Ar : VG.Proof.AesCcm.Arm.Args s k w N A D R nl al n tl)
include Ar

theorem saved_mut : ∀ r ∈ VG.Proof.AesCcm.Arm.mutR w s.sp D n, (savedR w).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 36) (d := 0) (m := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (Ar.data.buf.w.sub_right (Lay.wSub (by decide))).symm

theorem k_mut : ∀ r ∈ VG.Proof.AesCcm.Arm.mutR w s.sp D n, (⟨State.addr k, 240⟩ : Region).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w' (by decide)
  · exact L.stk_k.symm
  · exact Ar.data.k

theorem args_mut : ∀ r ∈ VG.Proof.AesCcm.Arm.mutR w s.sp D n, (VG.Proof.AesCcm.Arm.args s 7).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.stk.aw.sub_right (Region.sub_prefix (by decide))
  · exact Ar.stk.aw.sub_right (Lay.wSub (by decide))
  · exact Ar.stk.blw_args rfl
  · exact Ar.da.symm

/-- The nonce and the associated data miss what the pieces write. -/
theorem nonce_mut : ∀ r ∈ VG.Proof.AesCcm.Arm.mutR w s.sp D n, (⟨State.addr N, nl⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.nonce.w.sub_right (Region.sub_prefix (by decide))
  · exact Ar.nonce.w.sub_right (Lay.wSub (by decide))
  · exact Ar.nonce.stk.symm
  · exact Ar.nd

theorem aad_mut : ∀ r ∈ VG.Proof.AesCcm.Arm.mutR w s.sp D n, (⟨State.addr A, al⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.aad.w.sub_right (Region.sub_prefix (by decide))
  · exact Ar.aad.w.sub_right (Lay.wSub (by decide))
  · exact Ar.aad.stk.symm
  · exact Ar.ad

end

/-- The tag misses what the pieces write. -/
theorem tag_mut {w sp D T : BitVec 32} {n tl : Nat} (hT : VG.Proof.AesCcm.Arm.TagB w sp D n T tl) :
    ∀ r ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, (⟨State.addr T, tl⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hT.w.sub_right (Region.sub_prefix (by decide))
  · exact hT.w.sub_right (Lay.wSub (by decide))
  · exact hT.stk.symm
  · exact hT.d

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Seal`. -/
section

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers in `W` and keeps `W`, the key schedule and the rounds in
registers (`entry_wp`); `Ctr₀` (`ctrs`) and `mac y` followed by `tag y`
leave the MAC of the payload, encrypted, at `W + y` (`front_wp`); `seal` then
encrypts the data (`ctr`), copies the tag to `tag` (`tagOut_ok`) and restores
the registers (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (savedR SavedAt restore_ok entry_ok covers_left bytesAt_frame Keeps LoopPre LoopOut
  copyLoop_ok covers_prefix writeBytes_frame' bytesAt_writeBytes_prefix)
open VG.Impl.AesGcm.Arm (copyLoop)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom length_xorFrom crypt_eq take_xorFrom_zero mac_eq
  BlockCipher bytesAt_prefix)

/-- What the pieces before the data is written change: `W` but for the
saved registers, and the stack below `sp`. -/
abbrev wR (w sp : BitVec 32) : List Region :=
  [⟨State.addr w, 128⟩, ⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, VG.Proof.AesCcm.Arm.blw sp]

theorem w_wR {w sp : BitVec 32} {a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ VG.Proof.AesCcm.Arm.wR w sp, Region.Sub ⟨State.addr w + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega)⟩

theorem wR_mut {w sp D : BitVec 32} {n : Nat} : ∀ r ∈ VG.Proof.AesCcm.Arm.wR w sp, ∃ r' ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

theorem macR_wR {w sp : BitVec 32} {y : Nat} (hy : y = 0 ∨ y = 112) :
    ∀ r ∈ VG.Proof.AesCcm.Arm.macR w sp y, ∃ r' ∈ VG.Proof.AesCcm.Arm.wR w sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesCcm.Arm.w_wR (.inl (by omega))
  · exact VG.Proof.AesCcm.Arm.w_wR (.inl (by decide))
  · exact VG.Proof.AesCcm.Arm.w_wR (.inr ⟨by decide, by decide⟩)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack below `sp` keeps its bytes. -/
theorem buf_wR {w sp : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : VG.Proof.AesCcm.Arm.Buf w sp s P len) {m m' : Mem}
    (hf : Frame (VG.Proof.AesCcm.Arm.wR w sp) m m') : bytesAt m' (State.addr P) len = bytesAt m (State.addr P) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

/-- The entry: our caller's registers saved in `W`, and `W`, the key schedule
and the rounds in `r11`, `r9` and `r8`. -/
theorem entry_wp {s₀ : State} {k w N A D : BitVec 32} {R nl al n tl : Nat} (Ar : VG.Proof.AesCcm.Arm.Args s₀ k w N A D R nl al n tl)
    (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (eW : stackArg s₀ 6 = w) :
    WP isa (.block entry) s₀ fun s₁ => VG.Proof.AesCcm.Arm.Env k w s₀.sp R (s₁.gpr .r10).toNat s₁ ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → s₁.gpr r = s₀.gpr r) ∧
      s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ SavedAt s₁.mem w s₀ ∧ Frame [savedR w] s₀.mem s₁.mem := by
  obtain ⟨i4, v4⟩ := Ar.stk.at 6 (by decide) (show 4 * 6 = 24 from rfl)
  rw [eW] at v4
  refine entry_ok (off := 24) (by decide) i4 (by rw [v4]; exact Ar.lay.ww) (by rw [v4]; exact Ar.perm.w)
    fun s' g12 g rd wr sp sv fr => ?_
  rw [v4] at g12 sv fr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, g .r1 (by decide), h1], by simp [gpr_setReg, g .r0 (by decide), h0],
    by simp [gpr_setReg], by simp [gpr_setReg, g12], sp, Perm.of_eq Ar.perm rd wr⟩, ?_, rd, wr, sv, fr⟩
  intro r a b c d; simp [gpr_setReg, a, b, c, g r d]

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, the
stack argument at `sp + 16`. -/
theorem tagOut_ok {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp) {s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s)
    {T : BitVec 32} {tl : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hli : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 20)) 4)
    (hlv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 20)) 32 = BitVec.ofNat 32 tl)
    (hTw : Covers [⟨State.addr T, tl⟩] s.wr) (hTf : T.toNat + tl ≤ 2 ^ 32)
    (hTW : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w, 2560⟩) :
    WP isa tagOut s fun s' => VG.Proof.AesCcm.Arm.Env k w sp R q1 s' ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr T) (bytesAt s.mem (State.addr w) tl) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, h1₁, h2₁, h3₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r1 (.reg .r11), .ldrSp .r2 16, .ldrSp .r3 20]
      s = some s₁ ∧ s₁.gpr .r1 = w ∧ s₁.gpr .r2 = T ∧ s₁.gpr .r3 = BitVec.ofNat 32 tl ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [hTi, hTv, hli, hlv], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg, hTv]
    · simp [gpr_setReg, hlv]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have ww := L.ww
  have lp : LoopPre s₁ w T tl :=
    ⟨h1₁, h2₁, h3₁, by omega, by omega, by omega, hTf, covers_left (covers_prefix he₁.perm.w (by omega)),
      by rw [k₁.wr]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, lo⟩ => ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr, by rw [hm₂, k₁.mem], by rw [lo.rd, k₁.rd], by rw [lo.wr, k₁.wr]⟩

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' {s₀ : State} {k w N A D T : BitVec 32} {R nl al n tl : Nat} (Ar : VG.Proof.AesCcm.Arm.Args s₀ k w N A D R nl al n tl)
    (Tb : VG.Proof.AesCcm.Arm.TagB w s₀.sp D n T tl) (hTw : Covers [⟨State.addr T, tl⟩] s₀.wr)
    (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (h2 : s₀.gpr .r2 = N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 nl) (eA : stackArg s₀ 0 = A) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) (eT : stackArg s₀ 4 = T)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eW : stackArg s₀ 6 = w) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) =
        (bytesAt s'.mem (State.addr D) n, bytesAt s'.mem (State.addr T) tl) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have hsavedK : (⟨State.addr k, 240⟩ : Region).Disjoint (savedR w) := L.k_w' (by decide)
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.entry_wp Ar h0 h1 eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, sv₁, f₁⟩ => ?_)
  have hent : ∀ {P : BitVec 32} {len : Nat}, VG.Proof.AesCcm.Arm.Buf w s₀.sp s₀ P len →
      bytesAt s₁.mem (State.addr P) len = bytesAt s₀.mem (State.addr P) len := fun hP =>
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.Ccm.ctxCiph s₁.mem (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R :=
    ctxCiph_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsavedK) hRb
  have hk₁ : VG.Proof.AesCcm.Arm.Stk w s₀ s₁ := Ar.stk.frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Ar.stk.aw.sub_right (Lay.wSub (by decide)))
    he₁.sp rd₁ wr₁
  -- `Ctr₀`.
  have hN₁ := Ar.nonce.of_eq rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.ctrs_ok L he₁ hN₁ (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]) Ar.h7 Ar.h13)
    fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have he₂ : VG.Proof.AesCcm.Arm.Env k w s₀.sp R (14 - nl) s₂ :=
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r11],
      by rw [sp₂, he₁.sp], he₁.perm.of_eq rd₂ wr₂⟩
  have f₂' : Frame (VG.Proof.AesCcm.Arm.wR w s₀.sp) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.Arm.w_wR (.inl (by decide))
  have hk₂ := hk₁.frame (f₂'.sub (VG.Proof.AesCcm.Arm.wR_mut (D := D) (n := n))) (VG.Proof.AesCcm.Arm.args_mut Ar) sp₂ rd₂ wr₂
  have rd₁₂ : s₂.rd = s₀.rd := rd₂.trans rd₁
  have wr₁₂ : s₂.wr = s₀.wr := wr₂.trans wr₁
  have hnl := length_bytesAt s₀.mem (State.addr N) nl
  have h7 : 7 ≤ (bytesAt s₀.mem (State.addr N) nl).length := by rw [hnl]; exact Ar.h7
  have h13 : (bytesAt s₀.mem (State.addr N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  -- The MAC.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.mac_ok L he₂ hk₂ rfl Ar.rounds eA eal eD en etl hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.al32 Ar.n32 Ar.hn c₂ (y := 0) (.inl rfl) (Ar.aad.of_eq rd₁₂ wr₁₂) (Ar.data.buf.of_eq rd₁₂ wr₁₂))
    fun s₃ M => ?_)
  have c₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₂]
  -- The encrypted MAC at `W`.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.tag_ok L M.env Ar.rounds h7 h13 c₃ (y := 0) (.inl rfl))
    fun s₄ ⟨he₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_)
  have f₄' : Frame (VG.Proof.AesCcm.Arm.wR w s₀.sp) s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.AesCcm.Arm.w_wR (.inl (by decide))
    · exact VG.Proof.AesCcm.Arm.w_wR (.inl (by decide))
    · exact VG.Proof.AesCcm.Arm.w_wR (.inr ⟨by decide, by decide⟩)
    · exact ⟨_, by simp, fun _ h => h⟩
  have G₄ : Frame (VG.Proof.AesCcm.Arm.wR w s₀.sp) s₁.mem s₄.mem := (f₂'.trans (M.frame.sub (VG.Proof.AesCcm.Arm.macR_wR (.inl rfl)))).trans f₄'
  have F₄ : Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem s₄.mem := G₄.sub VG.Proof.AesCcm.Arm.wR_mut
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, M.rd, rd₁₂]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, M.wr, wr₁₂]
  have c₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₃]
  have hk₄ := hk₁.frame F₄ (VG.Proof.AesCcm.Arm.args_mut Ar) (by rw [he₄.sp, he₁.sp]) (by rw [rd₄', rd₁]) (by rw [wr₄', wr₁])
  -- Counter mode.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.ctr_ok L he₄ hk₄ Ar.rounds h7 h13 c₄ eD en (Ar.data.of_eq rd₄' wr₄')
    (by rw [hnl]; exact Ar.hn) Ar.n32) fun s₅ ⟨he₅, rd₅, wr₅, _, f₅, o₅⟩ => ?_)
  have F₅ : Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem s₅.mem := F₄.trans (f₅.sub VG.Proof.AesCcm.Arm.ctrR_mut)
  -- The tag copied to `T`.
  have hk₅ := hk₁.frame F₅ (VG.Proof.AesCcm.Arm.args_mut Ar) (by rw [he₅.sp, he₁.sp]) (by rw [rd₅, rd₄', rd₁])
    (by rw [wr₅, wr₄', wr₁])
  obtain ⟨i4, v4⟩ := hk₅.at 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨i5, v5⟩ := hk₅.at 5 (by decide) (show 4 * 5 = 20 from rfl)
  rw [eT] at v4
  rw [etl] at v5
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.tagOut_ok L he₅ Ar.t4 Ar.t16 i4 v4 i5 v5 (by rw [wr₅, wr₄']; exact hTw) Tb.wrap Tb.w)
    fun s₆ ⟨he₆, hm₆, rd₆, wr₆⟩ => ?_)
  have hx : (bytesAt s₅.mem (State.addr w) tl).length = tl := length_bytesAt _ _ _
  have f₆ : Frame [⟨State.addr T, tl⟩] s₅.mem s₆.mem := by rw [hm₆]; exact writeBytes_frame' _ hx
  -- `restore`.
  refine WP.mono (restore_ok he₆.r11 L.ww (covers_left he₆.perm.w)
    ((sv₁.frame F₅ (VG.Proof.AesCcm.Arm.saved_mut Ar)).frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Tb.w.sub_right (Lay.wSub (by decide))).symm) he₆.sp)
    fun s' ⟨ab, hm, _, _, _⟩ => ⟨ab, ?_⟩
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (State.addr k) R) := fun _ x =>
    Proof.Cmac.aesWith_length _ _ x
  have cK : ∀ {m : Mem}, Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem m →
      Spec.Ccm.ctxCiph m (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R := fun hf => by
    rw [ctxCiph_frame hf (VG.Proof.AesCcm.Arm.k_mut Ar) hRb, hK₁]
  have a₂ : bytesAt s₂.mem (State.addr A) al = bytesAt s₀.mem (State.addr A) al := by
    rw [VG.Proof.AesCcm.Arm.buf_wR Ar.aad f₂', hent Ar.aad]
  have d₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [VG.Proof.AesCcm.Arm.buf_wR Ar.data.buf f₂', hent Ar.data.buf]
  have d₄ : bytesAt s₄.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [VG.Proof.AesCcm.Arm.buf_wR Ar.data.buf G₄, hent Ar.data.buf]
  have w₅ : bytesAt s₅.mem (State.addr w) 16 = bytesAt s₄.mem (State.addr w) 16 :=
    bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 64) (m := 32) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 384) (m := 2176) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
  have mo := M.out
  rw [BitVec.add_zero] at o₄ mo
  have hY := congrArg List.length o₄
  rw [length_bytesAt, length_xorFrom] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  have d₆ : bytesAt s₆.mem (State.addr D) n = bytesAt s₅.mem (State.addr D) n :=
    bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Tb.d.symm) (by have := Ar.n32; omega)
  have t₆ : bytesAt s₆.mem (State.addr T) tl = bytesAt s₅.mem (State.addr w) tl := by
    rw [hm₆, bytesAt_writeBytes_prefix _ _ _ (by rw [hx]) (by have := Ar.t16; omega), hx, Nat.sub_self]
    simp [Spec.Aes.bytesAt]
  refine ⟨?_, ?_⟩
  · rw [hm, d₆, o₅, cK F₄, d₄, crypt_eq (hBC _)]
  · rw [hm, t₆, bytesAt_prefix s₅.mem (State.addr w) Ar.t16, w₅, o₄, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16,
      mo, cK (f₂'.sub VG.Proof.AesCcm.Arm.wR_mut), cK ((f₂'.sub VG.Proof.AesCcm.Arm.wR_mut).trans (M.frame.sub (VG.Proof.AesCcm.Arm.macR_mut (.inl rfl)))), a₂, d₂,
      ← mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega)]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp {s : State} (h : sealArm.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' :=
  have A := VG.Proof.AesCcm.Arm.args_of_seal h
  VG.Proof.AesCcm.Arm.seal_wp' A.1.1 A.1.2 A.2.1 rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl
    (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Mask`. -/
section

/-!
# AES-CCM on ARMv7: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of
the data with `0 − ok`, for `ok ∈ {0, 1}` in `r7`: the data is kept if
`ok = 1` and zeroed if `ok = 0` (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (Keeps z_subFlags gpr_subFlags z_cmp eval_eq' eval_ne' addr_i dec32 z_dec in_of_covers
  bytesAt_succ mem_store gpr_store add32_ofNat_assoc in_left add_ofNat_zero mem_subFlags)

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1, .subs .r5 .r5 (imm 1)]

theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {c : Bool} (h4 : s.gpr .r4 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if c then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa VG.Proof.AesCcm.Arm.maskBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if c then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [h4, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      VG.Proof.AesCcm.Arm.mask_byte]
  · simp [gpr_setReg, h4, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, Proof.AesCcm.length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {k w sp : BitVec 32} {R q1 : Nat} {s₀ s : State} (he : VG.Proof.AesCcm.Arm.Env k w sp R q1 s) (hk : VG.Proof.AesCcm.Arm.Stk w s₀ s)
    {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (hD : VG.Proof.AesCcm.Arm.Dat k w sp s D n) (hn32 : n < 2 ^ 32) {c : Bool} (h7 : s.gpr .r7 = if c then 1 else 0) :
    WP isa mask s fun s' => VG.Proof.AesCcm.Arm.Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (if c then bytesAt s.mem (State.addr D) n else zeros n) := by
  have hn := hD.buf.fit
  obtain ⟨i2, v2⟩ := hk.at 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₁, run₁, h4₁, h5₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r1 (imm 0),
      .dp .sub .r1 .r1 (.reg .r7), .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r4 = D ∧ s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₁.gpr .r1 = 0 - (if c then 1 else 0) ∧
      s₁.z = decide (n = 0) ∧ (∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [i2, v2, i3, v3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v2, eD]
    · simp [gpr_setReg, v3, en]
    · simp [gpr_setReg, h7, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v3, en, imm]
      rw [z_cmp hn32 (by decide)]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := by simpa using hb
    subst hn0
    refine ⟨he₁, k₁.rd, k₁.wr, fun r hr a b _ => g₁ r ?_ a b, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, VG.WriteBytes.writeBytes_nil]
  have hn0 : 0 < n := by have : n ≠ 0 := by simpa using hb
                         omega
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r4 = D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - j) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (if c then bytesAt s.mem (State.addr D) j else zeros j) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (n - 0) _
    ⟨0, rfl, hn0, by rw [h4₁, add_ofNat_zero], by rw [h5₁]; rfl,
      by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, VG.WriteBytes.writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr, k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r4, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r4', r5', z', g', rd', wr', sp'⟩ := VG.Proof.AesCcm.Arm.maskStep_ok t (c := c) r4 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers hD.buf.rd hj (by omega))
    (by rw [wr, aD]; exact in_of_covers hD.wr hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr D, j⟩] s.mem t.mem := by
    rw [mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.Arm.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr D + BitVec.ofNat 64 j) = s.mem (State.addr D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D)
      (if c then bytesAt s.mem (State.addr D) (j + 1) else zeros (j + 1)) := by
    rw [mem', aD, hq, mem, VG.Proof.AesCcm.Arm.mask_succ, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesCcm.Arm.length_mask]; omega), VG.Proof.AesCcm.Arm.length_mask]
  have hz : t'.z = decide (j + 1 = n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = n) := eval_ne' hz
  by_cases hjn : j + 1 = n
  · left
    refine ⟨by rw [ev]; simp [hjn], he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], fun r hr a b _ => ?_, by rw [hmem, hjn]⟩
    have hr12 : r ≠ .r12 ∧ r ≠ .r1 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gg r a b hr12.1, g₁ r hr12.2 a b]
  · right
    refine ⟨by rw [ev]; simp [hjn], n - (j + 1), by omega, j + 1, rfl, by omega, r4',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Open`. -/
section

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is the entry, `Ctr₀`,
counter mode over the data (which decrypts it), the encrypted MAC of the
plaintext at `W + 112`, then the comparison of its first `t` bytes with the
received tag at `tag` (`recv`, `cmp`), the mask of the data and `restore`
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.Arm (imm recv cmp uO restore)
open VG.Proof.AesGcm.Arm (savedR SavedAt restore_ok covers_left bytesAt_frame Keeps)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom length_xorFrom crypt_eq take_xorFrom_zero mac_eq
  BlockCipher bytesAt_prefix bytesAt_writeBytes_base cryptTag_eq_iff)

/-- Whether the received tag `tag` is that of the decrypted `ct`. -/
abbrev tagOk (ciph : Spec.Ccm.Cipher) (tl : Nat) (nonce ct aad tag : List Byte) : Bool :=
  decide (Spec.Ccm.cryptTag ciph tl nonce tag = Spec.Ccm.mac ciph tl nonce aad (Spec.Ccm.crypt ciph nonce ct))

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' {s₀ : State} {k w N A D T : BitVec 32} {R nl al n tl : Nat} (Ar : VG.Proof.AesCcm.Arm.Args s₀ k w N A D R nl al n tl)
    (Tb : VG.Proof.AesCcm.Arm.TagB w s₀.sp D n T tl) (hTr : Covers [⟨State.addr T, tl⟩] (s₀.rd ++ s₀.wr)) (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (h2 : s₀.gpr .r2 = N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 nl) (eA : stackArg s₀ 0 = A) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) (eT : stackArg s₀ 4 = T)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eW : stackArg s₀ 6 = w) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      s'.gpr .r0 = (if VG.Proof.AesCcm.Arm.tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl)
        then 1 else 0) ∧
      bytesAt s'.mem (State.addr D) n =
        (if VG.Proof.AesCcm.Arm.tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
          (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl)
          then Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) (bytesAt s₀.mem (State.addr N) nl)
            (bytesAt s₀.mem (State.addr D) n)
          else zeros n) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have hsavedK : (⟨State.addr k, 240⟩ : Region).Disjoint (savedR w) := L.k_w' (by decide)
  have t16 := Ar.t16
  have t4 := Ar.t4
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.entry_wp Ar h0 h1 eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, sv₁, f₁⟩ => ?_)
  have hent : ∀ {P : BitVec 32} {len : Nat}, VG.Proof.AesCcm.Arm.Buf w s₀.sp s₀ P len →
      bytesAt s₁.mem (State.addr P) len = bytesAt s₀.mem (State.addr P) len := fun hP =>
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.Ccm.ctxCiph s₁.mem (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R :=
    ctxCiph_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsavedK) hRb
  have hk₁ : VG.Proof.AesCcm.Arm.Stk w s₀ s₁ := Ar.stk.frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Ar.stk.aw.sub_right (Lay.wSub (by decide)))
    he₁.sp rd₁ wr₁
  -- `Ctr₀`.
  have hN₁ := Ar.nonce.of_eq rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.ctrs_ok L he₁ hN₁ (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]) Ar.h7 Ar.h13)
    fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have he₂ : VG.Proof.AesCcm.Arm.Env k w s₀.sp R (14 - nl) s₂ :=
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r11],
      by rw [sp₂, he₁.sp], he₁.perm.of_eq rd₂ wr₂⟩
  have f₂' : Frame (VG.Proof.AesCcm.Arm.wR w s₀.sp) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.Arm.w_wR (.inl (by decide))
  have F₂ : Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem s₂.mem := f₂'.sub VG.Proof.AesCcm.Arm.wR_mut
  have hk₂ := hk₁.frame F₂ (VG.Proof.AesCcm.Arm.args_mut Ar) sp₂ rd₂ wr₂
  have rd₁₂ : s₂.rd = s₀.rd := rd₂.trans rd₁
  have wr₁₂ : s₂.wr = s₀.wr := wr₂.trans wr₁
  have hnl := length_bytesAt s₀.mem (State.addr N) nl
  have h7 : 7 ≤ (bytesAt s₀.mem (State.addr N) nl).length := by rw [hnl]; exact Ar.h7
  have h13 : (bytesAt s₀.mem (State.addr N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  -- Counter mode: the plaintext.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.ctr_ok L he₂ hk₂ Ar.rounds h7 h13 c₂ eD en (Ar.data.of_eq rd₁₂ wr₁₂)
    (by rw [hnl]; exact Ar.hn) Ar.n32) fun s₃ ⟨he₃, rd₃, wr₃, _, f₃, o₃⟩ => ?_)
  have F₃ : Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem s₃.mem := F₂.trans (f₃.sub VG.Proof.AesCcm.Arm.ctrR_mut)
  have rd₁₃ : s₃.rd = s₀.rd := rd₃.trans rd₁₂
  have wr₁₃ : s₃.wr = s₀.wr := wr₃.trans wr₁₂
  have hk₃ := hk₁.frame F₃ (VG.Proof.AesCcm.Arm.args_mut Ar) (by rw [he₃.sp, he₁.sp]) (by rw [rd₁₃, rd₁]) (by rw [wr₁₃, wr₁])
  have c₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm
      · exact (Ar.data.buf.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c₂]
  have a₃ : bytesAt s₃.mem (State.addr A) al = bytesAt s₀.mem (State.addr A) al := by
    rw [bytesAt_frame F₃ (VG.Proof.AesCcm.Arm.aad_mut Ar) (by have := Ar.aad.lt; omega), hent Ar.aad]
  -- The MAC of the plaintext, encrypted, at `W + 112`.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.mac_ok L he₃ hk₃ rfl Ar.rounds eA eal eD en etl hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.al32 Ar.n32 Ar.hn c₃ (y := uO) (.inr rfl) (Ar.aad.of_eq rd₁₃ wr₁₃) (Ar.data.buf.of_eq rd₁₃ wr₁₃))
    fun s₄ M => ?_)
  have c₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₃]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.tag_ok L M.env Ar.rounds h7 h13 c₄ (y := uO) (.inr rfl))
    fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ => ?_)
  have f₅' : Frame (VG.Proof.AesCcm.Arm.wR w s₀.sp) s₄.mem s₅.mem := f₅.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.AesCcm.Arm.w_wR (.inl (by decide))
    · exact VG.Proof.AesCcm.Arm.w_wR (.inl (by decide))
    · exact VG.Proof.AesCcm.Arm.w_wR (.inr ⟨by decide, by decide⟩)
    · exact ⟨_, by simp, fun _ h => h⟩
  have G₅ : Frame (VG.Proof.AesCcm.Arm.wR w s₀.sp) s₃.mem s₅.mem := (M.frame.sub (VG.Proof.AesCcm.Arm.macR_wR (.inr rfl))).trans f₅'
  have F₅ : Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem s₅.mem := F₃.trans (G₅.sub VG.Proof.AesCcm.Arm.wR_mut)
  have rd₁₅ : s₅.rd = s₀.rd := by rw [rd₅, M.rd, rd₁₃]
  have wr₁₅ : s₅.wr = s₀.wr := by rw [wr₅, M.wr, wr₁₃]
  have hk₅ := hk₁.frame F₅ (VG.Proof.AesCcm.Arm.args_mut Ar) (by rw [he₅.sp, he₁.sp]) (by rw [rd₁₅, rd₁]) (by rw [wr₁₅, wr₁])
  have hT₅ : bytesAt s₅.mem (State.addr T) tl = bytesAt s₀.mem (State.addr T) tl := by
    rw [bytesAt_frame F₅ (VG.Proof.AesCcm.Arm.tag_mut Tb) (by omega), bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Tb.w.sub_right (Lay.wSub (by decide))) (by omega)]
  -- `t`, and the received tag padded at `W + 256`.
  obtain ⟨i5, v5⟩ := hk₅.at 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₆, run₆, h6₆, g₆, k₆⟩ : ∃ s₆, runBlock isa [.ldrSp .r6 20] s₅ = some s₆ ∧
      s₆.gpr .r6 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r) ∧ Keeps s₅ s₆ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5, etl]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) k₆.sp k₆.rd k₆.wr
  obtain ⟨i4, v4⟩ := (hk₅.of_eq k₆.mem k₆.sp k₆.rd k₆.wr).at 4 (by decide) (show 4 * 4 = 16 from rfl)
  rw [eT] at v4
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.recv_ok L he₆ i4 v4
      (by rw [k₆.rd, k₆.wr, rd₁₅, wr₁₅]; exact hTr) Tb.wrap (Tb.w.sub_right (Lay.wSub (by decide))) h6₆
      (by omega) t16) fun s₇ ⟨hR₇, fr₇, g₇, rd₇, wr₇, sp₇⟩ => ?_)
  have he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    sp₇ rd₇ wr₇
  have h6₇ : s₇.gpr .r6 = BitVec.ofNat 32 tl := by
    rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₆]
  -- The comparison.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.cmp_ok L he₇ (o := uO) (.inr rfl) h6₇ (by omega) t16)
    fun s₈ ⟨h0₈, fr₈, g₈, rd₈, wr₈, sp₈⟩ => ?_)
  obtain ⟨s₉, run₉, h7₉, g₉, k₉⟩ : ∃ s₉, runBlock isa [.mov .r7 (.reg .r0)] s₈ = some s₉ ∧
      s₉.gpr .r7 = s₈.gpr .r0 ∧ (∀ r, r ≠ .r7 → s₉.gpr r = s₈.gpr r) ∧ Keeps s₈ s₉ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have he₉ := he₇.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₉ _ (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)])
    (k₉.sp.trans sp₈) (k₉.rd.trans rd₈) (k₉.wr.trans wr₈)
  have f₅₉ : Frame (VG.Proof.AesCcm.Arm.wR w s₀.sp) s₅.mem s₉.mem := by
    rw [k₉.mem, ← k₆.mem] at *
    refine (fr₇.sub fun r hr => ?_).trans (fr₈.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.Arm.w_wR (.inr ⟨by decide, by decide⟩)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.Arm.w_wR (.inr ⟨by decide, by decide⟩)
  have F₉ : Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem s₉.mem := F₅.trans (f₅₉.sub VG.Proof.AesCcm.Arm.wR_mut)
  have rd₁₉ : s₉.rd = s₀.rd := by rw [k₉.rd, rd₈, rd₇, k₆.rd, rd₁₅]
  have wr₁₉ : s₉.wr = s₀.wr := by rw [k₉.wr, wr₈, wr₇, k₆.wr, wr₁₅]
  have hk₉ := hk₁.frame F₉ (VG.Proof.AesCcm.Arm.args_mut Ar) (by rw [he₉.sp, he₁.sp]) (by rw [rd₁₉, rd₁]) (by rw [wr₁₉, wr₁])
  -- What the comparison compares.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (State.addr k) R) := fun _ x =>
    Proof.Cmac.aesWith_length _ _ x
  have cK : ∀ {m : Mem}, Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem m →
      Spec.Ccm.ctxCiph m (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R := fun hf => by
    rw [ctxCiph_frame hf (VG.Proof.AesCcm.Arm.k_mut Ar) hRb, hK₁]
  have d₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [VG.Proof.AesCcm.Arm.buf_wR Ar.data.buf f₂', hent Ar.data.buf]
  have p₃ : bytesAt s₃.mem (State.addr D) n = Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
      (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n) := by
    rw [o₃, cK F₂, d₂, crypt_eq (hBC _)]
  have p₉ : bytesAt s₉.mem (State.addr D) n = bytesAt s₃.mem (State.addr D) n := by
    rw [VG.Proof.AesCcm.Arm.buf_wR Ar.data.buf f₅₉, VG.Proof.AesCcm.Arm.buf_wR Ar.data.buf G₅]
  have hl : (bytesAt s₀.mem (State.addr N) nl).length ≤ 15 := by rw [hnl]; have := Ar.h13; omega
  have mo := M.out
  rw [cK F₃, a₃, p₃] at mo
  rw [cK (F₃.trans (M.frame.sub (VG.Proof.AesCcm.Arm.macR_mut (.inr rfl)))), mo] at o₅
  have hY := congrArg List.length o₅
  rw [length_bytesAt, length_xorFrom] at hY
  have hV : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
          (bytesAt s₀.mem (State.addr A) al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
            (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n))) := by
    rw [bytesAt_prefix _ _ t16, bytesAt_frame fr₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), k₆.mem, o₅, take_xorFrom_zero (hBC _) _ hY.symm t16, ← mac_eq _ _ hl]
  have hRv : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16 =
      bytesAt s₀.mem (State.addr T) tl ++ Spec.Gcm.zeros (16 - tl) := by
    rw [hR₇, k₆.mem, hT₅]
  have hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
      (bytesAt s₀.mem (State.addr A) al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R)
        (bytesAt s₀.mem (State.addr N) nl) (bytesAt s₀.mem (State.addr D) n))).length = tl := by
    rw [mac_eq _ _ hl, List.length_take, ← mo, length_bytesAt]; omega
  have key : decide (bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl ++ Spec.Gcm.zeros (16 - tl) =
      bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16) =
      VG.Proof.AesCcm.Arm.tagOk (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) (bytesAt s₀.mem (State.addr T) tl) := by
    rw [hV, hRv, VG.Proof.AesCcm.Arm.tagOk, decide_eq_decide, List.append_left_inj,
      cryptTag_eq_iff (hBC _) t16 _ (length_bytesAt _ _ _) hML, eq_comm]
  have h7' : s₉.gpr .r7 = if decide (bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 uO) tl ++
      Spec.Gcm.zeros (16 - tl) = bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 256) 16) then 1 else 0 := by
    rw [h7₉, h0₈]; simp only [decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.Arm.mask_ok he₉ hk₉ eD en (Ar.data.of_eq rd₁₉ wr₁₉) Ar.n32 h7')
    fun s₁₀ ⟨he₁₀, rd₁₀, wr₁₀, g₁₀, m₁₀⟩ => ?_)
  rw [key] at m₁₀
  have F₁₀ : Frame (VG.Proof.AesCcm.Arm.mutR w s₀.sp D n) s₁.mem s₁₀.mem := F₉.trans (by
    rw [m₁₀]
    exact (VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.Arm.length_mask]; exact Region.contains_self _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- `ok` in `r0`, and `restore`.
  show WP isa (.block ([.mov .r0 (.reg .r7)] ++ restore)) s₁₀ _
  refine WP.block_append (WP.of_runBlock ⟨s₁₀.setReg .r0 (s₁₀.gpr .r7), by arun [], ?_⟩)
  refine WP.mono (restore_ok (by simp [gpr_setReg, he₁₀.r11]) L.ww
    (by simp only [rd_setReg, wr_setReg]; exact covers_left he₁₀.perm.w)
    (by simp only [mem_setReg]; exact sv₁.frame F₁₀ (VG.Proof.AesCcm.Arm.saved_mut Ar)) (by simp only [sp_setReg]; exact he₁₀.sp))
    fun s' ⟨ab, hm, h0', _, _⟩ => ⟨ab, ?_, ?_⟩
  · rw [h0', gpr_setReg_self, g₁₀ _ (by decide) (by decide) (by decide) (by decide), h7']
    rw [key]
  · rw [hm, mem_setReg, m₁₀, bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesCcm.Arm.length_mask]) (by have := Ar.data.buf.lt; omega),
      VG.Proof.AesCcm.Arm.length_mask, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil, p₉, p₃]

theorem openPost {s s' : State} {c : Prop} [Decidable c] {pt : List Byte}
    (hres : VG.Proof.AesCcm.Arm.openRes s = if c then some pt else none) (h0 : s'.gpr .r0 = if decide c then 1 else 0)
    (hd : bytesAt s'.mem (State.addr (VG.Proof.AesCcm.Arm.arg s 2)) (VG.Proof.AesCcm.Arm.arg s 3).toNat =
      if decide c then pt else zeros (VG.Proof.AesCcm.Arm.arg s 3).toNat) : openArm.post s s' := by
  by_cases hc : c
  · simp only [hc, decide_true, ite_true] at hres h0 hd
    simp only [VG.Proof.AesCcm.Arm.openArm, hres]; exact ⟨h0, hd⟩
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at hres h0 hd
    simp only [VG.Proof.AesCcm.Arm.openArm, hres]; exact ⟨h0, hd⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp {s : State} (h : openArm.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' :=
  have A := VG.Proof.AesCcm.Arm.args_of_open h
  WP.mono (VG.Proof.AesCcm.Arm.open_wp' A.1.1 A.1.2 A.2 rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl
    (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm rfl)
    fun _ ⟨ab, h0, hd⟩ => ⟨ab, VG.Proof.AesCcm.Arm.openPost rfl h0 hd⟩

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.CTBase`. -/
section

/-!
# AES-CCM on ARMv7: constant time, the invariants

Untrusted: everything here is checked by Lean. Two runs of `seal` or `open`
with the same public arguments (`onePub`) are related piece by piece by
invariants `CT I` (`Proof.AesGcm.Arm.CT`), whose parameters are the public
values: the pointers, the lengths, the rounds and `W` (`One`, the
arguments, as `Args`, with their values on the stack; `PubArgs`, which the
taint analysis of blocks reading them needs, `CT.args`). Each piece's
correctness lemma, in each run, gives the invariant of the next
(`One.next`).
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CT ArgsKeep arg_frame)

/-- The stack arguments `a`, which the code may not write, as public. -/
structure PubArgs (sp : BitVec 32) (a : Nat → BitVec 32) (s : State) : Prop where
  hsp : s.sp = sp
  fit : sp.toNat + 4 * 7 ≤ 2 ^ 32
  wr : ∀ r ∈ s.wr, (VG.Proof.AesCcm.Arm.args s 7).Disjoint r
  arg : ∀ i < 7, stackArg s i = a i

/-- A block the taint analysis checks from the registers `rs` and the stack
arguments, the same in both runs. -/
theorem CT.args {I : State → Prop} {c : Prog isa} {sp : BitVec 32} {a : Nat → BitVec 32} (rs : List Reg)
    (hI : ∀ s, I s → VG.Proof.AesCcm.Arm.PubArgs sp a s) (hp : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint rs (4 * 7)) c h).isSome = true) : CT I c := by
  obtain ⟨_, hc⟩ := hc
  refine Proof.AesGcm.Arm.CT.argTaint rs (4 * 7) hp (fun s₁ s₂ h₁ h₂ => (hI _ h₁).hsp.trans (hI _ h₂).hsp.symm)
    (fun s h => ⟨by rw [(hI s h).hsp]; exact (hI s h).fit, fun r hr => ?_⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of ((hI _ h₁).hsp.trans (hI _ h₂).hsp.symm) (by rw [(hI _ h₁).hsp]; exact (hI _ h₁).fit)
      fun i hi => by rw [(hI _ h₁).arg i hi, (hI _ h₂).arg i hi]) hc
  have := (hI s h).wr r hr
  rwa [show Proof.AesCcm.Arm.args s 7 = ⟨State.addr s.sp, 4 * 7⟩ by
    simp only [Proof.AesCcm.Arm.args, Proof.AesGcm.Arm.argAddr_zero]] at this

/-- `a; (b; c)`, from `(a; b); c`. -/
theorem CT.assoc {I : State → Prop} {a b c : Prog isa} (h : CT I (.seq (.seq a b) c)) : CT I (.seq a (.seq b c)) :=
  RelCT.assoc h

/-- `a; (b; (c; (d; e)))`, from `(a; (b; (c; d))); e`. -/
theorem CT.assoc4 {I : State → Prop} {a b c d e : Prog isa} (h : CT I (.seq (.seq a (.seq b (.seq c d))) e)) :
    CT I (.seq a (.seq b (.seq c (.seq d e)))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- The values of the stack arguments. -/
abbrev argVals (A D T w : BitVec 32) (al n tl : Nat) (i : Nat) : BitVec 32 :=
  [A, BitVec.ofNat 32 al, D, BitVec.ofNat 32 n, T, BitVec.ofNat 32 tl, w].getD i 0

/-- One run between the pieces, with its public values: the arguments, the
stack pointer and what the code may write. -/
structure One (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop where
  ar : VG.Proof.AesCcm.Arm.Args s k w N A D R nl al n tl
  sp : s.sp = sp
  wr : ∀ r ∈ s.wr, (VG.Proof.AesCcm.Arm.args s 7).Disjoint r
  eA : stackArg s 0 = A
  eal : stackArg s 1 = BitVec.ofNat 32 al
  eD : stackArg s 2 = D
  en : stackArg s 3 = BitVec.ofNat 32 n
  eT : stackArg s 4 = T
  etl : stackArg s 5 = BitVec.ofNat 32 tl
  eW : stackArg s 6 = w

namespace One

variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} {s : State} (h : VG.Proof.AesCcm.Arm.One k w sp N A D T R nl al n tl s)
include h

theorem pubArgs : VG.Proof.AesCcm.Arm.PubArgs sp (VG.Proof.AesCcm.Arm.argVals A D T w al n tl) s where
  hsp := h.sp
  fit := by rw [← h.sp]; exact h.ar.stk.fit
  wr := h.wr
  arg i hi := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.eA
    · exact h.eal
    · exact h.eD
    · exact h.en
    · exact h.eT
    · exact h.etl
    · exact h.eW

/-- After code that writes regions apart from the stack arguments. -/
theorem next' {s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (VG.Proof.AesCcm.Arm.args s 7).Disjoint r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.One k w sp N A D T R nl al n tl s' := by
  have Ar := h.ar
  have hk : VG.Proof.AesCcm.Arm.Stk w s s' := Ar.stk.frame hf hd hsp hrd hwr
  have ea : VG.Proof.AesCcm.Arm.args s' 7 = VG.Proof.AesCcm.Arm.args s 7 := Proof.AesGcm.Arm.args_sp hsp 7
  have ka : ∀ i < 7, stackArg s' i = stackArg s i := hk.keep.arg
  have sb : VG.Proof.AesCcm.Arm.blw s'.sp = VG.Proof.AesCcm.Arm.blw s.sp := by rw [hsp]
  refine ⟨?_, by rw [hsp, h.sp], by rw [hwr, ea]; exact h.wr, by rw [ka 0 (by decide), h.eA],
    by rw [ka 1 (by decide), h.eal], by rw [ka 2 (by decide), h.eD], by rw [ka 3 (by decide), h.en],
    by rw [ka 4 (by decide), h.eT], by rw [ka 5 (by decide), h.etl], by rw [ka 6 (by decide), h.eW]⟩
  have L := Ar.lay
  exact {
    lay := ⟨L.kw, L.ww, by rw [hsp]; exact L.sp16, L.k_w, by rw [sb]; exact L.stk_k, by rw [sb]; exact L.stk_w⟩
    perm := Ar.perm.of_eq hrd hwr
    stk := ⟨ArgsKeep.refl 7 s', by rw [hsp]; exact Ar.stk.fit, by rw [ea, hrd]; exact Ar.stk.rd,
      by rw [ea]; exact Ar.stk.aw⟩
    rounds := Ar.rounds
    nonce := { Ar.nonce.of_eq hrd hwr with stk := by rw [sb]; exact Ar.nonce.stk }
    aad := { Ar.aad.of_eq hrd hwr with stk := by rw [sb]; exact Ar.aad.stk }
    data := ⟨{ Ar.data.buf.of_eq hrd hwr with stk := by rw [sb]; exact Ar.data.buf.stk }, by rw [hwr]; exact Ar.data.wr,
      Ar.data.k⟩
    nd := Ar.nd
    ad := Ar.ad
    da := by rw [ea]; exact Ar.da
    h7 := Ar.h7
    h13 := Ar.h13
    t4 := Ar.t4
    t16 := Ar.t16
    te := Ar.te
    hn := Ar.hn
    n32 := Ar.n32
    al32 := Ar.al32 }

/-- After code that writes regions within `mutR`. -/
theorem next {s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, Region.Sub r r') (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.One k w sp N A D T R nl al n tl s' := by
  rw [← h.sp] at hsub
  exact h.next' (hf.sub hsub) (VG.Proof.AesCcm.Arm.args_mut h.ar) hsp hrd hwr

end One

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.CTMac`. -/
section

/-!
# AES-CCM on ARMv7: the MAC is constant time

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` get the same arguments in both runs (`updBlock_ct`,
`Proof.AesCcm.Arm.upd_rel`); the branches are on the lengths, public; the
blocks between the calls the taint analysis checks.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop minLen)
open VG.Proof.AesGcm.Arm (CT copyLoop_ok bytesAt_frame)
open VG.Proof.AesCcm (headLen)

/-- Before a piece chaining the `len` bytes at `P`. -/
def AbsI (k w sp : BitVec 32) (R q1 : Nat) (P : BitVec 32) (len : Nat) (s : State) : Prop :=
  VG.Proof.AesCcm.Arm.Env k w sp R q1 s ∧ (len ≠ 0 → VG.Proof.AesCcm.Arm.Buf w sp s P len) ∧ s.gpr .r4 = P ∧ s.gpr .r5 = BitVec.ofNat 32 len

theorem env_eq {k w sp : BitVec 32} {R q1 : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.AesCcm.Arm.Env k w sp R q1 s₁) (h₂ : VG.Proof.AesCcm.Arm.Env k w sp R q1 s₂)
    {r : Reg} (hr : r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- `updBlock y`. -/
theorem updBlock_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (VG.Proof.AesCcm.Arm.Env k w sp R q1) (updBlock y) := by
  refine CT.seq (J := fun s => VG.Proof.AesCcm.Arm.UArgs s k (w + BitVec.ofNat 32 y) (w + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 384)
    R 1 ∧ s.sp = sp) ?_ (fun s he => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
        (.block (updArgs y ++ [addI .r3 .r11 bO, .mov .r12 (imm 1)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => VG.Proof.AesCcm.Arm.env_eq h₁ h₂ (by simpa using hr)) hc
  · obtain ⟨s₁, run₁, U, he₁, -, -⟩ := VG.Proof.AesCcm.Arm.updBlockArgs_ok L he hR hy
    exact WP.of_runBlock ⟨s₁, run₁, U, he₁.sp⟩
  · exact VG.Proof.AesCcm.Arm.upd_rel fun _ _ ⟨⟨U₁, e₁⟩, ⟨U₂, e₂⟩⟩ => ⟨U₁, U₂, e₁, e₂⟩

/-- The whole blocks of a string. -/
theorem absorbWhole_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (VG.Proof.AesCcm.Arm.AbsI k w sp R q1 P len) (absorbWhole y) := by
  refine CT.seq (J := fun s => VG.Proof.AesCcm.Arm.AbsI k w sp R q1 P len s ∧ s.gpr .r12 = BitVec.ofNat 32 (len / 16) ∧
    s.z = decide (len / 16 = 0)) ?_ (fun s ⟨he, hP, h4, h5⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2, h₂.2.2.2]) hc
  · obtain ⟨s₁, run₁, h12, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split16_ok hl h5
    refine WP.of_runBlock ⟨s₁, run₁, ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr,
      fun h => (hP h).of_eq k₁.rd k₁.wr, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5]⟩, h12, hz⟩
  refine CT.ite (decide (len / 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : len / 16 ≠ 0 := by simpa using hb
  refine CT.seq (J := fun s => VG.Proof.AesCcm.Arm.UArgs s k (w + BitVec.ofNat 32 y) P (w + BitVec.ofNat 32 384) R (len / 16) ∧
    s.sp = sp) ?_ (fun s ⟨⟨he, hP, h4, _⟩, h12, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r8, .r9, .r10, .r11])
        (.block (updArgs y ++ [.mov .r3 (.reg .r4)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · exact VG.Proof.AesCcm.Arm.env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₂, run₂, U, he₂, -, -⟩ := VG.Proof.AesCcm.Arm.absArgs_ok L he hR hy ((hP (by omega)).take (Nat.mul_div_le len 16))
      (by omega) h4 h12
    exact WP.of_runBlock ⟨s₂, run₂, U, he₂.sp⟩
  · exact VG.Proof.AesCcm.Arm.upd_rel fun _ _ ⟨⟨U₁, e₁⟩, ⟨U₂, e₂⟩⟩ => ⟨U₁, U₂, e₁, e₂⟩

/-- The last bytes of a string. -/
theorem absorbTail_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (VG.Proof.AesCcm.Arm.AbsI k w sp R q1 P len) (absorbTail y) := by
  refine CT.seq (J := fun s => VG.Proof.AesCcm.Arm.AbsI k w sp R q1 P len s ∧ s.gpr .r6 = BitVec.ofNat 32 (len % 16) ∧
    s.z = decide (len % 16 = 0)) ?_ (fun s ⟨he, hP, h4, h5⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2, h₂.2.2.2]) hc
  · obtain ⟨s₁, run₁, h6, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split15_ok hl h5
    refine WP.of_runBlock ⟨s₁, run₁, ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr,
      fun h => (hP h).of_eq k₁.rd k₁.wr, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5]⟩, h6, hz⟩
  refine CT.ite (decide (len % 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : len % 16 ≠ 0 := by simpa using hb
  refine CT.assoc (CT.seq (J := VG.Proof.AesCcm.Arm.Env k w sp R q1) ?_ (fun _ ⟨⟨he, hP, h4, h5⟩, h6, _⟩ => ?_) (VG.Proof.AesCcm.Arm.updBlock_ct L hR hy))
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r8, .r9, .r10, .r11])
        (.seq (.block (zero16 bO ++ [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4), addI .r2 .r11 bO,
          .mov .r3 (.reg .r6)])) copyLoop) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · rw [h₁.1.2.2.2, h₂.1.2.2.2]
    · rw [h₁.2.1, h₂.2.1]
    · exact VG.Proof.AesCcm.Arm.env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₃, run₃, -, lp, he₃, -, -, -, -⟩ := VG.Proof.AesCcm.Arm.tailPre_ok L he hP hl h0 h4 h5 h6
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    exact WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨_, lo⟩ => he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr

/-- A string padded. -/
theorem absorbPad_ct {y : Nat} (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hl : len < 2 ^ 32) :
    CT (VG.Proof.AesCcm.Arm.AbsI k w sp R q1 P len) (absorbPad y) :=
  CT.seq (VG.Proof.AesCcm.Arm.absorbWhole_ct L hR hy hl) (fun _ ⟨he, hP, h4, h5⟩ =>
    WP.mono (VG.Proof.AesCcm.Arm.absorbWhole_ok L he hR hy hP hl h4 h5) fun _ A => ⟨A.env, fun h => (hP h).of_eq A.rd A.wr, A.r4, A.r5⟩)
    (VG.Proof.AesCcm.Arm.absorbTail_ct L hR hy hl)

/-- The first block of the associated data. -/
theorem aadHead_ct {y : Nat} (hy : y = 0 ∨ y = 112) {A : BitVec 32} {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32) :
    CT (fun s => VG.Proof.AesCcm.Arm.Env k w sp R q1 s ∧ VG.Proof.AesCcm.Arm.Buf w sp s A a ∧ s.gpr .r4 = A ∧ s.gpr .r5 = BitVec.ofNat 32 a)
      (aadHead y) := by
  refine CT.assoc4 (CT.seq (J := VG.Proof.AesCcm.Arm.Env k w sp R q1) ?_ (fun s ⟨he, hA, h4, h5⟩ =>
    WP.mono (VG.Proof.AesCcm.Arm.aadHeadPre_ok L he hA ha0 ha h4 h5) fun _ h => h.1) (VG.Proof.AesCcm.Arm.updBlock_ct L hR hy))
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r8, .r9, .r10, .r11])
      (.seq header (.seq minLen (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r11 bO, .dp .add .r2 .r2 (.reg .r6),
        .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]) copyLoop))) h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · exact VG.Proof.AesCcm.Arm.env_eq h₁.1 h₂.1 hr

end

/-- Between the pieces of the MAC: one run, the environment with `q − 1` in
`r10`, and `Ctr₀` at `W + 48`. -/
def MacI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  VG.Proof.AesCcm.Arm.One k w sp N A D T R nl al n tl s ∧ VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s ∧
    ∃ nonce : List Byte, nonce.length = nl ∧
      bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}

theorem c0_macR {y : Nat} (hy : y = 0 ∨ y = 112) (L : VG.Proof.AesCcm.Arm.Lay k w sp) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.Arm.macR w sp y) m m') :
    bytesAt m' (State.addr w + BitVec.ofNat 64 48) 16 = bytesAt m (State.addr w + BitVec.ofNat 64 48) 16 :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide)

/-- After a piece of the MAC. -/
theorem MacI.next {y : Nat} (hy : y = 0 ∨ y = 112) {s s' : State} (h : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s)
    {Y : List Byte} (M : VG.Proof.AesCcm.Arm.MacStep k w sp R (14 - nl) s y Y s') : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s' := by
  obtain ⟨o, he, nonce, hl, hc⟩ := h
  have L : VG.Proof.AesCcm.Arm.Lay k w sp := by have := o.ar.lay; rwa [o.sp] at this
  exact ⟨o.next M.frame (VG.Proof.AesCcm.Arm.macR_mut hy) (by rw [M.env.sp, he.sp]) M.rd M.wr, M.env, nonce, hl,
    by rw [VG.Proof.AesCcm.Arm.c0_macR hy L M.frame, hc]⟩

theorem MacI.lay {s : State} (h : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s) : VG.Proof.AesCcm.Arm.Lay k w sp := by
  have := h.1.ar.lay; rwa [h.1.sp] at this

variable (L : VG.Proof.AesCcm.Arm.Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hal : al < 2 ^ 32)
include L hR hal

/-- The associated data. -/
theorem aad_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) (aad y) := by
  refine CT.seq (J := fun s => VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s ∧ s.gpr .r4 = A ∧
    s.gpr .r5 = BitVec.ofNat 32 al ∧ s.z = decide (al = 0)) ?_ (fun s h => ?_) ?_
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.aadLd_ok h.1.ar.stk h.1.eA h.1.eal hal
    have he₁ := h.2.1.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
    refine WP.of_runBlock ⟨s₁, run₁, ⟨h.1.next (rs := []) (by rw [k₁.mem]; exact Frame.refl _ _)
      (fun _ h => by simp at h) k₁.sp k₁.rd k₁.wr, he₁, ?_⟩, h4, h5, hz⟩
    obtain ⟨nonce, hl, hc⟩ := h.2.2
    exact ⟨nonce, hl, by rw [k₁.mem]; exact hc⟩
  refine CT.ite (decide (al = 0)) (fun s h => h.2.2.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : al ≠ 0 := by simpa using hb
  have hn1 : headLen al ≤ al := by unfold headLen; omega
  have bufA : ∀ {s : State}, VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s → VG.Proof.AesCcm.Arm.Buf w sp s A al := fun h => by
    have := h.1.ar.aad; rwa [h.1.sp] at this
  refine CT.seq (J := VG.Proof.AesCcm.Arm.AbsI k w sp R (14 - nl) (A + BitVec.ofNat 32 (headLen al)) (al - headLen al))
    ((VG.Proof.AesCcm.Arm.aadHead_ct L hR hy (by omega) hal).mono fun s ⟨h, h4, h5, _⟩ => ⟨h.2.1, bufA h, h4, h5⟩)
    (fun s ⟨h, h4, h5, _⟩ => WP.mono (VG.Proof.AesCcm.Arm.aadHead_ok L h.2.1 hR hy (bufA h) (by omega) hal h4 h5) fun _ A₂ =>
      ⟨A₂.env, fun e => ((bufA h).sub (j := headLen al) (k := al - headLen al) (by omega) (by omega)).of_eq
        A₂.rd A₂.wr, A₂.r4, A₂.r5⟩) (VG.Proof.AesCcm.Arm.absorbPad_ct L hR hy (by omega))

/-- `B₀`. -/
theorem b0_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) (b0 y) := by
  refine CT.assoc (CT.seq (J := VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl)) ?_ (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) (VG.Proof.AesCcm.Arm.updBlock_ct L hR hy))
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint [.r8, .r9, .r10, .r11] (4 * 7))
        (.seq flagsCode (.block (b0Block y))) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.args _ (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => VG.Proof.AesCcm.Arm.env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) ⟨_, hc⟩
  · have Ar := o.ar
    exact WP.mono (VG.Proof.AesCcm.Arm.b0Pre_ok L he Ar.stk o.etl o.eal o.en hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te hal Ar.n32 Ar.hn hc hy)
      fun _ h => h.1

/-- The MAC. -/
theorem mac_ct {y : Nat} (hy : y = 0 ∨ y = 112) (hn : n < 2 ^ 32) : CT (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) (VG.Impl.AesCcm.Arm.mac y) := by
  refine CT.seq (J := VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) (VG.Proof.AesCcm.Arm.b0_ct L hR hal hy) (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) ?_
  · have Ar := o.ar
    exact WP.mono (VG.Proof.AesCcm.Arm.b0_ok L he Ar.stk hR o.etl o.eal o.en hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te hal Ar.n32 Ar.hn hc hy)
      fun _ M => MacI.next hy ⟨o, he, nonce, hl, hc⟩ M
  refine CT.seq (J := VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) (VG.Proof.AesCcm.Arm.aad_ct L hR hal hy) (fun s h => ?_) ?_
  · obtain ⟨o, he, _⟩ := id h
    have bufA : VG.Proof.AesCcm.Arm.Buf w sp s A al := by have := o.ar.aad; rwa [o.sp] at this
    exact WP.mono (VG.Proof.AesCcm.Arm.aad_ok L he hR hy o.ar.stk o.eA o.eal hal bufA) fun _ M => MacI.next hy h M
  refine CT.seq (J := VG.Proof.AesCcm.Arm.AbsI k w sp R (14 - nl) D n) ?_ (fun s ⟨o, he, _⟩ => ?_) (VG.Proof.AesCcm.Arm.absorbPad_ct L hR hy hn)
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.dataLd_ok o.ar.stk o.eD o.en
    have bufD : VG.Proof.AesCcm.Arm.Buf w sp s D n := by have := o.ar.data.buf; rwa [o.sp] at this
    exact WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr,
      fun _ => bufD.of_eq k₁.rd k₁.wr, h4, h5⟩

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.CTCrypt`. -/
section

/-!
# AES-CCM on ARMv7: the tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32`
get the same arguments in both runs (`Proof.AesGcm.Arm.CT.ctr`); the
branches are on the length of the data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 xorLoop ctrFrame)
open VG.Proof.AesGcm.Arm (CT bytesAt_frame ctr_call CtrCall)

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}

/-- After code that writes `rs`, within what the pieces write and apart from `Ctr₀`. -/
theorem MacI.of {s s' : State} (h : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s) (he : VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s')
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesCcm.Arm.mutR w sp D n, Region.Sub r r')
    (hd : ∀ r ∈ rs, (⟨State.addr w + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s' := by
  obtain ⟨o, he₀, nonce, hl, hc⟩ := h
  exact ⟨o.next hf hsub (by rw [he.sp, he₀.sp]) hrd hwr, he, nonce, hl, by rw [bytesAt_frame hf hd (by decide), hc]⟩

variable (L : VG.Proof.AesCcm.Arm.Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- `tag y`. -/
theorem tag_ct {y : Nat} (hy : y = 0 ∨ y = 112) : CT (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) (tag y) := by
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 y)
    (w + BitVec.ofNat 32 384) R 1 ∧ s.sp = sp) ?_ (fun s ⟨o, he, nonce, hl, hc⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
        (.block ([.mov .r0 (imm 0)] ++ ctrAt ++ ctrArgs ++ [addI .r3 .r11 y, .mov .r12 (imm 1)])) h).isSome = true := by
      rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => VG.Proof.AesCcm.Arm.env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) hc
  · obtain ⟨s₃, run₃, C, he₃, -⟩ := VG.Proof.AesCcm.Arm.tagArgs_ok L he hR (nonce := nonce) (by rw [hl]; exact o.ar.h7)
      (by rw [hl]; exact o.ar.h13) hc hy
    exact WP.of_runBlock ⟨s₃, run₃, C, he₃.sp⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.trans e₂.symm⟩

/-- Before counter mode. -/
def CrI (k w sp : BitVec 32) (R nl : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop :=
  VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s ∧ (∃ nonce : List Byte, nonce.length = nl ∧
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) ∧
  VG.Proof.AesCcm.Arm.Dat k w sp s D n ∧ s.gpr .r4 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n

omit L hR in
theorem CrI.keep {s s' : State} (h : VG.Proof.AesCcm.Arm.CrI k w sp R nl D n s) (hg : ∀ r, r ≠ .r12 → r ≠ .r6 → s'.gpr r = s.gpr r)
    (hk : Proof.AesGcm.Arm.Keeps s s') : VG.Proof.AesCcm.Arm.CrI k w sp R nl D n s' := by
  obtain ⟨he, ⟨nonce, hl, hc⟩, hD, h4, h5⟩ := h
  exact ⟨he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    ⟨nonce, hl, by rw [hk.mem]; exact hc⟩, hD.of_eq hk.rd hk.wr, by rw [hg _ (by decide) (by decide), h4],
    by rw [hg _ (by decide) (by decide), h5]⟩

/-- The whole blocks of the data. -/
theorem ctrWhole_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn4 : n < 2 ^ 32) : CT (VG.Proof.AesCcm.Arm.CrI k w sp R nl D n) ctrWhole := by
  refine CT.seq (J := fun s => VG.Proof.AesCcm.Arm.CrI k w sp R nl D n s ∧ s.gpr .r12 = BitVec.ofNat 32 (n / 16) ∧
    s.z = decide (n / 16 = 0)) ?_ (fun s h => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]) hc
  · obtain ⟨s₁, run₁, h12, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split16_ok hn4 h.2.2.2.2
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r a _ => g₁ r a) k₁, h12, hz⟩
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) D (w + BitVec.ofNat 32 384) R (n / 16) ∧
    s.sp = sp) ?_ (fun s ⟨⟨he, ⟨nonce, hl, hc⟩, hD, h4, _⟩, h12, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r8, .r9, .r10, .r11])
        (.block ([.mov .r0 (imm 1)] ++ ctrAt ++ ctrArgs ++ [.mov .r3 (.reg .r4)])) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1]
    · exact VG.Proof.AesCcm.Arm.env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₄, run₄, C, he₄, -⟩ := VG.Proof.AesCcm.Arm.ctrWholeArgs_ok L he hR (nonce := nonce) (by omega) (by omega) hc hD h4 h12
    exact WP.of_runBlock ⟨s₄, run₄, C, he₄.sp⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.trans e₂.symm⟩

/-- The last bytes of the data. -/
theorem ctrTail_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (VG.Proof.AesCcm.Arm.CrI k w sp R nl D n) ctrTail := by
  refine CT.seq (J := fun s => VG.Proof.AesCcm.Arm.CrI k w sp R nl D n s ∧ s.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧
    s.z = decide (n % 16 = 0)) ?_ (fun s h => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5])
        (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2, h₂.2.2.2.2]) hc
  · obtain ⟨s₁, run₁, h6, hz, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.split15_ok hn4 h.2.2.2.2
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r _ b => g₁ r b) k₁, h6, hz⟩
  refine CT.ite (decide (n % 16 = 0)) (fun s h => h.2.2) (fun _ => CT.skip) fun _ => ?_
  let J₃ : State → Prop := fun s => VG.Proof.AesCcm.Arm.Env k w sp R (14 - nl) s ∧ s.gpr .r4 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n ∧
    s.gpr .r6 = BitVec.ofNat 32 (n % 16)
  refine CT.seq (J := fun s => CtrCall s k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 80)
      (w + BitVec.ofNat 32 384) R 1 ∧ J₃ s) ?_ (fun s ⟨⟨he, ⟨nonce, hl, hc⟩, _, h4, h5⟩, h6, _⟩ => ?_)
    (CT.seq (J := J₃) ?_ (fun s ⟨C, he, h4, h5, h6⟩ => WP.mono (ctr_call C) fun s' P =>
      ⟨he.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h4],
        by rw [P.saved _ (by decide) (by decide), h5], by rw [P.saved _ (by decide) (by decide), h6]⟩) ?_)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5, .r8, .r9, .r10, .r11])
        (.block (zero16 ksO ++ [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++ ctrAt ++ ctrArgs ++
          [addI .r3 .r11 ksO, .mov .r12 (imm 1)])) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · rw [h₁.1.2.2.2.2, h₂.1.2.2.2.2]
    · exact VG.Proof.AesCcm.Arm.env_eq h₁.1.1 h₂.1.1 hr
  · obtain ⟨s₅, run₅, C, he₅, g₅, -⟩ := VG.Proof.AesCcm.Arm.ctrTailArgs_ok L he hR (nonce := nonce) (by omega) (by omega) hc
      (by rw [hl]; exact hn) hn4 h5
    exact WP.of_runBlock ⟨s₅, run₅, C, he₅, by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h4], by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h5],
      by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]⟩
  · exact CT.ctr fun _ _ ⟨C₁, e₁⟩ ⟨C₂, e₂⟩ => ⟨_, _, _, _, _, _, C₁, C₂, e₁.1.sp.trans e₂.1.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r8, .r9, .r10, .r11])
        (.seq (.block [addI .r1 .r11 ksO, .dp .sub .r2 .r5 (.reg .r6), .dp .add .r2 .r2 (.reg .r4),
          .mov .r3 (.reg .r6)]) xorLoop) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · exact VG.Proof.AesCcm.Arm.env_eq h₁.1 h₂.1 hr

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.CTFn`. -/
section

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_seal` and `vg_aes_ccm_open` are constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments (`onePub`) both satisfy the invariants of the same
public values (`entryI`), piece by piece. `open` compares the tags and masks
the data without a branch: whether the tag is right, in `r0` and `r7`, is
never branched on nor used as an address.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI recv cmp uO restore)
open VG.Proof.AesGcm.Arm (CT bytesAt_frame savedR)
open VG.Proof.AesCcm (length_bytesAt)

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- Counter mode. -/
theorem ctr_ct (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) ctr := by
  refine CT.seq (J := VG.Proof.AesCcm.Arm.CrI k w sp R nl D n) ?_ (fun s ⟨o, he, c0⟩ => ?_) ?_
  · exact CT.args [] (fun s h => h.1.pubArgs) (fun _ _ _ _ _ h => by simp at h) ⟨_, by taint_decide⟩
  · obtain ⟨s₁, run₁, h4, h5, g₁, k₁⟩ := VG.Proof.AesCcm.Arm.dataLd_ok o.ar.stk o.eD o.en
    have hD : VG.Proof.AesCcm.Arm.Dat k w sp s D n := by have := o.ar.data; rwa [o.sp] at this
    obtain ⟨nonce, hl, hc⟩ := c0
    exact WP.of_runBlock ⟨s₁, run₁, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr,
      ⟨nonce, hl, by rw [k₁.mem]; exact hc⟩, hD.of_eq k₁.rd k₁.wr, h4, h5⟩
  refine CT.seq (J := VG.Proof.AesCcm.Arm.CrI k w sp R nl D n) (VG.Proof.AesCcm.Arm.ctrWhole_ct L hR h7 h13 hn4) (fun s ⟨he, ⟨nonce, hl, hc⟩, hD, h4, h5⟩ => ?_)
    (VG.Proof.AesCcm.Arm.ctrTail_ct L hR h7 h13 hn hn4)
  refine WP.mono (VG.Proof.AesCcm.Arm.ctrWhole_ok L he hR (nonce := nonce) (by omega) (by omega) hc hD (by rw [hl]; exact hn) hn4 h4 h5)
    fun s' ⟨he', rd, wr, g, f, _⟩ => ⟨he', ⟨nonce, hl, ?_⟩, hD.of_eq rd wr, by rw [g _ (by decide) (by decide), h4],
      by rw [g _ (by decide) (by decide), h5]⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact ((hD.buf.w.sub_left (Region.sub_prefix (Nat.mul_div_le n 16))).sub_right
        (Lay.wSub (by decide))).symm) (by decide), hc]

end

/-- At the entry: one run, and the registers holding the key schedule, the
rounds and the nonce. -/
def EntI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  VG.Proof.AesCcm.Arm.One k w sp N A D T R nl al n tl s ∧ s.gpr .r0 = k ∧ s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = N ∧
    s.gpr .r3 = BitVec.ofNat 32 nl

/-- After the entry. -/
def AftI (k w sp N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop :=
  VG.Proof.AesCcm.Arm.One k w sp N A D T R nl al n tl s ∧ VG.Proof.AesCcm.Arm.Env k w sp R (s.gpr .r10).toNat s ∧ s.gpr .r2 = N ∧
    s.gpr .r3 = BitVec.ofNat 32 nl

section
variable {k w sp N A D T : BitVec 32} {R nl al n tl : Nat} (L : VG.Proof.AesCcm.Arm.Lay k w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)

/-- The entry. -/
theorem entry_ct : CT (VG.Proof.AesCcm.Arm.EntI k w sp N A D T R nl al n tl) (.block entry) :=
  CT.args [.r0, .r1, .r2, .r3] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2, h₂.2.2.2.2]) ⟨_, by taint_decide⟩

theorem entry_wpI {s : State} (h : VG.Proof.AesCcm.Arm.EntI k w sp N A D T R nl al n tl s) :
    WP isa (.block entry) s (VG.Proof.AesCcm.Arm.AftI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, h0, h1, h2, h3⟩ := h
  refine WP.mono (VG.Proof.AesCcm.Arm.entry_wp o.ar h0 h1 o.eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, _, f₁⟩ => ?_
  have hsp : s₁.sp = s.sp := he₁.sp
  rw [o.sp] at he₁
  refine ⟨o.next' f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact o.ar.stk.aw.sub_right (Lay.wSub (by decide)))
    hsp rd₁ wr₁, he₁, by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2],
    by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]⟩

/-- `Ctr₀`. -/
theorem ctrs_ct : CT (VG.Proof.AesCcm.Arm.AftI k w sp N A D T R nl al n tl) ctrs :=
  CT.args [.r2, .r3, .r8, .r9, .r11] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1.r8, h₂.2.1.r8]
    · rw [h₁.2.1.r9, h₂.2.1.r9]
    · rw [h₁.2.1.r11, h₂.2.1.r11]) ⟨_, by taint_decide⟩

include L in
theorem ctrs_wpI {s : State} (h : VG.Proof.AesCcm.Arm.AftI k w sp N A D T R nl al n tl s) :
    WP isa ctrs s (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, h2, h3⟩ := h
  have hN : VG.Proof.AesCcm.Arm.Buf w sp s N nl := by have := o.ar.nonce; rwa [o.sp] at this
  refine WP.mono (VG.Proof.AesCcm.Arm.ctrs_ok L he hN h2 h3 o.ar.h7 o.ar.h13) fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  refine ⟨o.next f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.Arm.w_mut (.inl (by decide))) sp₂ rd₂ wr₂,
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he.r11],
      by rw [sp₂, he.sp], he.perm.of_eq rd₂ wr₂⟩, _, length_bytesAt _ _ _, c₂⟩

include L hR

theorem mac_wpI {y : Nat} (hy : y = 0 ∨ y = 112) {s : State} (h : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s) :
    WP isa (VG.Impl.AesCcm.Arm.mac y) s (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  have Ar := o.ar
  have hA : VG.Proof.AesCcm.Arm.Buf w sp s A al := by have := Ar.aad; rwa [o.sp] at this
  have hD : VG.Proof.AesCcm.Arm.Buf w sp s D n := by have := Ar.data.buf; rwa [o.sp] at this
  exact WP.mono (VG.Proof.AesCcm.Arm.mac_ok L he Ar.stk o.sp hR o.eA o.eal o.eD o.en o.etl hl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32
    Ar.n32 Ar.hn hc hy hA hD) fun _ M => MacI.next hy h M

theorem tag_wpI {y : Nat} (hy : y = 0 ∨ y = 112) {s : State} (h : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s) :
    WP isa (tag y) s (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  refine WP.mono (VG.Proof.AesCcm.Arm.tag_ok L he hR (nonce := nonce) (by rw [hl]; exact o.ar.h7) (by rw [hl]; exact o.ar.h13) hc hy)
    fun s' ⟨he', rd, wr, _, f, _⟩ => h.of he' f (fun r hr => ?_) (fun r hr => ?_) rd wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact VG.Proof.AesCcm.Arm.w_mut (.inl (by decide))
    · exact VG.Proof.AesCcm.Arm.w_mut (.inl (by omega))
    · exact VG.Proof.AesCcm.Arm.w_mut (.inr ⟨by decide, by decide⟩)
    · exact VG.Proof.AesCcm.Arm.blw_mut
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm

theorem ctr_wpI {s : State} (h : VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl s) :
    WP isa ctr s (VG.Proof.AesCcm.Arm.MacI k w sp N A D T R nl al n tl) := by
  obtain ⟨o, he, nonce, hl, hc⟩ := id h
  have hD : VG.Proof.AesCcm.Arm.Dat k w sp s D n := by have := o.ar.data; rwa [o.sp] at this
  refine WP.mono (VG.Proof.AesCcm.Arm.ctr_ok L he o.ar.stk hR (nonce := nonce) (by rw [hl]; exact o.ar.h7) (by rw [hl]; exact o.ar.h13)
    hc o.eD o.en hD (by rw [hl]; exact o.ar.hn) o.ar.n32) fun s' ⟨he', rd, wr, _, f, _⟩ =>
      h.of he' f VG.Proof.AesCcm.Arm.ctrR_mut (fun r hr => ?_) rd wr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (hD.buf.w.sub_right (Lay.wSub (by decide))).symm

/-- `vg_aes_ccm_seal`, from the entry invariant. -/
theorem seal_ctI (hal : al < 2 ^ 32) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (VG.Proof.AesCcm.Arm.EntI k w sp N A D T R nl al n tl) «seal» := by
  refine CT.seq VG.Proof.AesCcm.Arm.entry_ct (fun _ h => VG.Proof.AesCcm.Arm.entry_wpI h) ?_
  refine CT.seq VG.Proof.AesCcm.Arm.ctrs_ct (fun _ h => VG.Proof.AesCcm.Arm.ctrs_wpI L h) ?_
  refine CT.seq (VG.Proof.AesCcm.Arm.mac_ct L hR hal (.inl rfl) hn4) (fun _ h => VG.Proof.AesCcm.Arm.mac_wpI L hR (.inl rfl) h) ?_
  refine CT.seq (VG.Proof.AesCcm.Arm.tag_ct L hR (.inl rfl)) (fun _ h => VG.Proof.AesCcm.Arm.tag_wpI L hR (.inl rfl) h) ?_
  refine CT.seq (VG.Proof.AesCcm.Arm.ctr_ct L hR h7 h13 hn hn4) (fun _ h => VG.Proof.AesCcm.Arm.ctr_wpI L hR h) ?_
  -- The copy of the tag to `tag`, a public stack argument, and the exit.
  exact CT.args [.r11] (fun s h => h.1.pubArgs) (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1.r11, h₂.2.1.r11]) ⟨_, by taint_decide⟩

/-- `vg_aes_ccm_open`, from the entry invariant. -/
theorem open_ctI (hal : al < 2 ^ 32) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn : n < 256 ^ (15 - nl)) (hn4 : n < 2 ^ 32) :
    CT (VG.Proof.AesCcm.Arm.EntI k w sp N A D T R nl al n tl) «open» := by
  refine CT.seq VG.Proof.AesCcm.Arm.entry_ct (fun _ h => VG.Proof.AesCcm.Arm.entry_wpI h) ?_
  refine CT.seq VG.Proof.AesCcm.Arm.ctrs_ct (fun _ h => VG.Proof.AesCcm.Arm.ctrs_wpI L h) ?_
  refine CT.seq (VG.Proof.AesCcm.Arm.ctr_ct L hR h7 h13 hn hn4) (fun _ h => VG.Proof.AesCcm.Arm.ctr_wpI L hR h) ?_
  refine CT.seq (VG.Proof.AesCcm.Arm.mac_ct L hR hal (.inr rfl) hn4) (fun _ h => VG.Proof.AesCcm.Arm.mac_wpI L hR (.inr rfl) h) ?_
  refine CT.seq (VG.Proof.AesCcm.Arm.tag_ct L hR (.inr rfl)) (fun _ h => VG.Proof.AesCcm.Arm.tag_wpI L hR (.inr rfl) h) ?_
  exact CT.args [.r8, .r9, .r10, .r11] (fun s h => h.1.pubArgs)
    (fun s₁ s₂ h₁ h₂ r hr => VG.Proof.AesCcm.Arm.env_eq h₁.2.1 h₂.2.1 (by simpa using hr)) ⟨_, by taint_decide⟩

end

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Verified`. -/
section

/-!
# AES-CCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ccm/Contract.lean` with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with 16 bytes of stack: each call pushes two
words, and `vg_cmac_aes_update` pushes two more for its own call of
`vg_aes_ctr32`. `Frame.lean` allocates the working space.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- The entry invariant of a run, from the arguments. -/
theorem entI_of {s : State} {T : BitVec 32} {tl : Nat}
    (Ar : VG.Proof.AesCcm.Arm.Args s (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat tl) (hT : VG.Proof.AesCcm.Arm.arg s 4 = T) (htl : VG.Proof.AesCcm.Arm.arg s 5 = BitVec.ofNat 32 tl)
    (hwr : ∀ r ∈ s.wr, (VG.Proof.AesCcm.Arm.args s 7).Disjoint r) :
    VG.Proof.AesCcm.Arm.EntI (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) s.sp (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) T (s.gpr .r1).toNat (s.gpr .r3).toNat
      (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat tl s :=
  ⟨⟨Ar, rfl, hwr, rfl, (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm, rfl, (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm, hT, htl, rfl⟩,
    rfl, (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm, rfl, (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm⟩

/-- The entry invariant of `seal`'s runs. -/
theorem entI_seal {s : State} (h : sealArm.pre s) :
    VG.Proof.AesCcm.Arm.EntI (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) s.sp (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (VG.Proof.AesCcm.Arm.arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 5).toNat s := by
  have A := VG.Proof.AesCcm.Arm.args_of_seal h
  refine VG.Proof.AesCcm.Arm.entI_of A.1.1 rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.1.1.da.symm
  · exact A.2.2.symm
  · exact A.1.1.stk.aw

/-- The entry invariant of `open`'s runs. -/
theorem entI_open {s : State} (h : openArm.pre s) :
    VG.Proof.AesCcm.Arm.EntI (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) s.sp (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (VG.Proof.AesCcm.Arm.arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 5).toNat s := by
  have A := VG.Proof.AesCcm.Arm.args_of_open h
  refine VG.Proof.AesCcm.Arm.entI_of A.1.1 rfl (VG.Proof.AesCcm.Arm.ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.1.1.da.symm
  · exact A.1.1.stk.aw

/-- The second run, with the first's public arguments. -/
theorem entI_pub {pre : State → Prop}
    (hpre : ∀ {s}, pre s → VG.Proof.AesCcm.Arm.EntI (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) s.sp (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (VG.Proof.AesCcm.Arm.arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 5).toNat s)
    {s₁ s₂ : State} (h₂ : pre s₂) (hq : VG.Proof.AesCcm.Arm.onePub s₁ s₂) :
    VG.Proof.AesCcm.Arm.EntI (s₁.gpr .r0) (VG.Proof.AesCcm.Arm.arg s₁ 6) s₁.sp (s₁.gpr .r2) (VG.Proof.AesCcm.Arm.arg s₁ 0) (VG.Proof.AesCcm.Arm.arg s₁ 2) (VG.Proof.AesCcm.Arm.arg s₁ 4) (s₁.gpr .r1).toNat
      (s₁.gpr .r3).toNat (VG.Proof.AesCcm.Arm.arg s₁ 1).toNat (VG.Proof.AesCcm.Arm.arg s₁ 3).toNat (VG.Proof.AesCcm.Arm.arg s₁ 5).toNat s₂ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have e := hpre h₂
  rwa [← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide), ← qa 6 (by decide)] at e

theorem one_ct {pre : State → Prop}
    (hpre : ∀ {s}, pre s → VG.Proof.AesCcm.Arm.EntI (s.gpr .r0) (VG.Proof.AesCcm.Arm.arg s 6) s.sp (s.gpr .r2) (VG.Proof.AesCcm.Arm.arg s 0) (VG.Proof.AesCcm.Arm.arg s 2) (VG.Proof.AesCcm.Arm.arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (VG.Proof.AesCcm.Arm.arg s 1).toNat (VG.Proof.AesCcm.Arm.arg s 3).toNat (VG.Proof.AesCcm.Arm.arg s 5).toNat s)
    {c : Prog isa}
    (hc : ∀ {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}, VG.Proof.AesCcm.Arm.Lay k w sp → (R = 10 ∨ R = 12 ∨ R = 14) →
      al < 2 ^ 32 → 7 ≤ nl → nl ≤ 13 → n < 256 ^ (15 - nl) → n < 2 ^ 32 →
      Proof.AesGcm.Arm.CT (VG.Proof.AesCcm.Arm.EntI k w sp N A D T R nl al n tl) c)
    {pub : State → State → Prop} (hp : ∀ s₁ s₂, pub s₁ s₂ → VG.Proof.AesCcm.Arm.onePub s₁ s₂) :
    ConstantTime isa pre pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have Ar := (hpre h₁).1.ar
  exact (hc Ar.lay Ar.rounds Ar.al32 Ar.h7 Ar.h13 Ar.hn Ar.n32 _ _ _ _ _ _ ⟨hpre h₁, VG.Proof.AesCcm.Arm.entI_pub hpre h₂ (hp _ _ hq)⟩
    e₁ e₂).1

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  VG.Proof.AesCcm.Arm.one_ct VG.Proof.AesCcm.Arm.entI_seal (fun L hR hal h7 h13 hn hn4 => VG.Proof.AesCcm.Arm.seal_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  VG.Proof.AesCcm.Arm.one_ct VG.Proof.AesCcm.Arm.entI_open (fun L hR hal h7 h13 hn hn4 => VG.Proof.AesCcm.Arm.open_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h.1

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 7 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { VG.Proof.AesCcm.Arm.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 28⟩], wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesCcm.sealScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesCcm.Arm.seal_wp hs) VG.Proof.AesCcm.Arm.seal_ct (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
      VG.Proof.AesCcm.Arm.sealArm, VG.Proof.AesCcm.Arm.sealPre, VG.Proof.AesCcm.Arm.oneLay, VG.Proof.AesCcm.Arm.onePub, VG.Proof.AesCcm.Arm.bel16, VG.Proof.AesCcm.Arm.arg, VG.Proof.AesCcm.Arm.args, VG.Proof.AesCcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesCcm.Arm.sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesCcm.openScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesCcm.Arm.open_wp hs) VG.Proof.AesCcm.Arm.open_ct
    { pre := by
        sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          VG.Proof.AesCcm.Arm.openArm, VG.Proof.AesCcm.Arm.openPre, VG.Proof.AesCcm.Arm.oneLay, VG.Proof.AesCcm.Arm.onePub, VG.Proof.AesCcm.Arm.openLeak, VG.Proof.AesCcm.Arm.bel16, VG.Proof.AesCcm.Arm.arg, VG.Proof.AesCcm.Arm.args, VG.Proof.AesCcm.Arm.roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [VG.Proof.AesCcm.Arm.openArm, VG.Proof.AesCcm.Arm.openRes, VG.Proof.AesCcm.Arm.ciph, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          VG.Proof.AesCcm.Arm.openArm, VG.Proof.AesCcm.Arm.openPre, VG.Proof.AesCcm.Arm.oneLay, VG.Proof.AesCcm.Arm.onePub, VG.Proof.AesCcm.Arm.openLeak, VG.Proof.AesCcm.Arm.bel16, VG.Proof.AesCcm.Arm.arg, VG.Proof.AesCcm.Arm.args, VG.Proof.AesCcm.Arm.roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
        · exact a6
      sat := by
        sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          VG.Proof.AesCcm.Arm.openArm, VG.Proof.AesCcm.Arm.openPre, VG.Proof.AesCcm.Arm.oneLay, VG.Proof.AesCcm.Arm.onePub, VG.Proof.AesCcm.Arm.openLeak, VG.Proof.AesCcm.Arm.bel16, VG.Proof.AesCcm.Arm.arg, VG.Proof.AesCcm.Arm.args, VG.Proof.AesCcm.Arm.roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesCcm.Arm.openSat }

end VG.Proof.AesCcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.Arm.Frame`. -/
section

/-!
# AES-CCM on ARMv7, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): their working space is their seventh stack
argument, after `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`, so the
frame of 2592 bytes holds a copy of those six words, the address of the
working space, the saved `lr` and the working space. The copies are read
only where the pre- and postconditions read the buffers, and `open`'s leak,
whether it succeeds, reads only its buffers (`Proof/AesCcm/Scratch.lean`).
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { VG.Proof.AesCcm.Arm.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract Arm.abi 2608).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesCcm.Arm.sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»)
      (Spec.Ccm.sealContract Arm.abi 2608) :=
  Arm.Verified.stackScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre Arm.abi.ptrBits)
    (post := Spec.Ccm.sealPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 6) VG.Proof.AesCcm.Arm.seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) VG.Proof.AesCcm.Arm.sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { VG.Proof.AesCcm.Arm.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract Arm.abi 2608).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesCcm.Arm.openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Spec.Ccm.openContract Arm.abi 2608) :=
  Arm.Verified.stackScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre Arm.abi.ptrBits)
    (post := Spec.Ccm.openPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak Arm.abi.ptrBits))
    (m := 6) VG.Proof.AesCcm.Arm.open_verified (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) VG.Proof.AesCcm.Arm.openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.Arm

end
