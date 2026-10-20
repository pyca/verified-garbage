module

import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# The ARMv7 PKCS #1 v1.5 functions: their callees SHA-256 and HMAC-SHA-256

The contracts of SHA-256's `init`, `update` and `finalize` and of
HMAC-SHA-256's `init` (for a key of any length) and `finalize` (with their
working space in their own frames), at a call with given arguments: what the call needs (`*_pre`), that
two calls with the same arguments are related as their contract asks
(`*_pub`), and what the call gives (`*_post`). The 64-bit `count` is in
`r2:r3`, the low word in `r2`; ours are below `2^32`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm

open VG VG.Arm VG.Proof.RsaPkcs1Sig.Arm

/-- The `S` bytes below a call's stack pointer. -/
abbrev lowR (sp : BitVec 32) (S : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 S, S⟩

theorem count_eq {lo : Nat} (h : lo < 2 ^ 32) :
    (0 : BitVec 32) ++ BitVec.ofNat 32 lo = BitVec.ofNat 64 lo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]
  simp

/-! ## SHA-256's `init(state)` -/

theorem shInit_pre {s : State} {st : BitVec 32} (h0 : s.gpr .r0 = st) (fit : st.toNat + 96 ≤ 2 ^ 32) :
    (Spec.Sha256.initContract abi).pre (s.callEntry.withRegions [] [⟨State.addr st, 96⟩]) := by
  sig_pre [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argRegs, reduceClassify, Loc.val]
  rw [h0]
  exact ⟨by have := s.sp.isLt; omega, rfl, fit⟩

theorem shInit_pub {s₁ s₂ : State} {st : BitVec 32} (h₁ : s₁.gpr .r0 = st) (h₂ : s₂.gpr .r0 = st)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Sha256.initContract abi).pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argRegs, reduceClassify, Loc.val]
  exact ⟨hsp, by rw [h₁, h₂]⟩

theorem shInit_post {s t : State} {st : BitVec 32} (h0 : s.gpr .r0 = st) {rd wr : List Region}
    (hp : (Spec.Sha256.initContract abi).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr)) :
    Spec.Sha256.Repr t.mem (State.addr st) [] := by
  sig_post [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argRegs, reduceClassify, Loc.val] at hp
  rw [h0] at hp
  exact hp

/-! ## SHA-256's `update(state, count, data, len)` -/

/-- The call's arguments. -/
structure UpdArgs (s : State) (st data : BitVec 32) (len cnt : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r2 : s.gpr .r2 = BitVec.ofNat 32 cnt
  r3 : s.gpr .r3 = 0
  a0 : stackArg s 0 = data
  a1 : stackArg s 1 = BitVec.ofNat 32 len
  len32 : len < 2 ^ 32
  cnt32 : cnt < 2 ^ 32

abbrev updRd (sp data : BitVec 32) (len : Nat) : List Region := [⟨State.addr data, len⟩, ⟨State.addr sp, 8⟩]
abbrev updWr (st : BitVec 32) : List Region := [⟨State.addr st, 96⟩]

section
variable {s : State} {st data : BitVec 32} {len cnt : Nat}

theorem upd_pre {sp : BitVec 32} (h : UpdArgs s st data len cnt) (hspE : s.sp = sp) (hsp : 624 ≤ sp.toNat)
    (hsa : sp.toNat + 8 ≤ 2 ^ 32) (dSD : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr data, len⟩)
    (dSA : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr sp, 8⟩)
    (lo : ∀ r ∈ updWr st ++ updRd sp data len, (lowR sp 624).Disjoint r)
    (fS : st.toNat + 96 ≤ 2 ^ 32) (fD : data.toNat + len ≤ 2 ^ 32) :
    (Spec.Sha256.updateContract abi 624).pre (s.callEntry.withRegions (updRd sp data len) (updWr st)) := by
  subst hspE
  sig_pre [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.a0, h.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.len32]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  exact ⟨hsp, hsa, rfl, rfl, dSD, dSA, lo _ (by simp [State.addr]), lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), fS, fD⟩

theorem upd_pub {s₁ s₂ : State} (h₁ : UpdArgs s₁ st data len cnt) (h₂ : UpdArgs s₂ st data len cnt)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Sha256.updateContract abi 624).pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r2, h₁.r3, h₁.a0, h₁.a1, h₂.r0, h₂.r2, h₂.r3, h₂.a0, h₂.a1]
  exact ⟨hsp, trivial, trivial, trivial, trivial, trivial⟩

theorem upd_post {t : State} (h : UpdArgs s st data len cnt) {rd wr : List Region}
    (hp : (Spec.Sha256.updateContract abi 624).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr))
    {iv : Spec.Sha256.HashValue} {msg : List Byte} (hr : Spec.Sha256.ReprFrom iv s.mem (State.addr st) msg)
    (hl : msg.length = cnt) :
    Spec.Sha256.ReprFrom iv t.mem (State.addr st) (msg ++ Spec.Rsa.bytesAt s.mem (State.addr data) len) := by
  sig_post [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost, abi, argRegs,
    reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r2, h.r3, h.a0, h.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.len32] at hp
  exact hp iv msg hr (by rw [count_eq h.cnt32, hl])

end

/-! ## SHA-256's `finalize(state, count, out)` -/

/-- The call's arguments. -/
structure FinArgs (s : State) (st out : BitVec 32) (cnt : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r2 : s.gpr .r2 = BitVec.ofNat 32 cnt
  r3 : s.gpr .r3 = 0
  a0 : stackArg s 0 = out
  cnt32 : cnt < 2 ^ 32

abbrev finRd (sp : BitVec 32) : List Region := [⟨State.addr sp, 4⟩]
abbrev finWr (st out : BitVec 32) : List Region := [⟨State.addr st, 96⟩, ⟨State.addr out, 32⟩]

section
variable {s : State} {st out : BitVec 32} {cnt : Nat}

theorem fin_pre {sp : BitVec 32} (h : FinArgs s st out cnt) (hspE : s.sp = sp) (hsp : 624 ≤ sp.toNat)
    (hsa : sp.toNat + 4 ≤ 2 ^ 32) (dSO : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr out, 32⟩)
    (dSA : Region.Disjoint ⟨State.addr st, 96⟩ ⟨State.addr sp, 4⟩)
    (dOA : Region.Disjoint ⟨State.addr out, 32⟩ ⟨State.addr sp, 4⟩)
    (lo : ∀ r ∈ finWr st out ++ finRd sp, (lowR sp 624).Disjoint r)
    (fS : st.toNat + 96 ≤ 2 ^ 32) (fO : out.toNat + 32 ≤ 2 ^ 32) :
    (Spec.Sha256.finalizeContract abi 624).pre (s.callEntry.withRegions (finRd sp) (finWr st out)) := by
  subst hspE
  sig_pre [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.a0]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  exact ⟨hsp, hsa, rfl, rfl, dSO, dSA, dOA, lo _ (by simp [State.addr]), lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), fS, fO⟩

theorem fin_pub {s₁ s₂ : State} (h₁ : FinArgs s₁ st out cnt) (h₂ : FinArgs s₂ st out cnt)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Sha256.finalizeContract abi 624).pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r2, h₁.r3, h₁.a0, h₂.r0, h₂.r2, h₂.r3, h₂.a0]
  exact ⟨hsp, trivial, trivial, trivial, trivial⟩

theorem fin_post {t : State} (h : FinArgs s st out cnt) {rd wr : List Region}
    (hp : (Spec.Sha256.finalizeContract abi 624).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr))
    {iv : Spec.Sha256.HashValue} {msg : List Byte} (hr : Spec.Sha256.ReprFrom iv s.mem (State.addr st) msg)
    (hl : msg.length = cnt) :
    Spec.Rsa.bytesAt t.mem (State.addr out) 32 = Spec.Sha256.finalHash iv msg := by
  sig_post [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost, abi, argRegs,
    reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r2, h.r3, h.a0] at hp
  exact hp iv msg hr (by rw [count_eq h.cnt32, hl])

end

/-! ## HMAC-SHA-256's `init(inner, outer, key, key_len)` -/

/-- The call's arguments. -/
structure HiArgs (s : State) (inn out key : BitVec 32) (kl : Nat) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = out
  r2 : s.gpr .r2 = key
  r3 : s.gpr .r3 = BitVec.ofNat 32 kl
  kl64 : kl ≤ 64

abbrev hiRd (key : BitVec 32) (kl : Nat) : List Region := [⟨State.addr key, kl⟩]
abbrev hiWr (inn out : BitVec 32) : List Region := [⟨State.addr inn, 96⟩, ⟨State.addr out, 96⟩]

section
variable {s : State} {inn out key : BitVec 32} {kl : Nat}

theorem hi_pre {sp : BitVec 32} (h : HiArgs s inn out key kl) (hspE : s.sp = sp) (hsp : 1656 ≤ sp.toNat)
    (dIO : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr out, 96⟩)
    (dIK : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr key, kl⟩)
    (dOK : Region.Disjoint ⟨State.addr out, 96⟩ ⟨State.addr key, kl⟩)
    (lo : ∀ r ∈ hiWr inn out ++ hiRd key kl, (lowR sp 1656).Disjoint r)
    (fI : inn.toNat + 96 ≤ 2 ^ 32) (fO : out.toNat + 96 ≤ 2 ^ 32) (fK : key.toNat + kl ≤ 2 ^ 32) :
    (Spec.Hmac.sha256I.initAnyKeyContract abi 1656).pre (s.callEntry.withRegions (hiRd key kl) (hiWr inn out)) := by
  subst hspE
  have k32 : kl < 2 ^ 32 := by have := h.kl64; omega
  sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [h.r0, h.r1, h.r2, h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32]
  exact ⟨hsp, by have := s.sp.isLt; omega, rfl, rfl, dIO, dIK, dOK, lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), lo _ (by simp [State.addr]), fI, fO, fK⟩

theorem hi_pub {s₁ s₂ : State} (h₁ : HiArgs s₁ inn out key kl) (h₂ : HiArgs s₂ inn out key kl)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Hmac.sha256I.initAnyKeyContract abi 1656).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3]
  exact ⟨hsp, trivial, trivial, trivial, trivial⟩

theorem hi_post {t : State} (h : HiArgs s inn out key kl) {rd wr : List Region}
    (hp : (Spec.Hmac.sha256I.initAnyKeyContract abi 1656).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr)) :
    let k0 := Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Rsa.bytesAt s.mem (State.addr key) kl)
    Spec.Sha256.Repr t.mem (State.addr inn) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
      Spec.Sha256.Repr t.mem (State.addr out) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) := by
  have k32 : kl < 2 ^ 32 := by have := h.kl64; omega
  sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [h.r0, h.r1, h.r2, h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32] at hp
  exact hp

end

/-! ## HMAC-SHA-256's `finalize(inner, outer, count, out)` -/

/-- The call's arguments. -/
structure HfArgs (s : State) (inn ou out : BitVec 32) (cnt : Nat) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = ou
  r2 : s.gpr .r2 = BitVec.ofNat 32 cnt
  r3 : s.gpr .r3 = 0
  a0 : stackArg s 0 = out
  cnt32 : cnt < 2 ^ 32

abbrev hfRd (sp ou : BitVec 32) : List Region := [⟨State.addr ou, 96⟩, ⟨State.addr sp, 4⟩]
abbrev hfWr (inn out : BitVec 32) : List Region := [⟨State.addr inn, 96⟩, ⟨State.addr out, 32⟩]

section
variable {s : State} {inn ou out : BitVec 32} {cnt : Nat}

theorem hf_pre {sp : BitVec 32} (h : HfArgs s inn ou out cnt) (hspE : s.sp = sp) (hsp : 880 ≤ sp.toNat)
    (hsa : sp.toNat + 4 ≤ 2 ^ 32)
    (dIU : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr ou, 96⟩)
    (dIO : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr out, 32⟩)
    (dIA : Region.Disjoint ⟨State.addr inn, 96⟩ ⟨State.addr sp, 4⟩)
    (dUO : Region.Disjoint ⟨State.addr ou, 96⟩ ⟨State.addr out, 32⟩)
    (dOA : Region.Disjoint ⟨State.addr out, 32⟩ ⟨State.addr sp, 4⟩)
    (lo : ∀ r ∈ hfWr inn out ++ hfRd sp ou, (lowR sp 880).Disjoint r)
    (fI : inn.toNat + 96 ≤ 2 ^ 32) (fU : ou.toNat + 96 ≤ 2 ^ 32) (fO : out.toNat + 32 ≤ 2 ^ 32) :
    (Spec.Hmac.sha256I.finalizeContract abi 880).pre (s.callEntry.withRegions (hfRd sp ou) (hfWr inn out)) := by
  subst hspE
  sig_pre [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.r1, h.a0]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  exact ⟨hsp, hsa, rfl, rfl, dIU, dIO, dIA, dUO, dOA, lo _ (by simp [State.addr]), lo _ (by simp [State.addr]),
    lo _ (by simp [State.addr]), lo _ (by simp [State.addr]), fI, fU, fO⟩

theorem hf_pub {s₁ s₂ : State} (h₁ : HfArgs s₁ inn ou out cnt) (h₂ : HfArgs s₂ inn ou out cnt)
    (hsp : s₁.sp = s₂.sp) (rd wr : List Region) :
    (Spec.Hmac.sha256I.finalizeContract abi 880).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  sig_pub [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.a0, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.a0]
  exact ⟨hsp, trivial, trivial, trivial, trivial, trivial⟩

theorem hf_post {t : State} (h : HfArgs s inn ou out cnt) {rd wr : List Region}
    (hp : (Spec.Hmac.sha256I.finalizeContract abi 880).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr))
    {k0 text : List Byte} (hk : k0.length = 64) (ht : 64 + text.length = cnt)
    (hi : Spec.Sha256.Repr s.mem (State.addr inn) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text))
    (ho : Spec.Sha256.Repr s.mem (State.addr ou) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    Spec.Rsa.bytesAt t.mem (State.addr out) 32 = Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 k0 text := by
  sig_post [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r1, h.r2, h.r3, h.a0] at hp
  have c32 := h.cnt32
  exact hp k0 text hk (by omega) hi (by rw [count_eq h.cnt32, ← ht]) ho

end

end VG.Proof.RsaPkcs1Enc.Arm
