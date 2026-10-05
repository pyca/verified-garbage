import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesCcm.X86_64
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Verified
import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Narrow
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Contract`. -/
section

/-!
# AES-CCM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). `seal` and `open` call `vg_cmac_aes_update`, which calls
`vg_aes_ctr32`, and `vg_aes_ctr32` directly: the return addresses are in the
16 bytes below the stack pointer (`stk16`), which no buffer overlaps, nor
the return address (`ret`).
-/

namespace VG.Proof.AesCcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk16 (s : State) : Region := below (s.gpr .rsp) 16

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop :=
  (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx,
aad = r8, aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24],
tag_len = [rsp + 32], work = [rsp + 40])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨VG.Proof.AesCcm.arg s 0, (VG.Proof.AesCcm.arg s 1).toNat⟩
  let tag : Region := ⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩
  let work : Region := ⟨VG.Proof.AesCcm.arg s 4, 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesCcm.args s 5) ∧ work.Disjoint (VG.Proof.AesCcm.args s 5) ∧
    (VG.Proof.AesCcm.ret s).Disjoint data ∧ (VG.Proof.AesCcm.ret s).Disjoint work ∧
    (VG.Proof.AesCcm.stk16 s).Disjoint sch ∧ (VG.Proof.AesCcm.stk16 s).Disjoint nonce ∧ (VG.Proof.AesCcm.stk16 s).Disjoint aad ∧ (VG.Proof.AesCcm.stk16 s).Disjoint data ∧
    (VG.Proof.AesCcm.stk16 s).Disjoint tag ∧ (VG.Proof.AesCcm.stk16 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (VG.Proof.AesCcm.arg s 0).toNat + (VG.Proof.AesCcm.arg s 1).toNat ≤ 2 ^ 64 ∧
    (VG.Proof.AesCcm.arg s 2).toNat + (VG.Proof.AesCcm.arg s 3).toNat ≤ 2 ^ 64 ∧
    (VG.Proof.AesCcm.arg s 4).toNat + 2560 ≤ 2 ^ 64 ∧ 16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
    VG.Proof.AesCcm.rounds s ∧ valid (VG.Proof.AesCcm.arg s 3).toNat (s.gpr .rcx).toNat (s.gpr .r9).toNat (VG.Proof.AesCcm.arg s 1).toNat = true

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨VG.Proof.AesCcm.arg s 0, (VG.Proof.AesCcm.arg s 1).toNat⟩
  let tag : Region := ⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩
  let work : Region := ⟨VG.Proof.AesCcm.arg s 4, 2560⟩
  s.rd = [sch, nonce, aad, VG.Proof.AesCcm.args s 5] ∧ s.wr = [data, tag, work] ∧ VG.Proof.AesCcm.oneLay s ∧ (VG.Proof.AesCcm.ret s).Disjoint tag

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨VG.Proof.AesCcm.arg s 0, (VG.Proof.AesCcm.arg s 1).toNat⟩
  let tag : Region := ⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩
  let work : Region := ⟨VG.Proof.AesCcm.arg s 4, 2560⟩
  s.rd = [sch, nonce, aad, tag, VG.Proof.AesCcm.args s 5] ∧ s.wr = [data, work] ∧ VG.Proof.AesCcm.oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 5, VG.Proof.AesCcm.arg s₁ i = VG.Proof.AesCcm.arg s₂ i

/-- `vg_aes_ccm_seal`. -/
def sealX86_64 : Contract isa where
  pre := VG.Proof.AesCcm.sealPre
  post s s' :=
    VG.Spec.Ccm.encryptWith (VG.Spec.Ccm.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (VG.Proof.AesCcm.arg s 3).toNat
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat)
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat, VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesCcm.arg s 2) (VG.Proof.AesCcm.arg s 3).toNat)
  pub := VG.Proof.AesCcm.onePub

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesCcm.rounds s then [] else
  [if (VG.Spec.Ccm.decryptWith (VG.Spec.Ccm.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (VG.Proof.AesCcm.arg s 3).toNat
      (VG.Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat)
      (VG.Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesCcm.arg s 2) (VG.Proof.AesCcm.arg s 3).toNat)).isSome
    then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openX86_64 : Contract isa where
  pre := VG.Proof.AesCcm.openPre
  post s s' :=
    match VG.Spec.Ccm.decryptWith (VG.Spec.Ccm.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (VG.Proof.AesCcm.arg s 3).toNat
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat)
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesCcm.arg s 2) (VG.Proof.AesCcm.arg s 3).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat = VG.Spec.Ccm.zeros (VG.Proof.AesCcm.arg s 1).toNat
  pub s₁ s₂ := VG.Proof.AesCcm.onePub s₁ s₂ ∧ VG.Proof.AesCcm.openLeak s₁ = VG.Proof.AesCcm.openLeak s₂

end VG.Proof.AesCcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Env`. -/
section

/-!
# AES-CCM on x86-64: where everything is

Untrusted: everything here is checked by Lean. The key schedule (240 bytes
at `K`), the working space (2560 bytes at `W`) and the 16 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `K` and `W` and the stack pointer (`Env`); and the public
values the entry keeps in `W` (`Slots`). The pieces write the parts of `W`
in `mutR` (and the data, and the stack below `SP`), so the slots, our
caller's registers saved in `W` and the arguments stay as the entry left
them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

/-! ## Arithmetic -/

theorem imm_eq {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt ha, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega), VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega)]
  omega

theorem shr4 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hn, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem and15 (x : BitVec 64) : x &&& (BitVec.ofNat 32 15).signExtend 64 = BitVec.ofNat 64 (x.toNat % 16) := by
  rw [show (BitVec.ofNat 32 15).signExtend 64 = 15#64 by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem and15' (x : BitVec 64) : x &&& 15#64 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## Covering -/

/-- The part of a region at an offset is covered when the region is. -/
theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  VG.Proof.AesCcm.X86_64.covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => VG.Proof.AesCcm.X86_64.in_left (h a n hi)

theorem covers_cons {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil {ts : List Region} : Covers [] ts := fun _ _ ⟨_, h, _⟩ => by cases h

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_append {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

/-! ## The regions -/

/-- The key schedule, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : Addr) : Prop where
  kw : K.toNat + 240 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  k_w : (⟨K, 240⟩ : Region).Disjoint ⟨W, 2560⟩
  stk_k : (below SP 16).Disjoint ⟨K, 240⟩
  stk_w : (below SP 16).Disjoint ⟨W, 2560⟩
  sp : 16 ≤ SP.toNat

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding the key schedule, `W` and the stack pointer, and
what the state may access. -/
structure Env (K W SP : Addr) (s : State) : Prop where
  r13 : s.gpr .r13 = K
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : VG.Proof.AesCcm.X86_64.Perm K W s

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : VG.Proof.AesCcm.X86_64.Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesCcm.X86_64.Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r13`, `r15`, `rsp` and the permissions. -/
theorem Env.keep {K W SP : Addr} {s s' : State} (h : VG.Proof.AesCcm.X86_64.Env K W SP s)
    (hg : ∀ r ∈ [Reg.r13, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesCcm.X86_64.Env K W SP s' :=
  ⟨by rw [hg _ (by simp), h.r13], by rw [hg _ (by simp), h.r15], by rw [hg _ (by simp), h.rsp],
    h.perm.of_eq hrd hwr⟩

theorem Env.of_saved {K W SP : Addr} {s s' : State} (h : VG.Proof.AesCcm.X86_64.Env K W SP s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.X86_64.Env K W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 240) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 240⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 240) (hd : d + k ≤ 2560) :
    (⟨K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (VG.Proof.AesCcm.X86_64.Lay.kSub ha)).sub_right (VG.Proof.AesCcm.X86_64.Lay.wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (below SP 16).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (VG.Proof.AesCcm.X86_64.Lay.wSub ha)

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : VG.Proof.AesCcm.X86_64.Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  VG.Proof.AesCcm.X86_64.in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesCcm.X86_64.in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesCcm.X86_64.in_left (P.wW h)

theorem kC {d n : Nat} (h : d + n ≤ 240) : Covers [⟨K + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Proof.AesCcm.X86_64.covers_off P.k h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesCcm.X86_64.covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`, the
key schedule and the stack below `SP`. -/
structure Buf (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  stk : (below SP 16).Disjoint ⟨D, n⟩

namespace Buf

variable {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesCcm.X86_64.Buf K W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.X86_64.Buf K W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : VG.Proof.AesCcm.X86_64.Buf K W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := VG.Proof.AesCcm.X86_64.covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base D (by omega))
  stk := h.stk.sub_right (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesCcm.X86_64.Buf K W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : VG.Proof.AesCcm.X86_64.Buf K W SP s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the rounds, the nonce and its
length, the associated data and its length, the data and its length, and
the tag length. -/
structure Slots (W : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (m : Mem) : Prop where
  rounds : m.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  nonce : m.readW (W + BitVec.ofNat 64 160) 64 = N
  nlen : m.readW (W + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 nl
  aad : m.readW (W + BitVec.ofNat 64 176) 64 = A
  alen : m.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  data : m.readW (W + BitVec.ofNat 64 192) 64 = D
  len : m.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n
  tl : m.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 tl

/-- The parts of `W` the pieces write: the blocks at `[0, 112)`, the slots
`[216, 232)` and `[240, 2560)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 112⟩
abbrev wK (W : Addr) : Region := ⟨W + BitVec.ofNat 64 216, 16⟩
abbrev wC (W : Addr) : Region := ⟨W + BitVec.ofNat 64 240, 2320⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : Addr) (n : Nat) : List Region := [VG.Proof.AesCcm.X86_64.wA W, VG.Proof.AesCcm.X86_64.wK W, VG.Proof.AesCcm.X86_64.wC W, below SP 16, ⟨D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : Addr} {n : Nat} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {d k : Nat} (hd : 112 ≤ d ∧ d + k ≤ 216 ∨ 232 ≤ d ∧ d + k ≤ 240) :
    ∀ r ∈ VG.Proof.AesCcm.X86_64.mutR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 112) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Callee`. -/
section

/-!
# AES-CCM on x86-64: the functions called

Untrusted: everything here is checked by Lean. A call of `vg_aes_ctr32`
from its contract (with `WP.call`): what it needs (`CtrCall`), what it
leaves (`CtrPost`), and that two calls with the same arguments leak the same
(`ctr_rel`); the calls of `vg_cmac_aes_update` are those of streaming
AES-CMAC (`Proof.CmacAes.Stream.X86_64.upd_call`). `uargs` and `cargs` build
their arguments from the environment: the key schedule, a block of `W` as
the state or the counter block, the data or blocks of `W` as the data, and
the working space at `W + 384`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32 aesWith)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs)

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, VG.Proof.AesCcm.X86_64.bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, VG.Proof.AesCcm.X86_64.bytesAt_frame hf hd hn]

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Ccm.ctxCiph m' K R = Spec.Ccm.ctxCiph m K R := by
  unfold Spec.Ccm.ctxCiph
  rw [VG.Proof.AesCcm.X86_64.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem disj_below {s : State} {p : Addr} {n : Nat} (h : (below (s.gpr .rsp) 8).Disjoint ⟨p, n⟩) :
    ∀ r ∈ [below (s.gpr .rsp) 8], (⟨p, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.symm

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R :=
  VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega)

theorem below8_sub (sp : Addr) : Region.Sub (below sp 8) (below sp 16) :=
  Offset.sub_below sp (a := 8) (b := 16) (by decide) (by decide)

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : blocksAt s'.mem D n = ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
    (blocksAt s.mem D n)

theorem CtrCall.pre {s : State} {K C D S : Addr} {R n : Nat} (h : VG.Proof.AesCcm.X86_64.CtrCall s K C D S R n) :
    Proof.Aes.ctr32X86_64.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := VG.Proof.AesCcm.X86_64.toNat_rounds h.rounds
  have hn := VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.stkC, h.stkD, h.stkS, h.wrap,
    h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {K C D S : Addr} {R n : Nat} (h : VG.Proof.AesCcm.X86_64.CtrCall s K C D S R n) :
    WP isa (.call v.callee.name v.callee.code) s (VG.Proof.AesCcm.X86_64.CtrPost s K C D S R n) := by
  have hR := VG.Proof.AesCcm.X86_64.toNat_rounds h.rounds
  have hn := VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.call (k := Proof.Aes.ctr32X86_64) v.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  obtain ⟨hdata, _⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn,
    hm₂] at hdata
  have fE := VG.Proof.AesCcm.X86_64.callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := VG.Proof.AesCcm.X86_64.bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega)
  rw [VG.Proof.AesCcm.X86_64.blockAt_frame fE (VG.Proof.AesCcm.X86_64.disj_below h.stkC), VG.Proof.AesCcm.X86_64.blocksAt_frame fE (VG.Proof.AesCcm.X86_64.disj_below h.stkD) (by have := h.wrap; omega),
    eK] at hdata
  exact ⟨hrd, hwr, hcs, by simpa using hf, hdata⟩

theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S : Addr, ∃ R n : Nat,
      VG.Proof.AesCcm.X86_64.CtrCall s₁ K C D S R n ∧ VG.Proof.AesCcm.X86_64.CtrCall s₂ K C D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx v.ok v.ct fun s₁ s₂ hp => ?_
  obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The arguments -/

/-- Data for a call: `k` bytes at `Q`, which the code may read, apart from
the parts of `W` from `384` on and the stack below `SP`. -/
structure Src (W SP : Addr) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 64
  qs : (⟨Q, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 384, 2176⟩
  stk : (below SP 16).Disjoint ⟨Q, k⟩

/-- Bytes of `W` below 384 as data. -/
theorem srcW {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (P : VG.Proof.AesCcm.X86_64.Perm K W s) {t k : Nat} (hk : t + k ≤ 384) :
    VG.Proof.AesCcm.X86_64.Src W SP s (W + BitVec.ofNat 64 t) k where
  rd := VG.Proof.AesCcm.X86_64.covers_left (P.wC (by omega))
  wrap := by
    have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := t) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  qs := L.w_w (.inl (by omega)) (by omega) (by decide)
  stk := L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : VG.Proof.AesCcm.X86_64.Buf K W SP s Q k) : VG.Proof.AesCcm.X86_64.Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

/-- The arguments of `vg_cmac_aes_update`: the key schedule, the state at
`W + y`, `n` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr} {n : Nat}
    (hq : VG.Proof.AesCcm.X86_64.Src W SP s Q (16 * n)) (hqy : (⟨Q, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 64) (rdi : s.gpr .rdi = K) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 y)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 384) :
    UArgs s K (W + BitVec.ofNat 64 y) Q (W + BitVec.ofNat 64 384) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hR
  hn := hn
  wc := by simpa using L.k_w' (a := 0) (n := 240) (d := y) (k := 16) (by decide) (by omega)
  ws := by simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2176) (by decide) (by decide)
  dc := hqy
  ds := hq.qs
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  stkW := by rw [E.rsp]; exact L.stk_k
  stkD := by rw [E.rsp]; exact hq.stk
  stkC := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  wrapC := by
    have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := y) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  wrapD := hq.wrap
  wrapS := by
    have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 384) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  reads := VG.Proof.AesCcm.X86_64.covers_append (VG.Proof.AesCcm.X86_64.covers_cons E.perm.k (VG.Proof.AesCcm.X86_64.covers_cons hq.rd VG.Proof.AesCcm.X86_64.covers_nil))
    (VG.Proof.AesCcm.X86_64.covers_cons (VG.Proof.AesCcm.X86_64.covers_left (E.perm.wC (by omega))) (VG.Proof.AesCcm.X86_64.covers_cons (VG.Proof.AesCcm.X86_64.covers_left (E.perm.wC (by decide))) VG.Proof.AesCcm.X86_64.covers_nil))
  writes := VG.Proof.AesCcm.X86_64.covers_cons (E.perm.wC (by omega)) (VG.Proof.AesCcm.X86_64.covers_cons (E.perm.wC (by decide)) VG.Proof.AesCcm.X86_64.covers_nil)

/-- The arguments of `vg_aes_ctr32`: the key schedule, the counter block at
`W + c`, `n` blocks at `Q`, which it may write, and the working space at
`W + 384`. -/
theorem cargs {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c : Nat} (hc : c + 16 ≤ 384) {Q : Addr} {n : Nat}
    (hq : VG.Proof.AesCcm.X86_64.Src W SP s Q (16 * n)) (hqc : (⟨Q, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 c, 16⟩)
    (hqk : (⟨K, 240⟩ : Region).Disjoint ⟨Q, 16 * n⟩) (hqw : Covers [⟨Q, 16 * n⟩] s.wr)
    (rdi : s.gpr .rdi = K) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 c)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 384) :
    VG.Proof.AesCcm.X86_64.CtrCall s K (W + BitVec.ofNat 64 c) Q (W + BitVec.ofNat 64 384) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hR
  wrap := hq.wrap
  kc := by simpa using L.k_w' (a := 0) (n := 240) (d := c) (k := 16) (by decide) (by omega)
  kd := hqk
  ks := by simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2048) (by decide) (by decide)
  cd := hqc.symm
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  ds := hq.qs.sub_right (Region.sub_prefix (by decide))
  stkK := by rw [E.rsp]; exact L.stk_k.sub_left (VG.Proof.AesCcm.X86_64.below8_sub _)
  stkC := by rw [E.rsp]; exact (L.stk_w' (by omega)).sub_left (VG.Proof.AesCcm.X86_64.below8_sub _)
  stkD := by rw [E.rsp]; exact hq.stk.sub_left (VG.Proof.AesCcm.X86_64.below8_sub _)
  stkS := by rw [E.rsp]; exact (L.stk_w' (a := 384) (n := 2048) (by decide)).sub_left (VG.Proof.AesCcm.X86_64.below8_sub _)
  reads := VG.Proof.AesCcm.X86_64.covers_append (VG.Proof.AesCcm.X86_64.covers_cons E.perm.k VG.Proof.AesCcm.X86_64.covers_nil)
    (VG.Proof.AesCcm.X86_64.covers_cons (VG.Proof.AesCcm.X86_64.covers_left (E.perm.wC (by omega))) (VG.Proof.AesCcm.X86_64.covers_cons hq.rd
      (VG.Proof.AesCcm.X86_64.covers_cons (VG.Proof.AesCcm.X86_64.covers_left (E.perm.wC (by decide))) VG.Proof.AesCcm.X86_64.covers_nil)))
  writes := VG.Proof.AesCcm.X86_64.covers_cons (E.perm.wC (by omega)) (VG.Proof.AesCcm.X86_64.covers_cons hqw (VG.Proof.AesCcm.X86_64.covers_cons (E.perm.wC (by decide)) VG.Proof.AesCcm.X86_64.covers_nil))

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Bytes`. -/
section

/-!
# AES-CCM on x86-64: the bytes of a buffer after writes

Untrusted: everything here is checked by Lean. A write of a byte, a word or
bytes into a buffer replaces those of its bytes (`bytesAt_writeBytes_at`,
`bytesAt_writeW8_at`, `bytesAt_writeW64_at`, `bytesAt_writeW32_at`): the
pieces build their blocks (`Ctr₀`, `B₀`, the first block of the associated
data, a last block padded) as lists.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8 le4)

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem getElem_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n)[i]'(by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact hi) = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt]

/-- `xs` written at `p + o`, inside the `n` bytes at `p`. -/
theorem bytesAt_writeBytes_at (m : Mem) (p : Addr) {o n : Nat} (xs : List Byte) (h : o + xs.length ≤ n)
    (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p n =
      (bytesAt m p n).take o ++ xs ++ (bytesAt m p n).drop (o + xs.length) := by
  apply List.ext_getElem (by simp [VG.Proof.AesCcm.X86_64.length_bytesAt]; omega)
  intro i h₁ h₂
  rw [VG.Proof.AesCcm.X86_64.getElem_bytesAt _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt] at h₁; exact h₁)]
  simp only [writeBytes]
  have hi : i < n := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt] at h₁; exact h₁
  have e : (p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 o)).toNat = (i + (2 ^ 64 - o)) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega), VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega)]
    omega
  rw [e]
  have hl := VG.Proof.AesCcm.X86_64.length_bytesAt m p n
  by_cases hlo : i < o
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = 2 ^ 64 - o + i by omega]
    simp only [show ¬ (2 ^ 64 - o + i < xs.length) by omega, ite_false]
    rw [List.getElem_append_left (by simp [hl]; omega), List.getElem_append_left (by simp [hl]; omega),
      List.getElem_take, VG.Proof.AesCcm.X86_64.getElem_bytesAt _ _ hi]
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = i - o by omega]
    by_cases hhi : i < o + xs.length
    · simp only [show i - o < xs.length by omega, ite_true]
      rw [List.getElem_append_left (by simp [hl]; omega), List.getElem_append_right (by simp [hl]; omega)]
      simp only [List.length_take, hl, List.getD_eq_getElem?_getD, Nat.min_eq_left (show o ≤ n by omega),
        List.getElem?_eq_getElem (show i - o < xs.length by omega), Option.getD_some]
    · simp only [show ¬ (i - o < xs.length) by omega, ite_false]
      rw [List.getElem_append_right (by simp [hl]; omega), List.getElem_drop]
      simp only [List.length_append, List.length_take, hl, Nat.min_eq_left (show o ≤ n by omega)]
      rw [VG.Proof.AesCcm.X86_64.getElem_bytesAt _ _ (by omega), show o + xs.length + (i - (o + xs.length)) = i by omega]

/-- A byte write is a write of one byte. -/
theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, List.length_cons, List.length_nil, Nat.zero_add]
  split
  · rename_i h
    simp only [show (x - a).toNat = 0 by omega, List.getD_cons_zero]
    simp
  · rfl

/-- A word write is a write of its bytes, least significant first. -/
theorem writeW64_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (le8 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le8]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le8 _ h]
    simp
  · rfl

theorem writeW32_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (le4 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le4]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le4 _ h]
    simp
  · rfl

theorem bytesAt_writeW8_at (m : Mem) (p : Addr) {o n : Nat} (b : Byte) (h : o + 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) b) p n = (bytesAt m p n).take o ++ [b] ++ (bytesAt m p n).drop (o + 1) := by
  rw [VG.Proof.AesCcm.X86_64.writeW8_eq, VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at _ _ _ h hn]; rfl

theorem bytesAt_writeW64_at (m : Mem) (p : Addr) {o n : Nat} (v : BitVec 64) (h : o + 8 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) v) p n = (bytesAt m p n).take o ++ le8 v ++ (bytesAt m p n).drop (o + 8) := by
  rw [VG.Proof.AesCcm.X86_64.writeW64_eq, VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at _ _ _ (by rw [Proof.Cmac.length_le8]; exact h) hn, Proof.Cmac.length_le8]

theorem bytesAt_writeW32_at (m : Mem) (p : Addr) {o n : Nat} (v : BitVec 32) (h : o + 4 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) v) p n = (bytesAt m p n).take o ++ le4 v ++ (bytesAt m p n).drop (o + 4) := by
  rw [VG.Proof.AesCcm.X86_64.writeW32_eq, VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at _ _ _ (by rw [Proof.Cmac.length_le4]; exact h) hn, Proof.Cmac.length_le4]

/-- At offset 0. -/
theorem bytesAt_writeBytes_base (m : Mem) (p : Addr) {n : Nat} (xs : List Byte) (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) : bytesAt (writeBytes m p xs) p n = xs ++ (bytesAt m p n).drop xs.length := by
  have := VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at m p (o := 0) xs (by omega) hn
  simpa using this

theorem bytesAt_writeW64_base (m : Mem) (p : Addr) {n : Nat} (v : BitVec 64) (h : 8 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p v) p n = le8 v ++ (bytesAt m p n).drop 8 := by
  have := VG.Proof.AesCcm.X86_64.bytesAt_writeW64_at m p (o := 0) v h hn
  simpa using this

theorem bytesAt_writeW8_base (m : Mem) (p : Addr) {n : Nat} (b : Byte) (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p b) p n = b :: (bytesAt m p n).drop 1 := by
  have := VG.Proof.AesCcm.X86_64.bytesAt_writeW8_at m p (o := 0) b h hn
  simpa using this

/-! ## Words as bytes -/

theorem le8_or (a b : BitVec 64) : le8 (a ||| b) = List.zipWith (· ||| ·) (le8 a) (le8 b) := by
  apply List.ext_getElem (by simp [le8])
  intro k h₁ h₂
  simp only [le8, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem bswap64_bytes (x : BitVec 64) :
    (List.range 8).map (fun j => (bswap64 x).extractLsb' (8 * j) 8) =
      (List.range 8).reverse.map (fun i => x.extractLsb' (8 * i) 8) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp (disch := decide) only [bswap64, Nat.mul_zero, Nat.reduceMul, extractLsb'_append_byte_lo,
      extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self]

theorem le8_bswap64 (x : BitVec 64) : le8 (bswap64 x) = (le8 x).reverse := by
  simp only [le8]
  rw [VG.Proof.AesCcm.X86_64.bswap64_bytes, List.map_reverse]

/-- The bytes of `[v]₆₄`, the most significant first. -/
theorem le8_bswap64_ofNat {v : Nat} (hv : v < 2 ^ 64) : le8 (bswap64 (BitVec.ofNat 64 v)) = Spec.Ccm.be 8 v := by
  rw [VG.Proof.AesCcm.X86_64.le8_bswap64]
  apply List.ext_getElem (by simp [le8, Proof.AesCcm.length_be])
  intro k h₁ h₂
  have hk : k < 8 := by simpa [le8] using h₁
  simp only [List.getElem_reverse, le8, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range, Spec.Ccm.be]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hv, show 8 - 1 - k = 7 - k by omega, show 2 ^ (8 * (7 - k)) = 256 ^ (7 - k) by
    rw [Nat.pow_mul]]

theorem be_zero (k : Nat) : Spec.Ccm.be k 0 = Spec.Ccm.zeros k := by
  simp [Spec.Ccm.be, Spec.Ccm.zeros, List.map_const']

/-- `[v]₈ₖ` for `v < 2^(8q)` and `k ≥ q`: zeros, then `[v]₈q`. -/
theorem be_split {q k v : Nat} (hqk : q ≤ k) (hv : v < 256 ^ q) :
    Spec.Ccm.be k v = Spec.Ccm.zeros (k - q) ++ Spec.Ccm.be q v := by
  induction k with
  | zero => rw [show q = 0 by omega]; simp [Spec.Ccm.zeros, Spec.Ccm.be]
  | succ k ih =>
    rcases Nat.lt_or_ge k q with h | h
    · rw [show q = k + 1 by omega]; simp [Spec.Ccm.zeros]
    · rw [Proof.AesCcm.be_succ, ih h, show k + 1 - q = (k - q) + 1 by omega, Spec.Ccm.zeros, Spec.Ccm.zeros,
        List.replicate_succ, List.cons_append]
      congr 1
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) h))]
      rfl

/-- The last 8 bytes of `Ctrᵢ`: the nonce's bytes after its first 7, then `[i]₈q`. -/
theorem ctrBlock_drop8 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).drop 8 = nonce.drop 7 ++ Spec.Ccm.be (15 - nonce.length) i := by
  simp [Spec.Ccm.ctrBlock, List.drop_append_of_le_length (show 7 ≤ nonce.length from h7)]

theorem ctrBlock_take8 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).take 8 = BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
  simp [Spec.Ccm.ctrBlock, List.take_append_of_le_length (show 7 ≤ nonce.length from h7)]

theorem zipWith_or_zeros_right (xs : List Byte) {n : Nat} (h : xs.length = n) :
    List.zipWith (· ||| ·) xs (Spec.Ccm.zeros n) = xs := by
  subst h
  apply List.ext_getElem (by simp [Spec.Ccm.zeros])
  intro k h₁ h₂
  simp [Spec.Ccm.zeros]

theorem zipWith_or_zeros_left (ys : List Byte) {n : Nat} (h : ys.length = n) :
    List.zipWith (· ||| ·) (Spec.Ccm.zeros n) ys = ys := by
  subst h
  apply List.ext_getElem (by simp [Spec.Ccm.zeros])
  intro k h₁ h₂
  simp [Spec.Ccm.zeros]

/-- `Ctrᵢ`'s last 8 bytes, from `Ctr₀`'s and `[i]₆₄`. -/
theorem ctr_or {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {w : BitVec 64}
    (hw : le8 w = (Spec.Ccm.ctrBlock nonce 0).drop 8) {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) :
    le8 (bswap64 (BitVec.ofNat 64 i) ||| w) = (Spec.Ccm.ctrBlock nonce i).drop 8 := by
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi (by
    rw [show 2 ^ 64 = 256 ^ 8 from rfl]; exact Nat.pow_le_pow_right (by decide) (by omega))
  rw [VG.Proof.AesCcm.X86_64.le8_or, VG.Proof.AesCcm.X86_64.le8_bswap64_ofNat hi64, hw, VG.Proof.AesCcm.X86_64.ctrBlock_drop8 h7, VG.Proof.AesCcm.X86_64.ctrBlock_drop8 h7, VG.Proof.AesCcm.X86_64.be_zero,
    VG.Proof.AesCcm.X86_64.be_split (q := 15 - nonce.length) (by omega) hi,
    List.zipWith_comm_of_comm (f := (· ||| ·)) (fun a b => BitVec.or_comm a b)]
  have hd : (nonce.drop 7).length = 8 - (15 - nonce.length) := by rw [List.length_drop]; omega
  rw [List.zipWith_append (by rw [hd]; simp [Spec.Ccm.zeros]), VG.Proof.AesCcm.X86_64.zipWith_or_zeros_right _ hd,
    VG.Proof.AesCcm.X86_64.zipWith_or_zeros_left _ (Proof.AesCcm.length_be _ _)]

theorem bytesAt_prefix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m p a = (bytesAt m p n).take a := by
  rw [show n = a + (n - a) by omega, Proof.Cmac.Stream.bytesAt_append, List.take_left' (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _)]

theorem bytesAt_suffix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m (p + BitVec.ofNat 64 a) (n - a) = (bytesAt m p n).drop a := by
  conv => rhs; rw [show n = a + (n - a) by omega, Proof.Cmac.Stream.bytesAt_append]
  rw [List.drop_left' (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _)]


end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Run`. -/
section

/-!
# AES-CCM on x86-64: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)

theorem setWidth_imm {n : Nat} : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Runs a block of the instructions the AES-CCM code uses. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, execAlu32, execShift, State.load64, State.store64, State.load32, State.store32,
    State.load8, State.store8, State.ea, State.setReg32, offset_nat, at_, imm, ptr, bO, c0O, c1O, ksO, uO,
    nonceO, nlenO, aadO, alenO, dataO, lenO, tlO, kO, okO, roundsO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, setWidth_imm, and_self, and_true, true_and, $ts,*]) <;> try rfl)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, VG.Proof.AesCcm.X86_64.ofNat_add_ofNat]

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h
theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl
theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem and_self_beq {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a &&& BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  rw [BitVec.and_self]
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt ha] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => VG.Proof.AesCcm.X86_64.seq_assoc3 h)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs`. -/
section

/-!
# AES-CCM on x86-64: `Ctr₀` (`ctrs`)

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte and copies the nonce
after it: `Ctr₀` (`ctrs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)

theorem sub_low_byte {nl : Nat} (h : nl ≤ 14) :
    ((BitVec.ofNat 64 14 - BitVec.ofNat 64 nl).setWidth 8 : Byte) = BitVec.ofNat 8 (15 - nl - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `Ctr₀`, from the nonce `N` of `nl` bytes. -/
theorem ctrs_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (hN : VG.Proof.AesCcm.X86_64.Buf K W SP s N nl) (h7 : 7 ≤ nl)
    (h13 : nl ≤ 13) :
    WP isa VG.Impl.AesCcm.X86_64.ctrs s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N nl) 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h15 := E.r15
  have w₁ := E.perm.wW (show 48 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 56 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 48 + 1 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 168 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 160 + 8 ≤ 2560 by decide)
  have hnl := S.nlen
  have hNp := S.nonce
  obtain ⟨s₁, run₁, hm₁, hsi, hdi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov .rsi (.mem (at_ .r15 nonceO)), .mov .rcx (.mem (at_ .r15 nlenO))] ++ zero16 c0O ++
        [.mov32 .rax (imm 14), .alu .sub .rax (.reg .rcx), .store8 (at_ .r15 c0O) .rax] ++ ptr .rdi .r15 (c0O + 1)) s =
        some s₁ ∧
      s₁.mem = ((s.mem.writeW (W + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 56)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 48) (BitVec.ofNat 8 (15 - nl - 1)) ∧
      s₁.gpr .rsi = N ∧ s₁.gpr .rdi = W + BitVec.ofNat 64 49 ∧ s₁.gpr .rcx = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [zero16, h15, w₁, w₂, w₃, r₁, r₂, VG.Proof.AesCcm.X86_64.add_ofNat_assoc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]
      rw [hnl, VG.Proof.AesCcm.X86_64.sub_low_byte (show nl ≤ 14 by omega)]
      rfl
    · simp [gpr_setReg, hNp]
    · simp [gpr_setReg]
    · simp [gpr_setReg, hnl]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dNW : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 49, nl⟩ := hN.w.sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₁ N (W + BitVec.ofNat 64 49) nl :=
    ⟨hsi, hdi, hcx, by omega, by omega, by rw [hrd₁, hwr₁]; exact hN.rd, E₁.perm.wC (by omega), dNW⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
  have hfz : Frame [⟨W + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (d := 48) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains W (d := 56) (n := 8) (e := 48) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains W (d := 48) (n := 1) (e := 48) (k := 16) (by decide) (by decide) (by decide))
  have hNs : bytesAt s₁.mem N nl = bytesAt s.mem N nl :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame hfz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hN.w.sub_right (Lay.wSub (by decide))) (by omega)
  refine ⟨E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂, ?_, ?_,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · refine hfz.trans ?_
    rw [hm₂]
    exact writeBytes_frame _ _ _ (by
      rw [VG.Proof.AesCcm.X86_64.length_bytesAt]
      exact Offset.contains W (d := 49) (n := nl) (e := 48) (k := 16) (by decide) (by omega) (by decide))
  · -- The bytes of the block.
    have e56 : W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
    have hz : bytesAt s₁.mem (W + BitVec.ofNat 64 48) 16 = BitVec.ofNat 8 (15 - nl - 1) :: Spec.Ccm.zeros 15 := by
      rw [hm₁, VG.Proof.AesCcm.X86_64.bytesAt_writeW8_base _ _ _ (by decide) (by decide), e56, Proof.Cmac.bytesAt_store2,
        Proof.Cmac.le8_zero]
      rfl
    have hl := VG.Proof.AesCcm.X86_64.length_bytesAt s.mem N nl
    rw [hm₂, show W + BitVec.ofNat 64 49 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 1 by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc],
      VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; omega) (by decide), VG.Proof.AesCcm.X86_64.length_bytesAt, hz, hNs,
      Spec.Ccm.ctrBlock, hl, VG.Proof.AesCcm.X86_64.be_zero, show 1 + nl = nl + 1 by omega]
    simp only [Spec.Ccm.zeros, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_replicate,
      List.cons_append, List.nil_append]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Blocks`. -/
section

/-!
# AES-CCM on x86-64: counter blocks and chaining a block

Untrusted: everything here is checked by Lean. `ctrAt` makes `Ctrᵢ` at
`W + 64` from `Ctr₀` (`ctrAt_ok`); `updBlock y` chains the block `B` at
`W + 32` into the MAC state at `W + y` (`updBlock_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (upd_call)

/-! ## `ctrAt` -/

/-- `Ctrᵢ` at `W + 64`, for `i` in `rax`. -/
theorem ctrAt_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (h13 : nonce.length ≤ 13) (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) (hax : s.gpr .rax = BitVec.ofNat 64 i) :
    ∃ s', runBlock isa ctrAt s = some s' ∧ Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h15 := E.r15
  have w₁ := E.perm.wW (show 64 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 56 + 8 ≤ 2560 by decide)
  obtain ⟨s', run, hm, hg, hrd, hwr⟩ : ∃ s', runBlock isa ctrAt s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 64) (s.mem.readW (W + BitVec.ofNat 64 48) 64)).writeW
        (W + BitVec.ofNat 64 72) (bswap64 (BitVec.ofNat 64 i) ||| s.mem.readW (W + BitVec.ofNat 64 56) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by crun [ctrAt, h15, w₁, w₂, r₁, r₂], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, hax]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  have e72 : W + BitVec.ofNat 64 72 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
  have e56 : W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
  refine ⟨s', run, ?_, ?_, hg, hrd, hwr⟩
  · rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains W (d := 64) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains W (d := 72) (n := 8) (e := 64) (k := 16) (by decide) (by decide) (by decide))
  · have h8 : bytesAt s.mem (W + BitVec.ofNat 64 48) 8 = (bytesAt s.mem (W + BitVec.ofNat 64 48) 16).take 8 := by
      rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hlo : le8 (s.mem.readW (W + BitVec.ofNat 64 48) 64) = (Spec.Ccm.ctrBlock nonce i).take 8 := by
      rw [Proof.Cmac.le8_readW, h8, hc0, VG.Proof.AesCcm.X86_64.ctrBlock_take8 h7, VG.Proof.AesCcm.X86_64.ctrBlock_take8 h7]
    have hhi : le8 (s.mem.readW (W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    rw [hm, e72, Proof.Cmac.bytesAt_store2, hlo, VG.Proof.AesCcm.X86_64.ctr_or h7 h13 hhi hi, List.take_append_drop]

/-! ## Chaining `B` -/

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (updBlock v.callee v.suffix y) s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
          [bytesAt s.mem (W + BitVec.ofNat 64 32) 16] := by
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rdi = K ∧ s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₁.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s₁.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₁.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .rbp, .r12, .r14], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, VG.Proof.AesCcm.X86_64.imm_eq hy']
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hq := VG.Proof.AesCcm.X86_64.srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨W + BitVec.ofNat 64 32, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (upd_call v _ (VG.Proof.AesCcm.X86_64.uargs L E₁ hR (by omega) hq hqy (by decide) hdi hsi hdx hcx hr8 hr9))
    fun s₂ h => ⟨E₁.of_saved h.saved h.rd h.wr, fun r hr => ?_, by rw [h.rd, hrd₁], by rw [h.wr, hwr₁], ?_, ?_⟩
  · rw [h.saved r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      hg₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp)]
  · rw [← hm₁]; simpa [E₁.rsp] using h.frame
  · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
      (Proof.Cmac.bytesAt_length _ _ _), hm₁]
    rfl

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.B0`. -/
section

/-!
# AES-CCM on x86-64: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `b0 y` computes the flags
`64 [a > 0] + 4 (t − 2) + q − 1` (which is A.2.1's for an even `t`), writes
`B₀` to `W + 32` from `Ctr₀`, zeroes the MAC state at `W + y` and chains
`B₀` into it (`b0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B`, the
working space of the functions called and the stack below `SP`. -/
abbrev macR (W SP : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16]

theorem flags_val {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    ((BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega, ite_false, Nat.zero_add]; omega
  · simp only [h, ite_false, show al > 0 by omega, ite_true]; omega

/-- `B₀` in `B` and the MAC state at `W + y` zeroed. -/
theorem b0Pre_ok {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov32 .rcx (imm 14), .alu .sub .rcx (.mem (at_ .r15 nlenO)),
        .alu .add .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)])
      (.seq (.ite .e (.block []) (.block [.alu .add .rax (imm 64)]))
      (.block (([.mov .rcx (.mem (at_ .r15 c0O)), .mov .rdx (.mem (at_ .r15 (c0O + 8))),
        .mov .rsi (.mem (at_ .r15 lenO)), .store (at_ .r15 bO) .rcx, .store8 (at_ .r15 bO) .rax, .bswap .rsi,
        .alu .or .rsi (.reg .rdx), .store (at_ .r15 (bO + 8)) .rsi] : List Instr) ++ zero16 y)))) s fun s' =>
      VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
  have h15 := E.r15
  have rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have rn := E.perm.wR (show 168 + 8 ≤ 2560 by decide)
  have ra := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have htl := S.tl
  have hnl' := S.nlen
  have hal' := S.alen
  -- The flags, without `64 [a > 0]`, and ZF for `a = 0`.
  obtain ⟨s₁, run₁, hm₁, hax₁, hzf₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov32 .rcx (imm 14), .alu .sub .rcx (.mem (at_ .r15 nlenO)),
        .alu .add .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rax = BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl)) ∧
      s₁.zf = some (decide (al = 0)) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, rt, rn, ra], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, htl, hnl']
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, VG.Proof.AesCcm.X86_64.setWidth_imm]
      omega
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hal', VG.Proof.AesCcm.X86_64.and_self_beq hal]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- `64 [a > 0]`.
  have hite : WP isa (.ite .e (.block []) (.block [.alu .add .rax (imm 64)])) s₁ fun s₂ =>
      s₂.mem = s.mem ∧ s₂.gpr .rax = BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine WP.ite (decide (al = 0)) (VG.Proof.AesCcm.X86_64.eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : al = 0 := of_decide_eq_true ht
      exact WP.of_runBlock ⟨s₁, rfl, hm₁, by rw [hax₁, h0]; rfl, hg₁, hrd₁, hwr₁⟩
    · have h0 : al ≠ 0 := of_decide_eq_false hf
      refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
      · exact hm₁
      · simp only [gpr_setReg, ite_true, hax₁, h0, ite_false]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.AesCcm.X86_64.imm_eq (show 64 < 2 ^ 31 by decide)]
        omega
      · intro r a b; simp [gpr_setReg, a, hg₁ r a b]
      · exact hrd₁
      · exact hwr₁
  refine WP.seq (WP.mono hite fun s₂ ⟨hm₂, hax₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  -- `B₀`, and the state zeroed.
  have h15₂ := E₂.r15
  have hRo : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₂]; exact S.rounds
  have hlen : s₂.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by rw [hm₂]; exact S.len
  have c₁ := E₂.perm.wR (show 48 + 8 ≤ 2560 by decide)
  have c₂ := E₂.perm.wR (show 56 + 8 ≤ 2560 by decide)
  have c₃ := E₂.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have b₁ := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have b₂ := E₂.perm.wW (show 32 + 1 ≤ 2560 by decide)
  have b₃ := E₂.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have y₁ := E₂.perm.wW (show y + 8 ≤ 2560 by omega)
  have y₂ := E₂.perm.wW (show y + 8 + 8 ≤ 2560 by omega)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₃, run₃, hm₃, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      ([.mov .rcx (.mem (at_ .r15 c0O)), .mov .rdx (.mem (at_ .r15 (c0O + 8))), .mov .rsi (.mem (at_ .r15 lenO)),
        .store (at_ .r15 bO) .rcx, .store8 (at_ .r15 bO) .rax, .bswap .rsi, .alu .or .rsi (.reg .rdx),
        .store (at_ .r15 (bO + 8)) .rsi] ++ zero16 y) s₂ = some s₃ ∧
      s₃.mem = (((((s₂.mem.writeW (W + BitVec.ofNat 64 32) (s₂.mem.readW (W + BitVec.ofNat 64 48) 64)).writeW
        (W + BitVec.ofNat 64 32) ((s₂.gpr .rax).setWidth 8 : Byte)).writeW (W + BitVec.ofNat 64 40)
        (bswap64 (BitVec.ofNat 64 n) ||| s₂.mem.readW (W + BitVec.ofNat 64 56) 64)).writeW (W + BitVec.ofNat 64 y)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 (y + 8)) (0 : BitVec 64)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [zero16, h15₂, c₁, c₂, c₃, b₁, b₂, b₃, y₁, y₂, VG.Proof.AesCcm.X86_64.imm_eq hy', VG.Proof.AesCcm.X86_64.add_ofNat_assoc], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hlen,
        VG.Proof.AesCcm.X86_64.add_ofNat_assoc, VG.Proof.AesCcm.X86_64.setWidth_imm, Nat.reduceMod]
      rfl
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have E₃ : VG.Proof.AesCcm.X86_64.Env K W SP s₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide) (by decide)) hrd₃ hwr₃
  -- What the block wrote.
  have e40 : W + BitVec.ofNat 64 40 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
  have ey8 : W + BitVec.ofNat 64 (y + 8) = W + BitVec.ofNat 64 y + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 → (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  have cY : ∀ d k, y ≤ d → d + k ≤ y + 16 → (⟨W + BitVec.ofNat 64 y, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega) (by omega)
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((s₂.mem.writeW (W + BitVec.ofNat 64 32) (s₂.mem.readW (W + BitVec.ofNat 64 48) 64)).writeW
      (W + BitVec.ofNat 64 32) ((s₂.gpr .rax).setWidth 8 : Byte)).writeW (W + BitVec.ofNat 64 40)
      (bswap64 (BitVec.ofNat 64 n) ||| s₂.mem.readW (W + BitVec.ofNat 64 56) 64) := ⟨_, rfl⟩
  rw [← hmB] at hm₃
  have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₂.mem mB := by
    rw [hmB]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))
  have fY : Frame [⟨W + BitVec.ofNat 64 y, 16⟩] mB s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cY y 8 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (cY (y + 8) 8 (by omega) (by omega))
  have dYB : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have f₃ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s₃.mem := by
    rw [← hm₂]
    exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  refine ⟨E₃, by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂], f₃, ?_⟩
  constructor
  · -- The state was zeroed.
    rw [hm₃, ey8, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · -- `B₀`.
    have hB₁ : bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 = bytesAt mB (W + BitVec.ofNat 64 32) 16 :=
      VG.Proof.AesCcm.X86_64.bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB) (by decide)
    have hlo : le8 (s₂.mem.readW (W + BitVec.ofNat 64 48) 64) =
        BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
      have h8 : bytesAt s₂.mem (W + BitVec.ofNat 64 48) 8 = (bytesAt s₂.mem (W + BitVec.ofNat 64 48) 16).take 8 := by
        rw [Proof.Cmac.bytesAt_split, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rw [Proof.Cmac.le8_readW, h8, hm₂, hc0, VG.Proof.AesCcm.X86_64.ctrBlock_take8 (by omega)]
    have hhi : le8 (s₂.mem.readW (W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
      have e56 : W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
      rw [Proof.Cmac.le8_readW, ← hc0, hm₂, Proof.Cmac.bytesAt_split, e56,
        List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have hb : ((s₂.gpr .rax).setWidth 8 : Byte) = Spec.Ccm.flags tl (15 - nonce.length) al := by
      rw [hax₂, hnl, VG.Proof.AesCcm.X86_64.flags_val ht4 ht16 hte h7 h13]
    have hB : bytesAt mB (W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
      rw [hmB, e40, VG.Proof.AesCcm.X86_64.bytesAt_writeW64_at _ _ _ (by decide) (by decide), VG.Proof.AesCcm.X86_64.bytesAt_writeW8_base _ _ _ (by decide)
        (by decide), VG.Proof.AesCcm.X86_64.bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hb,
        VG.Proof.AesCcm.X86_64.ctr_or (by omega) (by omega) hhi (by rw [hnl]; exact hn), VG.Proof.AesCcm.X86_64.ctrBlock_drop8 (by omega)]
      simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons]
      have hX : (Spec.Ccm.flags tl (15 - nonce.length) al ::
          (List.take 7 nonce ++ List.drop 8 (bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16))).length ≤ 8 + 8 := by
        simp [VG.Proof.AesCcm.X86_64.length_bytesAt]; omega
      rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega),
        List.drop_eq_nil_of_le hX, List.append_nil, ← List.append_assoc, List.take_append_drop]
    rw [hB₁, hB]

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee v.suffix y) s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ Frame (VG.Proof.AesCcm.X86_64.macR W SP y) s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n] ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine VG.Proof.AesCcm.X86_64.seq_assoc3 (WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.b0Pre_ok L E S hnl h7 h13 ht4 ht16 hte hal hn hc0 hy)
    fun s₃ ⟨E₃, rd₃, wr₃, f₃, hz, hB⟩ => ?_))
  have hRo₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by omega)) (by decide) (by omega)) (by decide)]
    exact S.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.X86_64.updBlock_ok v L E₃ hR hRo₃ hy) fun s₄ ⟨E₄, _, hrd₄, hwr₄, f₄, h₄⟩ =>
    ⟨E₄, ?_, ?_, by rw [hrd₄, rd₃], by rw [hwr₄, wr₃]⟩
  · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₄, hz, hB, VG.Proof.AesCcm.X86_64.ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Lay.wSub (by omega))) hRb]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Absorb`. -/
section

/-!
# AES-CCM on x86-64: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P`, padded with zeros to whole blocks, into the MAC state
at `W + y`: its whole blocks in one call of `vg_cmac_aes_update`
(`absorbWhole_ok`), then its last `len mod 16` bytes copied into the zeroed
block `B` (`absorbTail_ok`); together, the blocks of the padded string
(`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (upd_call)

theorem sub_mac {W SP : Addr} {y : Nat} {r : Region} (hr : r ∈ VG.Proof.AesCcm.X86_64.macR W SP y) :
    ∃ r' ∈ VG.Proof.AesCcm.X86_64.macR W SP y, Region.Sub r r' := ⟨r, hr, fun _ h => h⟩

/-- What `absorbPad`'s pieces keep: the environment, the registers holding
the string, and what they write. -/
structure Absorbed {K W SP : Addr} (s : State) (y : Nat) (P : Addr) (len : Nat) (Y : List Byte) (s' : State) :
    Prop where
  env : VG.Proof.AesCcm.X86_64.Env K W SP s'
  r12 : s'.gpr .r12 = P
  rbp : s'.gpr .rbp = BitVec.ofNat 64 len
  frame : Frame (VG.Proof.AesCcm.X86_64.macR W SP y) s.mem s'.mem
  out : bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The whole blocks of the string. -/
theorem absorbWhole_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (.seq (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)])
        (.ite .e (.block []) (.seq (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) (callUpdate v.callee v.suffix))))
      s (@VG.Proof.AesCcm.X86_64.Absorbed K W SP s y P len
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 ((bytesAt s.mem P len).take (16 * (len / 16)))))) := by
  have hl := hP.lt
  obtain ⟨s₁, run₁, hm₁, hr8, hzf, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ s₁.zf = some (decide (len / 16 = 0)) ∧
      (∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hbp, VG.Proof.AesCcm.X86_64.shr4 len hl]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hbp, VG.Proof.AesCcm.X86_64.shr4 len hl, VG.Proof.AesCcm.X86_64.and_self_beq (show len / 16 < 2 ^ 64 by omega)]
    · intro r a; simp [gpr_setReg, gpr_setFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (len / 16 = 0)) (VG.Proof.AesCcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len / 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hg₁ _ (by decide), h12], by rw [hg₁ _ (by decide), hbp],
      by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    rw [hm₁, h0, Nat.mul_zero, List.take_zero]; rfl
  · have h0 : len / 16 ≠ 0 := of_decide_eq_false hf
    have h15 := E₁.r15
    have h13 := E₁.r13
    have r₁ := E₁.perm.wR (show 232 + 8 ≤ 2560 by decide)
    have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₁]; exact hRo
    have hy' : y < 2 ^ 31 := by omega
    obtain ⟨s₂, run₂, hm₂, hdi, hsi, hdx, hcx, hr8₂, hr9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (updArgs y ++ [.mov .rcx (.reg .r12)]) s₁ = some s₂ ∧ s₂.mem = s₁.mem ∧
        s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 y ∧
        s₂.gpr .rcx = P ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 384 ∧
        (∀ r ∈ [Reg.r12, .rbp, .r13, .r15, .rsp], s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · simp [gpr_setReg, h13]
      · simp [gpr_setReg, hRo₁]
      · simp [gpr_setReg, h15, VG.Proof.AesCcm.X86_64.imm_eq hy']
      · simp [gpr_setReg, hg₁ _ (by decide : Reg.r12 ≠ .r8), h12]
      · simp [gpr_setReg, hr8]
      · simp [gpr_setReg, h15]
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
      all_goals rfl
    have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by simp)) hrd₂ hwr₂
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
    have hq := VG.Proof.AesCcm.X86_64.srcBuf ((hP.take hb).of_eq (s' := s₂) (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁]))
    have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ :=
      (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega))
    refine WP.mono (upd_call v _ (VG.Proof.AesCcm.X86_64.uargs L E₂ hR (by omega) hq hqy (by omega) hdi hsi hdx hcx hr8₂ hr9))
      fun s₃ h => ⟨E₂.of_saved h.saved h.rd h.wr, ?_, ?_, ?_, ?_, by rw [h.rd, hrd₂, hrd₁], by rw [h.wr, hwr₂, hwr₁]⟩
    · rw [h.saved _ (by decide), hg₂ _ (by simp), hg₁ _ (by decide), h12]
    · rw [h.saved _ (by decide), hg₂ _ (by simp), hg₁ _ (by decide), hbp]
    · rw [← hm₁, ← hm₂]
      exact h.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact VG.Proof.AesCcm.X86_64.sub_mac (by simp)
        · exact VG.Proof.AesCcm.X86_64.sub_mac (by simp)
        · exact ⟨below SP 16, by simp, by rw [E₂.rsp]; exact fun _ h => h⟩
    · rw [h.out, Proof.Cmac.Stream.blocksAt_eq, hm₂, hm₁, ← VG.Proof.AesCcm.X86_64.bytesAt_prefix _ _ hb]
      rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- The last bytes of the string, padded with zeros in `B`. -/
theorem absorbTail_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (.seq (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block [])
          (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
              ptr .rdi .r15 bO))
            (.seq copyLoop (updBlock v.callee v.suffix y)))))
      s (@VG.Proof.AesCcm.X86_64.Absorbed K W SP s y P len
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
          (VG.Proof.AesCcm.X86_64.tailBlocks (bytesAt s.mem P len)))) := by
  have hl := hP.lt
  have hxl := VG.Proof.AesCcm.X86_64.length_bytesAt s.mem P len
  obtain ⟨s₁, run₁, hm₁, hcx, hzf, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ s₁.zf = some (decide (len % 16 = 0)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hbp, VG.Proof.AesCcm.X86_64.and15', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hl]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, hbp, VG.Proof.AesCcm.X86_64.and15', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hl,
        VG.Proof.AesCcm.X86_64.and_self_beq (show len % 16 < 2 ^ 64 by omega)]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (len % 16 = 0)) (VG.Proof.AesCcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hg₁ _ (by decide), h12], by rw [hg₁ _ (by decide), hbp],
      by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    simp only [hm₁, VG.Proof.AesCcm.X86_64.tailBlocks, hxl, h0, ↓reduceIte]; rfl
  · have h0 : len % 16 ≠ 0 := of_decide_eq_false hf
    have h15 := E₁.r15
    have w₁ := E₁.perm.wW (show 32 + 8 ≤ 2560 by decide)
    have w₂ := E₁.perm.wW (show 40 + 8 ≤ 2560 by decide)
    obtain ⟨s₂, run₂, hm₂, hsi, hdi, hcx₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
          ptr .rdi .r15 bO) s₁ = some s₂ ∧
        s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 40)
          (0 : BitVec 64) ∧
        s₂.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) ∧ s₂.gpr .rdi = W + BitVec.ofNat 64 32 ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧
        (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by crun [zero16, h15, w₁, w₂, VG.Proof.AesCcm.X86_64.add_ofNat_assoc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [mem_setReg, mem_arithFlags]; rfl
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hg₁ _ (by decide : Reg.rbp ≠ .rcx),
          hg₁ _ (by decide : Reg.r12 ≠ .rcx), hbp, h12, hcx]
        rw [VG.Proof.AesCcm.X86_64.ofNat_sub (by omega) hl, BitVec.add_comm, show len - len % 16 = 16 * (len / 16) by omega]
      · simp [gpr_setReg, h15]
      · simp [gpr_setReg, hcx]
      · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
    have hb : 16 * (len / 16) + len % 16 = len := by omega
    have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega)).of_eq (s' := s₂)
      (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁])
    have dTB : (⟨P + BitVec.ofNat 64 (16 * (len / 16)), len % 16⟩ : Region).Disjoint
        ⟨W + BitVec.ofNat 64 32, len % 16⟩ := hT.w.sub_right (Lay.wSub (by omega))
    have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (W + BitVec.ofNat 64 32) (len % 16) :=
      ⟨hsi, hdi, hcx₂, by omega, by omega, hT.rd, E₂.perm.wC (by omega), dTB⟩
    refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_)
    have E₃ : VG.Proof.AesCcm.X86_64.Env K W SP s₃ := E₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
    -- What was written.
    have e40 : W + BitVec.ofNat 64 40 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
    have fZ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₁.mem s₂.mem := by
      rw [hm₂]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 32) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 40) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))
    have fC : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₂.mem s₃.mem := by
      rw [hm₃]
      exact writeBytes_frame _ _ _ (by
        rw [VG.Proof.AesCcm.X86_64.length_bytesAt]
        exact Offset.contains W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide))
    have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem := by rw [← hm₁]; exact fZ.trans fC
    have dK : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], (⟨K, 240⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))
    have hRo₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
      rw [fB.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)]
      exact hRo
    have hY₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (W + BitVec.ofNat 64 y) 16 :=
      VG.Proof.AesCcm.X86_64.bytesAt_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    have hB₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem P len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
      have hs₁ : bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
          (bytesAt s.mem P len).drop (16 * (len / 16)) := by
        rw [VG.Proof.AesCcm.X86_64.bytesAt_frame fZ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hT.w.sub_right (Lay.wSub (by decide))) (by omega),
          hm₁, show len % 16 = len - 16 * (len / 16) by omega, VG.Proof.AesCcm.X86_64.bytesAt_suffix _ _ (by omega)]
      have hz : bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
        rw [hm₂, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
      rw [hm₃, VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; omega) (by decide), hs₁, hz,
        List.length_drop, hxl]
      congr 1
      simp only [Spec.Cmac.zeros, Spec.Ccm.zeros, List.drop_replicate]
      congr 1
      omega
    have rw₄ : ∀ s₄ : State, s₄.rd = s₃.rd → s₄.wr = s₃.wr → s₄.rd = s.rd ∧ s₄.wr = s.wr := fun s₄ a b =>
      ⟨by rw [a, hrd₃, hrd₂, hrd₁], by rw [b, hwr₃, hwr₂, hwr₁]⟩
    refine WP.mono (VG.Proof.AesCcm.X86_64.updBlock_ok v L E₃ hR hRo₃ hy) fun s₄ ⟨E₄, g₄, hr₄, hw₄, f₄, h₄⟩ =>
      ⟨E₄, ?_, ?_, ?_, ?_, (rw₄ s₄ hr₄ hw₄).1, (rw₄ s₄ hr₄ hw₄).2⟩
    · rw [g₄ _ (by simp), hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide),
        hg₁ _ (by decide), h12]
    · rw [g₄ _ (by simp), hg₃ _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide),
        hg₁ _ (by decide), hbp]
    · refine ((fB.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
      · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.X86_64.sub_mac (by simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesCcm.X86_64.sub_mac (by simp)
    · have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
      rw [h₄, hY₃, hB₃, VG.Proof.AesCcm.X86_64.ctxCiph_frame fB dK hRb]
      simp only [VG.Proof.AesCcm.X86_64.tailBlocks, hxl, h0, ↓reduceIte]

/-- Keeps `[232, 240)`, where the rounds are. -/
theorem rounds_kept {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (hf : Frame (VG.Proof.AesCcm.X86_64.macR W SP y) m m') : m'.readW (W + BitVec.ofNat 64 232) 64 = m.readW (W + BitVec.ofNat 64 232) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide)

/-- A buffer missing `W` and the stack below `SP` keeps its bytes. -/
theorem buf_kept {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.X86_64.macR W SP y) m m') : bytesAt m' P len = bytesAt m P len :=
  VG.Proof.AesCcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem k_macR {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {y : Nat} (hy : y + 16 ≤ 2560) :
    ∀ r ∈ VG.Proof.AesCcm.X86_64.macR W SP y, (⟨K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Lay.wSub hy)
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len) :
    WP isa (absorbPad v.callee v.suffix y) s (@VG.Proof.AesCcm.X86_64.Absorbed K W SP s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem P len))))) := by
  refine VG.Proof.AesCcm.X86_64.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.absorbWhole_ok v L E hR hRo hy hP h12 hbp) fun s₁ A₁ => ?_))
  have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [VG.Proof.AesCcm.X86_64.rounds_kept L hy A₁.frame, hRo]
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.X86_64.absorbTail_ok v L A₁.env hR hRo₁ hy (hP.of_eq A₁.rd A₁.wr) A₁.r12 A₁.rbp) fun s₂ A₂ =>
    ⟨A₂.env, A₂.r12, A₂.rbp, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  rw [A₂.out, A₁.out, VG.Proof.AesCcm.X86_64.buf_kept hP (by omega) A₁.frame, VG.Proof.AesCcm.X86_64.ctxCiph_frame A₁.frame (VG.Proof.AesCcm.X86_64.k_macR L (by omega)) hRb,
    ← Proof.Cmac.chain_append, Proof.AesCcm.blocks_pad16, VG.Proof.AesCcm.X86_64.length_bytesAt, VG.Proof.AesCcm.X86_64.tailBlocks, VG.Proof.AesCcm.X86_64.length_bytesAt]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Header`. -/
section

/-!
# AES-CCM on x86-64: the encoding of the length of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a > 0` (A.2.2) at its start: `[a]₁₆`,
`0xff ‖ 0xfe ‖ [a]₃₂` or `0xff ‖ 0xff ‖ [a]₆₄`, by byte-swapping and
shifting `a` (`header_ok`); its length is in `rbx`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr minLen)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)

/-- A right shift by whole bytes drops the low bytes. -/
theorem le8_ushiftRight (x : BitVec 64) {k : Nat} (hk : k ≤ 8) :
    le8 (x >>> (8 * k)) = (le8 x).drop k ++ Spec.Ccm.zeros k := by
  have hl : ((le8 x).drop k).length = 8 - k := by rw [List.length_drop, Proof.Cmac.length_le8]
  have hlen : (le8 (x >>> (8 * k))).length = ((le8 x).drop k ++ Spec.Ccm.zeros k).length := by
    rw [Proof.Cmac.length_le8, List.length_append, hl, Spec.Ccm.zeros, List.length_replicate]
    omega
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have hi : i < 8 := by rwa [Proof.Cmac.length_le8] at h₁
  by_cases h : i < 8 - k
  · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_drop]
    simp only [le8, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [show 8 * k + 8 * i = 8 * (k + i) by omega]
  · rw [List.getElem_append_right (by rw [hl]; omega)]
    simp only [Spec.Ccm.zeros, List.getElem_replicate, le8, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

theorem le8_ffff : le8 (BitVec.ofNat 64 0xffff) = [0xff, 0xff] ++ Spec.Ccm.zeros 6 := by decide
theorem le8_feff : le8 (BitVec.ofNat 64 0xfeff) = [0xff, 0xfe] ++ Spec.Ccm.zeros 6 := by decide

theorem encodeLen_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) : Spec.Ccm.encodeLen a = Spec.Ccm.be 2 a := by
  simp [Spec.Ccm.encodeLen, h]

theorem encodeLen_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xfe] ++ Spec.Ccm.be 4 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem encodeLen_hi {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : ¬ a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xff] ++ Spec.Ccm.be 8 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem minLen_ok (s : State) {o n : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 o)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (ho : o ≤ 16) (hn : n < 2 ^ 64) :
    WP isa minLen s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (imm 16), .alu .sub .rcx (.reg .rbx),
      .alu .cmp .rbp (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (16 - o) ∧ s₁.cf = some (decide (n < 16 - o)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hbx, VG.Proof.AesCcm.X86_64.ofNat_sub ho (by decide)]
    · simp only [cf_arithFlags, hbp, hbx, VG.Proof.AesCcm.X86_64.setWidth_imm, VG.Proof.AesCcm.X86_64.ofNat_sub ho (by decide),
        VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hn, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show 16 - o < 2 ^ 64 by omega),
        show (16 : Nat) % 2 ^ 32 = 16 from rfl, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals rfl
  obtain ⟨hcx, hcf, hg, hm, hrd, hwr⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - o)) (VG.Proof.AesCcm.X86_64.eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · have h := of_decide_eq_true ht
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg .rbp (by decide), hbp, Nat.min_eq_right (Nat.le_of_lt h)]
    · intro r hr; simp [gpr_setReg, hr, hg r hr]
    all_goals first | exact hm | exact hrd | exact hwr
  · have h := of_decide_eq_false hf
    refine WP.of_runBlock ⟨s₁, rfl, ?_, hg, hm, hrd, hwr⟩
    rw [hcx, Nat.min_eq_left (by omega)]

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`rbp`) at its start, and its length in `rbx`. -/
theorem header_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {a : Nat} (ha0 : 0 < a)
    (ha : a < 2 ^ 64) (hbp : s.gpr .rbp = BitVec.ofNat 64 a) :
    WP isa header s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.gpr .rbx = BitVec.ofNat 64 (Proof.AesCcm.hdrLen a) ∧
      (∀ r ∈ [Reg.rbp, .r12, .r14], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - Proof.AesCcm.hdrLen a) := by
  have h15 := E.r15
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  have w₃ := E.perm.wW (show 34 + 8 ≤ 2560 by decide)
  have e40 : W + BitVec.ofNat 64 40 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
  have e34 : W + BitVec.ofNat 64 34 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 → (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  -- `B` zeroed; CF for `a < 2¹⁶ − 2⁸`.
  obtain ⟨s₁, run₁, hm₁, hcf₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (zero16 bO ++ [.mov32 .rax (imm 0xff00), .alu .cmp .rbp (.reg .rax)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧ s₁.cf = some (decide (a < 2 ^ 16 - 2 ^ 8)) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [zero16, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]; rfl
    · simp only [cf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt ha,
        BitVec.toNat_ofNat]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals rfl
  have hz : bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [hm₁, e40, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  have fz : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64) (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (cB 40 8 (by decide) (by decide))
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₁ _ (by decide), hbp]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ha64 := VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt ha
  refine WP.ite (decide (a < 2 ^ 16 - 2 ^ 8)) (VG.Proof.AesCcm.X86_64.eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
  · -- `[a]₁₆`.
    have h₁ := of_decide_eq_true ht
    have w₁' := E₁.perm.wW (show 32 + 8 ≤ 2560 by decide)
    refine WP.of_runBlock ⟨_, by crun [E₁.r15, w₁'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact E₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]) rfl rfl
    · simp [gpr_setReg, Proof.AesCcm.hdrLen, h₁]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags, hg₁ _ (by decide : Reg.r12 ≠ .rax),
        hg₁ _ (by decide : Reg.r14 ≠ .rax), hg₁ _ (by decide : Reg.rbp ≠ .rax)]
    · exact hrd₁
    · exact hwr₁
    · simp only [mem_setReg]
      exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp₁]
      rw [VG.Proof.AesCcm.X86_64.bytesAt_writeW64_base _ _ _ (by decide) (by decide), hz,
        show (48 : Nat) = 8 * 6 from rfl, VG.Proof.AesCcm.X86_64.le8_ushiftRight _ (by decide), VG.Proof.AesCcm.X86_64.le8_bswap64_ofNat ha,
        VG.Proof.AesCcm.X86_64.be_split (q := 2) (by decide) (by omega), VG.Proof.AesCcm.X86_64.encodeLen_lo h₁, show Proof.AesCcm.hdrLen a = 2 by
          simp [Proof.AesCcm.hdrLen, h₁]]
      simp [Spec.Ccm.zeros, List.drop_append_of_le_length, Proof.AesCcm.length_be]
  · have h₁ := of_decide_eq_false hf
    obtain ⟨s₂, run₂, hcf₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        [.movImm64 .rax 0x100000000, .alu .cmp .rbp (.reg .rax)] s₁ = some s₂ ∧
        s₂.cf = some (decide (a < 2 ^ 32)) ∧ (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
        s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [cf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp₁, ha64]; rfl
      · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
    have hbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₂ _ (by decide), hbp₁]
    refine WP.ite (decide (a < 2 ^ 32)) (VG.Proof.AesCcm.X86_64.eval_b hcf₂) (fun ht => ?_) (fun hf => ?_)
    · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
      have h₂ := of_decide_eq_true ht
      have w₁' := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
      refine WP.of_runBlock ⟨_, by crun [E₂.r15, w₁'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact E₂.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]) rfl rfl
      · simp [gpr_setReg, gpr_arithFlags, Proof.AesCcm.hdrLen, h₁, h₂]
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hg₂ _ (by decide : Reg.r12 ≠ .rax),
          hg₂ _ (by decide : Reg.r14 ≠ .rax), hg₂ _ (by decide : Reg.rbp ≠ .rax),
          hg₁ _ (by decide : Reg.r12 ≠ .rax), hg₁ _ (by decide : Reg.r14 ≠ .rax), hg₁ _ (by decide : Reg.rbp ≠ .rax)]
      · simp only [rd_setReg, rd_arithFlags]; rw [hrd₂, hrd₁]
      · simp only [wr_setReg, wr_arithFlags]; rw [hwr₂, hwr₁]
      · simp only [mem_setReg, mem_arithFlags, hm₂]
        exact fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))
      · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂, hm₂]
        rw [VG.Proof.AesCcm.X86_64.bytesAt_writeW64_base _ _ _ (by decide) (by decide), hz,
          show (65279#64 : BitVec 64) = BitVec.ofNat 64 0xfeff from rfl, VG.Proof.AesCcm.X86_64.le8_or,
          show bswap64 (BitVec.ofNat 64 a) >>> 16 = bswap64 (BitVec.ofNat 64 a) >>> (8 * 2) from rfl,
          VG.Proof.AesCcm.X86_64.le8_ushiftRight _ (by decide), VG.Proof.AesCcm.X86_64.le8_bswap64_ofNat ha, VG.Proof.AesCcm.X86_64.be_split (q := 4) (by decide) (by omega),
          VG.Proof.AesCcm.X86_64.encodeLen_mid h₁ h₂, VG.Proof.AesCcm.X86_64.le8_feff, show Proof.AesCcm.hdrLen a = 6 by simp [Proof.AesCcm.hdrLen, h₁, h₂]]
        have hl4 := Proof.AesCcm.length_be 4 a
        rcases hb : Spec.Ccm.be 4 a with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
          rw [hb] at hl4 <;> simp at hl4
        simp [Spec.Ccm.zeros, List.replicate]

    · -- `0xff ‖ 0xff ‖ [a]₆₄`.
      have h₂ := of_decide_eq_false hf
      have w₁' := E₂.perm.wW (show 32 + 8 ≤ 2560 by decide)
      have w₃' := E₂.perm.wW (show 34 + 8 ≤ 2560 by decide)
      refine WP.of_runBlock ⟨_, by crun [E₂.r15, w₁', w₃'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact E₂.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl
      · simp [gpr_setReg, Proof.AesCcm.hdrLen, h₁, h₂]
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, hg₂ _ (by decide : Reg.r12 ≠ .rax),
          hg₂ _ (by decide : Reg.r14 ≠ .rax), hg₂ _ (by decide : Reg.rbp ≠ .rax),
          hg₁ _ (by decide : Reg.r12 ≠ .rax), hg₁ _ (by decide : Reg.r14 ≠ .rax), hg₁ _ (by decide : Reg.rbp ≠ .rax)]
      · simp only [rd_setReg]; rw [hrd₂, hrd₁]
      · simp only [wr_setReg]; rw [hwr₂, hwr₁]
      · simp only [mem_setReg, hm₂]
        exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
          (List.mem_singleton_self _) _ (cB 34 8 (by decide) (by decide))
      · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbp₂, hm₂]
        rw [e34, VG.Proof.AesCcm.X86_64.bytesAt_writeW64_at _ _ _ (by decide) (by decide), VG.Proof.AesCcm.X86_64.bytesAt_writeW64_base _ _ _ (by decide)
          (by decide), hz, show (65535#64 : BitVec 64) = BitVec.ofNat 64 0xffff from rfl, VG.Proof.AesCcm.X86_64.le8_ffff,
          VG.Proof.AesCcm.X86_64.le8_bswap64_ofNat ha, VG.Proof.AesCcm.X86_64.encodeLen_hi h₁ h₂, show Proof.AesCcm.hdrLen a = 10 by
            simp [Proof.AesCcm.hdrLen, h₁, h₂]]
        simp [Spec.Ccm.zeros, List.replicate]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Aad`. -/
section

/-!
# AES-CCM on x86-64: the associated data (`aadHead y`, `aad y`)

Untrusted: everything here is checked by Lean. `aadHead y` writes the
encoding of the length `a` of the associated data to `B`, copies its first
`min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`); `aad y`
does that and chains the rest of the associated data, padded, if there is
any associated data (`aad_ok`): the blocks `Proof.AesCcm.adataBlocks`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop minLen)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks)

/-- The encoding of the length of the associated data and its first bytes in `B`. -/
theorem aadHeadPre_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s)
    {A : Addr} {a : Nat} (hA : VG.Proof.AesCcm.X86_64.Buf K W SP s A a) (ha0 : 0 < a)
    (h12 : s.gpr .r12 = A) (hbp : s.gpr .rbp = BitVec.ofNat 64 a) :
    WP isa (.seq header (.seq minLen (.seq (.block [.mov .rsi (.reg .r12), .mov .rdi (.reg .r15),
        .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm bO), .alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)])
        copyLoop))) s fun s₄ =>
      VG.Proof.AesCcm.X86_64.Env K W SP s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem ∧
      s₄.gpr .r12 = A + BitVec.ofNat 64 (headLen a) ∧ s₄.gpr .rbp = BitVec.ofNat 64 (a - headLen a) ∧
      bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a)) := by
  have ha := hA.lt
  have hh := Proof.AesCcm.hdrLen_le a
  have hh2 : 2 ≤ hdrLen a := by unfold hdrLen; split <;> [omega; split <;> omega]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.header_ok E ha0 ha hbp) fun s₁ ⟨E₁, hbx₁, hg₁, hrd₁, hwr₁, f₁, hB₁⟩ => ?_)
  have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₁ _ (by simp), hbp]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.minLen_ok s₁ hbx₁ hbp₁ (by omega) ha) fun s₂ ⟨hcx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = headLen a := by unfold headLen; omega
  rw [hn1] at hcx₂
  have hn1' : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  have h15 := E₂.r15
  obtain ⟨s₃, run₃, hm₃, hsi, hdi, hcx₃, h12₃, hbp₃, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .rsi (.reg .r12), .mov .rdi (.reg .r15), .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm bO),
        .alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)] s₂ = some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .rsi = A ∧ s₃.gpr .rdi = W + BitVec.ofNat 64 (32 + hdrLen a) ∧
      s₃.gpr .rcx = BitVec.ofNat 64 (headLen a) ∧ s₃.gpr .r12 = A + BitVec.ofNat 64 (headLen a) ∧
      s₃.gpr .rbp = BitVec.ofNat 64 (a - headLen a) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .r14], s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have h12₂ : s₂.gpr .r12 = A := by rw [hg₂ _ (by decide), hg₁ _ (by simp), h12]
    have hbx₂ : s₂.gpr .rbx = BitVec.ofNat 64 (hdrLen a) := by rw [hg₂ _ (by decide), hbx₁]
    have hbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 a := by rw [hg₂ _ (by decide), hbp₁]
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, gpr_arithFlags, h12₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, hbx₂]
      rw [BitVec.add_assoc, show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, VG.Proof.AesCcm.X86_64.ofNat_add_ofNat,
        Nat.add_comm (hdrLen a) 32]
    · simp [gpr_setReg, gpr_arithFlags, hcx₂]
    · simp [gpr_setReg, gpr_arithFlags, h12₂, hcx₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂, hcx₂]
      exact VG.Proof.AesCcm.X86_64.ofNat_sub hn1'.2.1 ha
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.X86_64.Env K W SP s₃ := E₂.keep (fun r hr => hg₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₃ hwr₃
  have hA₃ := hA.of_eq (s' := s₃) (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])
  have dAB : (⟨A, headLen a⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (32 + hdrLen a), headLen a⟩ :=
    (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₃ A (W + BitVec.ofNat 64 (32 + hdrLen a)) (headLen a) :=
    ⟨hsi, hdi, hcx₃, hn1'.1, by omega, (hA₃.take hn1'.2.1).rd, E₃.perm.wC (by omega), dAB⟩
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  have E₄ : VG.Proof.AesCcm.X86_64.Env K W SP s₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)) hrd₄ hwr₄
  -- What was written.
  have fC : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact writeBytes_frame _ _ _ (by
      rw [VG.Proof.AesCcm.X86_64.length_bytesAt]
      exact Offset.contains W (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← hm₂] at f₁; rw [← hm₃] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem A (headLen a) = (bytesAt s.mem A a).take (headLen a) := by
    rw [hm₃, hm₂, VG.Proof.AesCcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right
        (Lay.wSub (by decide))) (by omega), VG.Proof.AesCcm.X86_64.bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem A a).take (headLen a)).length = headLen a := by
      rw [List.length_take, VG.Proof.AesCcm.X86_64.length_bytesAt]; omega
    rw [hm₄, show W + BitVec.ofNat 64 (32 + hdrLen a) = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by
        rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc], VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; omega) (by decide),
      VG.Proof.AesCcm.X86_64.length_bytesAt, hAk, hm₃, hm₂, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega)
  exact ⟨E₄, by rw [hrd₄, hrd₃, hrd₂, hrd₁], by rw [hwr₄, hwr₃, hwr₂, hwr₁], fB,
    by rw [hg₄ _ (by decide) (by decide), h12₃], by rw [hg₄ _ (by decide) (by decide), hbp₃], hB₄⟩

/-- The first block of the associated data. -/
theorem aadHead_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : Addr} {a : Nat} (hA : VG.Proof.AesCcm.X86_64.Buf K W SP s A a) (ha0 : 0 < a)
    (h12 : s.gpr .r12 = A) (hbp : s.gpr .rbp = BitVec.ofNat 64 a) :
    WP isa (aadHead v.callee v.suffix y) s (@VG.Proof.AesCcm.X86_64.Absorbed K W SP s y (A + BitVec.ofNat 64 (headLen a)) (a - headLen a)
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a))])) := by
  refine VG.Proof.AesCcm.X86_64.seq_assoc4 (WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.aadHeadPre_ok E hA ha0 h12 hbp)
    fun s₄ ⟨E₄, hrd₄, hwr₄, fB, h12₄, hbp₄, hB₄⟩ => ?_))
  have hRo₄ : s₄.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fB.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)]
    exact hRo
  have hY₄ : bytesAt s₄.mem (W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (W + BitVec.ofNat 64 y) 16 :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  have dK : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], (⟨K, 240⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.AesCcm.X86_64.updBlock_ok v L E₄ hR hRo₄ hy) fun s₅ ⟨E₅, g₅, hr₅, hw₅, f₅, h₅⟩ =>
    ⟨E₅, ?_, ?_, (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_), ?_, ?_, ?_⟩
  · rw [g₅ _ (by simp), h12₄]
  · rw [g₅ _ (by simp), hbp₄]
  · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesCcm.X86_64.sub_mac (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesCcm.X86_64.sub_mac (by simp)
  · rw [h₅, hY₄, hB₄, VG.Proof.AesCcm.X86_64.ctxCiph_frame fB dK hRb]
  · rw [hr₅, hrd₄]
  · rw [hw₅, hwr₄]

/-- What a piece of the MAC leaves: the environment, what it writes, the
MAC state `Y` at `W + y`, and the permissions. -/
structure MacStep {K W SP : Addr} (s : State) (y : Nat) (Y : List Byte) (s' : State) : Prop where
  env : VG.Proof.AesCcm.X86_64.Env K W SP s'
  frame : Frame (VG.Proof.AesCcm.X86_64.macR W SP y) s.mem s'.mem
  out : bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The associated data, formatted and chained. -/
theorem aad_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : y = 0 ∨ y = 96) (hA : VG.Proof.AesCcm.X86_64.Buf K W SP s A al) :
    WP isa (aad v.callee v.suffix y) s (@VG.Proof.AesCcm.X86_64.MacStep K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem (W + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem A al)))) := by
  have h15 := E.r15
  have ha := hA.lt
  have r₁ := E.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hAp := S.aad
  have hal := S.alen
  obtain ⟨s₁, run₁, hm₁, h12, hbp, hzf, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .alu .test .rbp (.reg .rbp)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.zf = some (decide (al = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, gpr_arithFlags, hAp]
    · simp [gpr_setReg, gpr_arithFlags, hal]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hal, VG.Proof.AesCcm.X86_64.and_self_beq ha]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep hg₁ hrd₁ hwr₁
  have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₁]; exact S.rounds
  have hA₁ := hA.of_eq hrd₁ hwr₁
  refine WP.ite (decide (al = 0)) (VG.Proof.AesCcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    simp only [hm₁, adataBlocks, VG.Proof.AesCcm.X86_64.length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : al ≠ 0 := of_decide_eq_false hf
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.aadHead_ok v L E₁ hR hRo₁ hy hA₁ (by omega) h12 hbp) fun s₂ A₂ => ?_)
    have hn1 : headLen al ≤ al := by unfold headLen; omega
    have hRo₂ : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
      rw [VG.Proof.AesCcm.X86_64.rounds_kept L hy A₂.frame, hRo₁]
    have hT := (hA.drop hn1).of_eq (s' := s₂) (by rw [A₂.rd, hrd₁]) (by rw [A₂.wr, hwr₁])
    refine WP.mono (VG.Proof.AesCcm.X86_64.absorbPad_ok v L A₂.env hR hRo₂ hy hT A₂.r12 A₂.rbp) fun s₃ A₃ =>
      ⟨A₃.env, by rw [← hm₁]; exact A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd, hrd₁], by rw [A₃.wr, A₂.wr, hwr₁]⟩
    rw [A₃.out, A₂.out, VG.Proof.AesCcm.X86_64.buf_kept hT (by omega) A₂.frame, VG.Proof.AesCcm.X86_64.ctxCiph_frame A₂.frame (VG.Proof.AesCcm.X86_64.k_macR L (by omega)) hRb,
      VG.Proof.AesCcm.X86_64.bytesAt_suffix _ _ hn1, hm₁, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, VG.Proof.AesCcm.X86_64.length_bytesAt, h0, ↓reduceIte]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Entry`. -/
section

/-!
# AES-CCM on x86-64: the entry and the exit (`entry`, `restore`)

Untrusted: everything here is checked by Lean. `entry` reads the stack
arguments but `tag`, saves our caller's registers at `W + 112` and keeps the arguments
in `W` (`entry_ok`); `restore` reads the registers back (`restore_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)

/-- Our caller's registers, saved at `W + 112`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The save area and the slots, which `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 112, 128⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {s : State} (P : VG.Proof.AesCcm.X86_64.Perm K W s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (hsp : s.gpr .rsp = SP) (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr))
    (hargsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    ∃ s₁, runBlock isa VG.Impl.AesCcm.X86_64.entry s = some s₁ ∧ VG.Proof.AesCcm.X86_64.Env K W SP s₁ ∧ VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s₁.mem ∧
      VG.Proof.AesCcm.X86_64.Saved s₁.mem W s.gpr ∧ Frame [VG.Proof.AesCcm.X86_64.entryR W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₈ := VG.Proof.AesCcm.X86_64.in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₁₆ := VG.Proof.AesCcm.X86_64.in_off (d := 8) (n := 8) hargs (by decide) (by decide)
  have a₃₂ := VG.Proof.AesCcm.X86_64.in_off (d := 24) (n := 8) hargs (by decide) (by decide)
  have a₄₀ := VG.Proof.AesCcm.X86_64.in_off (d := 32) (n := 8) hargs (by decide) (by decide)
  rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc] at a₁₆ a₃₂ a₄₀
  have w₁ := P.wW (show 112 + 8 ≤ 2560 by decide)
  have w₂ := P.wW (show 120 + 8 ≤ 2560 by decide)
  have w₃ := P.wW (show 128 + 8 ≤ 2560 by decide)
  have w₄ := P.wW (show 136 + 8 ≤ 2560 by decide)
  have w₅ := P.wW (show 144 + 8 ≤ 2560 by decide)
  have w₆ := P.wW (show 152 + 8 ≤ 2560 by decide)
  have w₇ := P.wW (show 160 + 8 ≤ 2560 by decide)
  have w₈ := P.wW (show 168 + 8 ≤ 2560 by decide)
  have w₉ := P.wW (show 176 + 8 ≤ 2560 by decide)
  have w₁₀ := P.wW (show 184 + 8 ≤ 2560 by decide)
  have w₁₁ := P.wW (show 192 + 8 ≤ 2560 by decide)
  have w₁₂ := P.wW (show 200 + 8 ≤ 2560 by decide)
  have w₁₃ := P.wW (show 208 + 8 ≤ 2560 by decide)
  have w₁₄ := P.wW (show 232 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h⟩ : ∃ s₁, runBlock isa
      ([.mov .rax (.mem (at_ .rsp 40)), .mov .r10 (.mem (at_ .rsp 8)), .mov .r11 (.mem (at_ .rsp 16))] ++ save .rax ++
        [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
          .store (at_ .r15 nonceO) .rdx, .store (at_ .r15 nlenO) .rcx, .store (at_ .r15 aadO) .r8,
          .store (at_ .r15 alenO) .r9, .store (at_ .r15 dataO) .r10, .store (at_ .r15 lenO) .r11]) s = some s₁ ∧
      s₁.gpr .rsp = SP ∧ s₁.gpr .r15 = W ∧ s₁.gpr .r13 = K ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      Frame [VG.Proof.AesCcm.X86_64.entryR W] s.mem s₁.mem ∧ VG.Proof.AesCcm.X86_64.Saved s₁.mem W s.gpr ∧
      s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R ∧ s₁.mem.readW (W + BitVec.ofNat 64 160) 64 = N ∧
      s₁.mem.readW (W + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 nl ∧
      s₁.mem.readW (W + BitVec.ofNat 64 176) 64 = A ∧
      s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al ∧
      s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = D ∧
      s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by
    have cE : ∀ d, 112 ≤ d → d + 8 ≤ 240 → (VG.Proof.AesCcm.X86_64.entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
    refine ⟨_, by crun [save, saved, List.map_cons, List.map_nil, hW, hsp, hD, hn, a₈, a₁₆, a₄₀, w₁, w₂, w₃, w₄,
      w₅, w₆, w₇, w₈, w₉, w₁₀, w₁₁, w₁₂, w₁₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
    · rfl
    · rfl
    · simp only [mem_setReg]
      repeat (first | exact Frame.refl _ _ |
        refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
    · intro p hp
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (disch := decide) only [mem_setReg, VG.Proof.AesCcm.X86_64.readW_writeW_off, Mem.readW_writeW_self64]
    all_goals simp (disch := decide) only [mem_setReg, VG.Proof.AesCcm.X86_64.readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
      ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9]
  obtain ⟨hsp₁, h15, h13, hrd₁, hwr₁, f₁, sv₁, s232, s160, s168, s176, s184, s192, s200⟩ := h
  have htl₁ : s₁.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl := by
    rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have e : SP + BitVec.ofNat 64 32 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 24 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
      rw [e]
      exact (hargsW.sub_left (Offset.sub_base _ (by decide))).sub_right (Lay.wSub (by decide))) (by decide), htl]
  have a₃₂' : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [hrd₁, hwr₁]; exact a₃₂
  have w₁₃' : InRegions s₁.wr (W + BitVec.ofNat 64 208) 8 := by rw [hwr₁]; exact w₁₃
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .rax (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rax] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 tl) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by crun [hsp₁, h15, htl₁, a₃₂', w₁₃'], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have k : ∀ {d}, (d + 8 ≤ 208 ∨ 216 ≤ d) → d + 8 ≤ 2 ^ 64 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [hm₂, VG.Proof.AesCcm.X86_64.readW_writeW_off _ (by omega) h₂ (by decide)]
  refine ⟨s₂, ?_, ⟨by rw [hg₂ _ (by decide), h13], by rw [hg₂ _ (by decide), h15], by rw [hg₂ _ (by decide), hsp₁],
    P.of_eq (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁])⟩,
    ⟨by rw [k (by omega) (by decide), s232], by rw [k (by omega) (by decide), s160],
      by rw [k (by omega) (by decide), s168], by rw [k (by omega) (by decide), s176],
      by rw [k (by omega) (by decide), s184], by rw [k (by omega) (by decide), s192],
      by rw [k (by omega) (by decide), s200], by rw [hm₂, Mem.readW_writeW_self64]⟩,
    fun p hp => ?_, ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [show VG.Impl.AesCcm.X86_64.entry = ([.mov .rax (.mem (at_ .rsp 40)), .mov .r10 (.mem (at_ .rsp 8)),
        .mov .r11 (.mem (at_ .rsp 16))] ++ save .rax ++
        [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
          .store (at_ .r15 nonceO) .rdx, .store (at_ .r15 nlenO) .rcx, .store (at_ .r15 aadO) .r8,
          .store (at_ .r15 alenO) .r9, .store (at_ .r15 dataO) .r10, .store (at_ .r15 lenO) .r11]) ++
        [.mov .rax (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rax] by
      simp only [VG.Impl.AesCcm.X86_64.entry, List.append_assoc, List.cons_append, List.nil_append],
      VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂]
  · have hp' := hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [← sv₁ p hp]
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k (by decide) (by decide)
  · rw [hm₂]
    exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 208) (n := 8) (e := 112) (k := 128)
      (by decide) (by decide) (by decide))

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {g : Reg → BitVec 64} (hs : VG.Proof.AesCcm.X86_64.Saved s.mem W g) :
    ∃ s', runBlock isa VG.Impl.AesCcm.X86_64.restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 112 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 120 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 128 + 8 ≤ 2560 by decide)
  have r₄ := E.perm.wR (show 136 + 8 ≤ 2560 by decide)
  have r₅ := E.perm.wR (show 144 + 8 ≤ 2560 by decide)
  have r₆ := E.perm.wR (show 152 + 8 ≤ 2560 by decide)
  have v₁ := hs (.rbx, 112) (by decide)
  have v₂ := hs (.rbp, 120) (by decide)
  have v₃ := hs (.r12, 128) (by decide)
  have v₄ := hs (.r13, 136) (by decide)
  have v₅ := hs (.r14, 144) (by decide)
  have v₆ := hs (.r15, 152) (by decide)
  refine ⟨_, by crun [VG.Impl.AesCcm.X86_64.restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Args`. -/
section

/-!
# AES-CCM on x86-64: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`TagBuf`, `args_of_seal`, `args_of_open`). Between `entry` and `restore`, the
pieces only write the parts of `W` below 112, from 216 to 232 and from 240
on, the stack below `SP` and the data (`mutR`), so they keep the slots, the
saved registers, the key schedule, the nonce, the associated data, the tag's
address on the stack (`argT_kept`) and the received tag (`tag_kept`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Impl.AesCcm.X86_64 (saved)
open VG.Spec.Aes (bytesAt)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), a tag of `tl` bytes, the working space at
`W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) : Prop where
  lay : VG.Proof.AesCcm.X86_64.Lay K W SP
  perm : VG.Proof.AesCcm.X86_64.Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : VG.Proof.AesCcm.X86_64.Buf K W SP s N nl
  aad : VG.Proof.AesCcm.X86_64.Buf K W SP s A al
  data : VG.Proof.AesCcm.X86_64.Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩
  argsD : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩

/-- The tag, the `tl` bytes at `T`: apart from the data, `W` and the stack
below `SP`. -/
structure TagBuf (W SP D : Addr) (n : Nat) (T : Addr) (tl : Nat) : Prop where
  d : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  w : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩
  stk : (below SP 16).Disjoint ⟨T, tl⟩
  wrap : T.toNat + tl ≤ 2 ^ 64

theorem arg_eq (s : State) (i : Nat) : VG.Proof.AesCcm.arg s i = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 := rfl

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : VG.Proof.AesCcm.oneLay s)
    (hk : Covers [⟨s.gpr .rdi, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [VG.Proof.AesCcm.args s 5] (s.rd ++ s.wr))
    (hD : Covers [⟨VG.Proof.AesCcm.arg s 0, (VG.Proof.AesCcm.arg s 1).toNat⟩] s.wr) (hW : Covers [⟨VG.Proof.AesCcm.arg s 4, 2560⟩] s.wr) :
    VG.Proof.AesCcm.X86_64.Args s (s.gpr .rdi) (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (VG.Proof.AesCcm.arg s 0) (s.gpr .rsi).toNat
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 3).toNat ∧
      VG.Proof.AesCcm.X86_64.TagBuf (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 2) (VG.Proof.AesCcm.arg s 3).toNat := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, b20, b21, b22, b23,
    b24, b25, b26, _, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact ⟨{
    lay := ⟨b20, b25, d2, d14, d19, b26⟩
    perm := ⟨hk, hW⟩
    rounds := hR
    nonce := ⟨hN, BitVec.isLt _, b21, d4, d15⟩
    aad := ⟨hA, BitVec.isLt _, b22, d6, d16⟩
    data := ⟨VG.Proof.AesCcm.X86_64.covers_left hD, BitVec.isLt _, b23, d9, d17⟩
    dw := hD
    dk := d1
    nd := d3
    ad := d5
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    retW := d13
    retD := d12
    args := ha
    argsW := d11.symm
    argsD := d10.symm }, ⟨d7, d8, d18, b24⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : VG.Proof.AesCcm.sealPre s) :
    (VG.Proof.AesCcm.X86_64.Args s (s.gpr .rdi) (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (VG.Proof.AesCcm.arg s 0) (s.gpr .rsi).toNat
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 3).toNat ∧
      VG.Proof.AesCcm.X86_64.TagBuf (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 2) (VG.Proof.AesCcm.arg s 3).toNat) ∧
      Covers [⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩] s.wr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩ := by
  obtain ⟨hrd, hwr, hl, hrt⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      VG.Proof.AesCcm.args s 5], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    VG.Proof.AesCcm.X86_64.covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨VG.Proof.AesCcm.arg s 0, (VG.Proof.AesCcm.arg s 1).toNat⟩ : Region), ⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩, ⟨VG.Proof.AesCcm.arg s 4, 2560⟩],
      Covers [r] s.wr := fun r hr => VG.Proof.AesCcm.X86_64.covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesCcm.X86_64.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mwr _ (by simp), hrt⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : VG.Proof.AesCcm.openPre s) :
    (VG.Proof.AesCcm.X86_64.Args s (s.gpr .rdi) (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (VG.Proof.AesCcm.arg s 0) (s.gpr .rsi).toNat
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 3).toNat ∧
      VG.Proof.AesCcm.X86_64.TagBuf (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (VG.Proof.AesCcm.arg s 0) (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 2) (VG.Proof.AesCcm.arg s 3).toNat) ∧
      Covers [⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨VG.Proof.AesCcm.arg s 2, (VG.Proof.AesCcm.arg s 3).toNat⟩, VG.Proof.AesCcm.args s 5], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    VG.Proof.AesCcm.X86_64.covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨VG.Proof.AesCcm.arg s 0, (VG.Proof.AesCcm.arg s 1).toNat⟩ : Region), ⟨VG.Proof.AesCcm.arg s 4, 2560⟩], Covers [r] s.wr := fun r hr =>
    VG.Proof.AesCcm.X86_64.covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨VG.Proof.AesCcm.X86_64.args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mrd _ (by simp)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the pieces before the data is written may change. -/
abbrev wR (W SP : Addr) : List Region := [VG.Proof.AesCcm.X86_64.wA W, VG.Proof.AesCcm.X86_64.wK W, VG.Proof.AesCcm.X86_64.wC W, below SP 16]

theorem wR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ VG.Proof.AesCcm.X86_64.wR W SP, ∃ r' ∈ VG.Proof.AesCcm.X86_64.mutR W SP D n, Region.Sub r r' := by
  intro r hr
  refine ⟨r, ?_, fun _ h => h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl <;> simp

section
variable {K W SP N A D : Addr} {R nl al n tl : Nat} {m m' : Mem}

theorem slots_mut (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) m m') (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl m) : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl m' := by
  have k : ∀ d, (112 ≤ d ∧ d + 8 ≤ 216 ∨ 232 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (VG.Proof.AesCcm.X86_64.kept_mut L hD hd) (by decide)
  exact ⟨by rw [k 232 (by decide)]; exact S.rounds, by rw [k 160 (by decide)]; exact S.nonce,
    by rw [k 168 (by decide)]; exact S.nlen, by rw [k 176 (by decide)]; exact S.aad,
    by rw [k 184 (by decide)]; exact S.alen, by rw [k 192 (by decide)]; exact S.data,
    by rw [k 200 (by decide)]; exact S.len, by rw [k 208 (by decide)]; exact S.tl⟩

theorem saved_mut (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) m m') {g : Reg → BitVec 64} (S : VG.Proof.AesCcm.X86_64.Saved m W g) : VG.Proof.AesCcm.X86_64.Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 216 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (VG.Proof.AesCcm.X86_64.kept_mut L hD (.inl hd))
    (by decide)

theorem ciph_mut (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hf : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) m m') : Spec.Ccm.ctxCiph m' K R = Spec.Ccm.ctxCiph m K R :=
  VG.Proof.AesCcm.X86_64.ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) m m') :
    bytesAt m' P len = bytesAt m P len :=
  VG.Proof.AesCcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega)

theorem buf_wR {s : State} {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len) (hf : Frame (VG.Proof.AesCcm.X86_64.wR W SP) m m') :
    bytesAt m' P len = bytesAt m P len :=
  VG.Proof.AesCcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

end

section
variable {K W SP D : Addr} {n : Nat}

/-- The tag's address, at `SP + 24`, is apart from what the entry and the
pieces write. -/
theorem argT_disj (hW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ VG.Proof.AesCcm.X86_64.entryR W :: VG.Proof.AesCcm.X86_64.mutR W SP D n, (⟨SP + BitVec.ofNat 64 24, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 24, 8⟩ ⟨SP + BitVec.ofNat 64 8, 40⟩ := by
    rw [show SP + BitVec.ofNat 64 24 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 16 by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]]
    exact Offset.sub_base _ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Region.sub_prefix (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact Offset.disjoint_below SP (by decide)
  · exact hD.sub_left hs

/-- The tag's address, at `SP + 24`, through the entry and the pieces. -/
theorem argT_kept {m m' : Mem} (hf : Frame (VG.Proof.AesCcm.X86_64.entryR W :: VG.Proof.AesCcm.X86_64.mutR W SP D n) m m')
    (hW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩) :
    m'.readW (SP + BitVec.ofNat 64 24) 64 = m.readW (SP + BitVec.ofNat 64 24) 64 :=
  hf.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (VG.Proof.AesCcm.X86_64.argT_disj hW hD) (by decide)

/-- The received tag, through the entry and the pieces. -/
theorem tag_kept {T : Addr} {tl : Nat} (hT : VG.Proof.AesCcm.X86_64.TagBuf W SP D n T tl) (ht : tl ≤ 16) {m m' : Mem}
    (hf : Frame (VG.Proof.AesCcm.X86_64.entryR W :: VG.Proof.AesCcm.X86_64.mutR W SP D n) m m') : bytesAt m' T tl = bytesAt m T tl :=
  VG.Proof.AesCcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Region.sub_prefix (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.stk.symm
    · exact hT.d) (by omega)

end

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.CTBase`. -/
section

/-!
# AES-CCM on x86-64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`). Both runs have the same public
arguments, kept in the slots of `W` (`Slots`), so the taint analysis starts
from the registers that agree and those slots, public (`ccmT`, `both_agree`);
what correctness says about each run is added with `RelCT.wp`.
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

/-- The taint: the registers `rs`, `r13`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region) and the slots of the
public arguments `[160, 216)` and `[232, 240)` public. -/
def ccmT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r13, .r15, .rsp]), flags := false, lens := [0, 2560], bases := [(.r15, 1, 0)],
    slots := [(1, 160, 56), (1, 232, 8)] }

/-- Two runs with the same public arguments: both in the environment, with
the same slots and writable regions, agreeing on the registers `rs`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (rs : List Reg) (s₁ s₂ : State) :
    Prop where
  e₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁
  e₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂
  sl₁ : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s₁.mem
  sl₂ : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s₂.mem
  wr₁ : s₁.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  wr₂ : s₂.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- Bytes of a word that both memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} {v : BitVec 64} (h₁ : m₁.readW a 64 = v) (h₂ : m₂.readW a 64 = v)
    {j : Nat} (hj : j < 8) : m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  have e : bytesAt m₁ a 8 = bytesAt m₂ a 8 := by rw [← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, h₁, h₂]
  rw [← VG.Proof.AesCcm.X86_64.getElem_bytesAt m₁ a hj, ← VG.Proof.AesCcm.X86_64.getElem_bytesAt m₂ a hj]
  exact List.getElem_of_eq e _

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h : VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂) : X86_64.Taint.Agree (VG.Proof.AesCcm.X86_64.ccmT rs) s₁ s₂ := by
  have wf : ∀ {s : State}, VG.Proof.AesCcm.X86_64.Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.Wf (VG.Proof.AesCcm.X86_64.ccmT rs) s := fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 2560 ≤ 2 ^ 64; decide
    · simp only [VG.Proof.AesCcm.X86_64.ccmT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.wr₁, h.wr₂], wf h.e₁ h.wr₁, wf h.e₂ h.wr₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.e₁.r13, h.e₂.r13]
      · rw [h.e₁.r15, h.e₂.r15]
      · rw [h.e₁.rsp, h.e₂.rsp]
  · simp only [VG.Proof.AesCcm.X86_64.ccmT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> simp [VG.Proof.AesCcm.X86_64.ccmT]
  · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k := fun s hw => by
      simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
    have hw : ∀ d, k = d + (k - d) → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
      fun d e => by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc, ← e]
    simp only [VG.Proof.AesCcm.X86_64.ccmT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl <;> rw [hb s₁ h.wr₁, hb s₂ h.wr₂]
    · simp only at hk₁ hk₂
      have S₁ := h.sl₁
      have S₂ := h.sl₂
      have key : ∀ d, d ∈ [160, 168, 176, 184, 192, 200, 208] → d ≤ k → k < d + 8 →
          s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
        rw [hw d (by omega)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact VG.Proof.AesCcm.X86_64.word_byte S₁.nonce S₂.nonce (by omega)
        · exact VG.Proof.AesCcm.X86_64.word_byte S₁.nlen S₂.nlen (by omega)
        · exact VG.Proof.AesCcm.X86_64.word_byte S₁.aad S₂.aad (by omega)
        · exact VG.Proof.AesCcm.X86_64.word_byte S₁.alen S₂.alen (by omega)
        · exact VG.Proof.AesCcm.X86_64.word_byte S₁.data S₂.data (by omega)
        · exact VG.Proof.AesCcm.X86_64.word_byte S₁.len S₂.len (by omega)
        · exact VG.Proof.AesCcm.X86_64.word_byte S₁.tl S₂.tl (by omega)
      have hq : (k - 160) / 8 = 0 ∨ (k - 160) / 8 = 1 ∨ (k - 160) / 8 = 2 ∨ (k - 160) / 8 = 3 ∨
          (k - 160) / 8 = 4 ∨ (k - 160) / 8 = 5 ∨ (k - 160) / 8 = 6 := by omega
      exact key (160 + 8 * ((k - 160) / 8)) (by
        rcases hq with h | h | h | h | h | h | h <;> rw [h] <;> decide) (by omega) (by omega)
    · simp only at hk₁ hk₂
      rw [hw 232 (by omega)]
      exact VG.Proof.AesCcm.X86_64.word_byte h.sl₁.rounds h.sl₂.rounds (by omega)

/-- Code the taint analysis checks from `ccmT rs`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂)
    (hc : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (VG.Proof.AesCcm.X86_64.ccmT rs) (fun s₁ s₂ h => VG.Proof.AesCcm.X86_64.both_agree hDW hn (hP _ _ h)) hc

/-- Code the taint analysis checks from `ccmT rs`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂)
    (hc : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmT rs) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (VG.Proof.AesCcm.X86_64.both_agree hDW hn (hP _ _ hp)) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

theorem eval_e_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .e s₁ = isa.eval .e s₂ := h
theorem eval_ne_eq {s₁ s₂ : State} (h : s₁.zf = s₂.zf) : isa.eval .ne s₁ = isa.eval .ne s₂ := by
  show s₁.zf.map _ = s₂.zf.map _; rw [h]
theorem eval_b_eq {s₁ s₂ : State} (h : s₁.cf = s₂.cf) : isa.eval .b s₁ = isa.eval .b s₂ := h

/-- `a; (b; (c; d))`, related as `(a; (b; c)); d`. -/
theorem rel_assoc3 {P Q : State → State → Prop} {a b c d : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b c)) d) Q) : RelCT isa P (.seq a (.seq b (.seq c d))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `a; (b; c)`, related as `(a; b); c`. -/
theorem rel_assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := RelCT.assoc h

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (s : State) : Prop where
  env : VG.Proof.AesCcm.X86_64.Env K W SP s
  sl : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 2560⟩]

theorem Both.of {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (o₁ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁) (o₂ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, h⟩

theorem Both.one₁ {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (h : VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂) : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ := ⟨h.e₁, h.sl₁, h.wr₁⟩

theorem Both.one₂ {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (h : VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂) : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ := ⟨h.e₂, h.sl₂, h.wr₂⟩

/-- Registers with the same value in both runs agree. -/
theorem agree_of {s₁ s₂ : State} {l : List (Reg × BitVec 64)} (h₁ : ∀ p ∈ l, s₁.gpr p.1 = p.2)
    (h₂ : ∀ p ∈ l, s₂.gpr p.1 = p.2) : ∀ r ∈ l.map Prod.fst, s₁.gpr r = s₂.gpr r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  rw [h₁ p hp, h₂ p hp]

/-- `a; (b; (c; (d; e)))`, related as `(a; (b; (c; d))); e`. -/
theorem rel_assoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) : RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Tag`. -/
section

/-!
# AES-CCM on x86-64: the tag (`tag y`)

Untrusted: everything here is checked by Lean. `tag y` makes `Ctr₀` at
`W + 64` and calls `vg_aes_ctr32` on the MAC state at `W + y`, one block:
the state XORed with `CIPH_K(Ctr₀)`, CCM's keystream from `Ctr₀` (`tag_ok`),
whose first `t` bytes are the MAC encrypted (`Proof.AesCcm.take_xorFrom_zero`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The arguments of the call: `Ctr₀` at `W + 64`. -/
theorem tagArgs_ok {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov32 .rax (imm 0)] : List Instr) ++ ctrAt ++ ([.mov .rdi (.reg .r13)] : List Instr) ++
      ptr .rdx .r15 c1O ++ ptr .rcx .r15 y ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) s fun s₃ =>
      VG.Proof.AesCcm.X86_64.Env K W SP s₃ ∧ VG.Proof.AesCcm.X86_64.CtrCall s₃ K (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 384) R 1 ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14], s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  have h15 := E.r15
  have h13' := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₁, run₁, hm₁, hsi₁, hax₁, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov32 .rax (imm 0)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rax = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  obtain ⟨s₂, run₂, f₂, hc₂, hg₂, hrd₂, hwr₂⟩ :=
    VG.Proof.AesCcm.X86_64.ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (Nat.pow_pos (by decide)) hax₁
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have h15₂ := E₂.r15
  obtain ⟨s₃, run₃, hm₃, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      ([.mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 y ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s₂ =
        some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .rdi = K ∧ s₃.gpr .rsi = BitVec.ofNat 64 R ∧ s₃.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      s₃.gpr .rcx = W + BitVec.ofNat 64 y ∧ s₃.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₃.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .rbp, .r12, .r14], s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [h15₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, E₂.r13]
    · simp [gpr_setReg, hg₂ .rsi (by decide) (by decide) (by decide), hsi₁]
    · simp [gpr_setReg, h15₂]
    · simp [gpr_setReg, h15₂, VG.Proof.AesCcm.X86_64.imm_eq hy']
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₃ : VG.Proof.AesCcm.X86_64.Env K W SP s₃ := E₂.keep (fun r hr => hg₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₃ hwr₃
  refine WP.of_runBlock ⟨s₃, ?_, ?_⟩
  · simp only [List.append_assoc]
    rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, VG.Proof.AesCcm.X86_64.runBlock_append, run₂, Option.bind_some]
    simpa only [List.append_assoc] using run₃
  have hq := VG.Proof.AesCcm.X86_64.srcW (s := s₃) L E₃.perm (t := y) (k := 16 * 1) (by omega)
  have hqc : (⟨W + BitVec.ofNat 64 y, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16 * 1⟩ := L.k_w.sub_right (Lay.wSub (by omega))
  refine ⟨E₃, VG.Proof.AesCcm.X86_64.cargs L E₃ hR (c := 64) (by decide) hq hqc hqk (E₃.perm.wC (d := y) (n := 16 * 1) (by omega))
    hdi hsi hdx hcx hr8 hr9, fun r hr => ?_, by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁],
    by rw [hm₃, ← hm₁]; exact f₂, by rw [hm₃]; exact hc₂⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have h3 : r ∈ [Reg.r13, .r15, .rsp, .rbx, .rbp, .r12, .r14] := by rcases hr with rfl | rfl | rfl | rfl <;> simp
  have ha : r ≠ .rax := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hc : r ≠ .rcx := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hd : r ≠ .rdx := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hs : r ≠ .rsi := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  rw [hg₃ r h3, hg₂ r ha hc hd, hg₁ r ha hs]

/-- The MAC state at `W + y` XORed with `CIPH_K(Ctr₀)`. -/
theorem tag_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (tag v.callee y) s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩,
        below SP 16] s.mem s'.mem ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 0 (bytesAt s.mem (W + BitVec.ofNat 64 y) 16) := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.tagArgs_ok L E hR hRo h7 h13 hc0 hy) fun s₃ ⟨E₃, C₃, g₃, hrd₃, hwr₃, f₃, hc₃⟩ => ?_)
  refine WP.mono (VG.Proof.AesCcm.X86_64.ctr_call v C₃) fun s₄ h => ?_
  have hqc : (⟨W + BitVec.ofNat 64 y, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hK₃ : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    VG.Proof.AesCcm.X86_64.ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have hY₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (W + BitVec.ofNat 64 y) 16 :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hqc) (by decide)
  refine ⟨E₃.of_saved h.saved h.rd h.wr, fun r hr => ?_, by rw [h.rd, hrd₃], by rw [h.wr, hwr₃], ?_, ?_⟩
  · have hr' : r ∈ calleeSaved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [h.saved r hr', g₃ r hr]
  · have f₄ := h.frame
    rw [E₃.rsp] at f₄
    refine (f₃.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (f₄.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨below SP 16, by simp, VG.Proof.AesCcm.X86_64.below8_sub SP⟩
  · have hc := ctr32_ccm (m := s₃.mem) (m' := s₄.mem) (K := K) (C := W + BitVec.ofNat 64 64)
      (D := W + BitVec.ofNat 64 y) (R := R) (nonce := nonce) (by omega) (j := 0) (k := 1)
      (fun i hi => by
        rw [show i = 0 by omega, Nat.zero_add]
        show Spec.Gcm.ofBytes _ = _
        rw [hc₃]) h.out
    rw [Nat.mul_one] at hc
    rw [hc, hK₃, hY₃]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Chunk`. -/
section

/-!
# AES-CCM on x86-64: a chunk of counter mode (`ctrChunk`)

Untrusted: everything here is checked by Lean. After `b` whole blocks
(`CtrInv`), `ctrChunk` encrypts `k = min (n/16 − b, 2³² − (1 + b) mod 2³²)`
more by `vg_aes_ctr32` from `Ctr₁₊ᵦ`, whose counters do not wrap around in
their low 32 bits, so that they are CCM's (`chunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `W + 64`, `k` at
`W + 216`, the working space of the functions called, the stack below `SP`
and the data. -/
abbrev ctrR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 64, 32⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16, ⟨D, n⟩]

/-- What `ctr` writes, within what the pieces may write. -/
theorem ctrR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ VG.Proof.AesCcm.X86_64.ctrR W SP D n, ∃ r' ∈ VG.Proof.AesCcm.X86_64.mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wK W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `ctr` needs, of the state `s` it starts from. -/
structure CtrCtx (K W SP : Addr) (s : State) (R : Nat) (nonce : List Byte) (D : Addr) (n : Nat) : Prop where
  lay : VG.Proof.AesCcm.X86_64.Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ro : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  hn : n < 256 ^ (15 - nonce.length)
  c0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0
  buf : VG.Proof.AesCcm.X86_64.Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩

namespace CtrCtx

variable {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}

/-- The parts of `W` that `ctr` does not write. -/
theorem disj (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {d k : Nat}
    (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 216) ∨ (224 ≤ d ∧ d + k ≤ 384)) :
    ∀ r ∈ VG.Proof.AesCcm.X86_64.ctrR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.lay.w_w (by omega) (by omega) (by decide)
  · exact C.lay.w_w (by omega) (by omega) (by decide)
  · exact C.lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (C.lay.stk_w' (by omega)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega))).symm

theorem kdisj (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) : ∀ r ∈ VG.Proof.AesCcm.X86_64.ctrR W SP D n, (⟨K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.stk_k.symm
  · exact C.dk

theorem bytes_kept (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem m) {d k : Nat}
    (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 216) ∨ (224 ≤ d ∧ d + k ≤ 384)) :
    bytesAt m (W + BitVec.ofNat 64 d) k = bytesAt s.mem (W + BitVec.ofNat 64 d) k :=
  VG.Proof.AesCcm.X86_64.bytesAt_frame hf (C.disj h) (by omega)

theorem readW_kept (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem m) {d : Nat}
    (h : d + 8 ≤ 64 ∨ (96 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 384)) :
    m.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (C.disj h) (by decide)

theorem ciph_kept (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem m) :
    Spec.Ccm.ctxCiph m K R = Spec.Ccm.ctxCiph s.mem K R :=
  VG.Proof.AesCcm.X86_64.ctxCiph_frame hf C.kdisj (by rcases C.rounds with h | h | h <;> subst h <;> decide)

end CtrCtx

/-- The state of `ctr` after `b` whole blocks: those encrypted, the rest of
the data as it was. -/
structure CtrInv (K W SP : Addr) (s : State) (R : Nat) (nonce : List Byte) (D : Addr) (n b : Nat) (t : State) :
    Prop where
  env : VG.Proof.AesCcm.X86_64.Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b)
  r14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b)
  le : b ≤ n / 16
  frame : Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem t.mem
  done : bytesAt t.mem D (16 * b) = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D (16 * b))
  rest : bytesAt t.mem (D + BitVec.ofNat 64 (16 * b)) (n - 16 * b) =
    bytesAt s.mem (D + BitVec.ofNat 64 (16 * b)) (n - 16 * b)

theorem low32 (x : Nat) : ((BitVec.ofNat 64 x).setWidth 32).setWidth 64 = BitVec.ofNat 64 (x % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem two32_sub {y : Nat} (hy : y < 2 ^ 32) :
    (4294967296 : BitVec 64) - BitVec.ofNat 64 y = BitVec.ofNat 64 (2 ^ 32 - y) :=
  VG.Proof.AesCcm.X86_64.ofNat_sub (a := 2 ^ 32) (b := y) (Nat.le_of_lt hy) (by decide)

/-- `k = min (m, 2³² − (1 + b) mod 2³²)` in `r8`, for `m` blocks left. -/
theorem kSel_ok {b m : Nat} {t : State} (hbx : t.gpr .rbx = BitVec.ofNat 64 m)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b)) (hm : m < 2 ^ 64) :
    WP isa (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)]) (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))) t
      fun t₂ => t₂.mem = t.mem ∧ t₂.gpr .r8 = BitVec.ofNat 64 (min m (2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
        (∀ r, r ≠ .r8 → r ≠ .rcx → t₂.gpr r = t.gpr r) ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  obtain ⟨t₁, run₁, hm₁, hr8₁, hcx₁, hcf₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁, runBlock isa
      [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)] t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .r8 = BitVec.ofNat 64 m ∧ t₁.gpr .rcx = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) ∧
      t₁.cf = some (decide (m < 2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
      (∀ r, r ≠ .r8 → r ≠ .rcx → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14]
      rw [VG.Proof.AesCcm.X86_64.low32, VG.Proof.AesCcm.X86_64.two32_sub (Nat.mod_lt _ (by decide))]
    · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14, hbx]
      rw [VG.Proof.AesCcm.X86_64.low32, VG.Proof.AesCcm.X86_64.two32_sub (Nat.mod_lt _ (by decide)), VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hm,
        VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega)]
    · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (VG.Proof.AesCcm.X86_64.eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
  · have h := of_decide_eq_true ht
    exact WP.of_runBlock ⟨t₁, rfl, hm₁, by rw [hr8₁, Nat.min_eq_left (by omega)], hg₁, hrd₁, hwr₁⟩
  · have h := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · exact hm₁
    · simp only [gpr_setReg, ite_true, hcx₁, Nat.min_eq_right (Nat.le_of_not_lt h)]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, ite_false]; exact hg₁ r h₁ h₂
    · exact hrd₁
    · exact hwr₁

/-- The arguments of the call, and `Ctr₁₊ᵦ`. -/
theorem setup_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {b k : Nat} {t t₂ : State} (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) (hm₂ : t₂.mem = t.mem) (hr8₂ : t₂.gpr .r8 = BitVec.ofNat 64 k)
    (hg₂ : ∀ r, r ≠ .r8 → r ≠ .rcx → t₂.gpr r = t.gpr r) (hrd₂ : t₂.rd = t.rd) (hwr₂ : t₂.wr = t.wr) :
    ∃ t₅, runBlock isa (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++
        ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ([.mov .rcx (.reg .r12)] : List Instr) ++
        ptr .r9 .r15 scrO) t₂ = some t₅ ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem ∧
      bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b) ∧
      t₅.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      t₅.gpr .rdi = K ∧ t₅.gpr .rsi = BitVec.ofNat 64 R ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₅.gpr .rcx = D + BitVec.ofNat 64 (16 * b) ∧ t₅.gpr .r8 = BitVec.ofNat 64 k ∧
      t₅.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
  have E := I.env
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP t₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have h15 := E₂.r15
  have rR := E₂.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hRo : t₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [hm₂, C.readW_kept I.frame (by omega), C.ro]
  obtain ⟨t₃, run₃, hm₃, hsi₃, hax₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] t₂ = some t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.gpr .rsi = BitVec.ofNat 64 R ∧ t₃.gpr .rax = BitVec.ofNat 64 (1 + b) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t₃.gpr r = t₂.gpr r) ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by crun [h15, rR], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hRo]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hg₂ .r14 (by decide) (by decide), I.r14]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  have E₃ : VG.Proof.AesCcm.X86_64.Env K W SP t₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hc0₃ : bytesAt t₃.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₃, hm₂, C.bytes_kept I.frame (by omega), C.c0]
  have hq16 : n / 16 < 256 ^ (15 - nonce.length) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) C.hn
  obtain ⟨t₄, run₄, f₄, hc₄, hg₄, hrd₄, hwr₄⟩ :=
    VG.Proof.AesCcm.X86_64.ctrAt_ok E₃ C.h7 C.h13 hc0₃ (i := 1 + b) (by omega) hax₃
  have E₄ : VG.Proof.AesCcm.X86_64.Env K W SP t₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
  have h15₄ := E₄.r15
  have wk := E₄.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have g₄ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → t₄.gpr r = t.gpr r := fun r a c d e f => by
    rw [hg₄ r a c d, hg₃ r a e, hg₂ r f c]
  have r8₄ : t₄.gpr .r8 = BitVec.ofNat 64 k := by
    rw [hg₄ .r8 (by decide) (by decide) (by decide), hg₃ .r8 (by decide) (by decide), hr8₂]
  obtain ⟨t₅, run₅, hm₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ : ∃ t₅, runBlock isa
      ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ [.mov .rcx (.reg .r12)] ++
        ptr .r9 .r15 scrO) t₄ = some t₅ ∧ t₅.mem = t₄.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧
      t₅.gpr .rdi = K ∧ t₅.gpr .rsi = BitVec.ofNat 64 R ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₅.gpr .rcx = D + BitVec.ofNat 64 (16 * b) ∧ t₅.gpr .r8 = BitVec.ofNat 64 k ∧
      t₅.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
    refine ⟨_, by crun [h15₄, wk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, r8₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E₄.r13]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg₄ .rsi (by decide) (by decide) (by decide), hsi₃]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        g₄ .r12 (by decide) (by decide) (by decide) (by decide) (by decide), I.r12]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, r8₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₄]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq] <;>
        exact g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [rd_setReg, rd_arithFlags]; rw [hrd₄, hrd₃, hrd₂]
    · simp only [wr_setReg, wr_arithFlags]; rw [hwr₄, hwr₃, hwr₂]
  have hdis : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 216, 8⟩ :=
    C.lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨t₅, ?_, ?_, ?_, by rw [hm₅, Mem.readW_writeW_self64], hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩
  · simp only [List.append_assoc]
    rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₃, Option.bind_some, VG.Proof.AesCcm.X86_64.runBlock_append, run₄, Option.bind_some]
    simpa only [List.append_assoc] using run₅
  · rw [hm₅, ← hm₂, ← hm₃]
    exact (f₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩).writeW
      (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (by simp) _ (Region.contains_self _ _)
  · rw [hm₅, VG.Proof.AesCcm.X86_64.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self ⟨W + BitVec.ofNat 64 216, 8⟩) _
      (Region.contains_self _ _)) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdis)
      (by decide), hc₄]

/-- What follows the call: `k` blocks past them, and ZF set when none is left. -/
theorem step_ok {W D : Addr} {t : State} {n b k : Nat} (h15 : t.gpr .r15 = W)
    (rk : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 216) 8)
    (hkO : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k)
    (hbx : t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b)) (h14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b))
    (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b)) (hkb : b + k ≤ n / 16) (hn : n < 2 ^ 64) :
    ∃ t', runBlock isa
      [.mov .rax (.mem (at_ .r15 kO)), .alu .sub .rbx (.reg .rax), .alu .add .r14 (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .r12 (.reg .rax), .alu .test .rbx (.reg .rbx)] t = some t' ∧ t'.mem = t.mem ∧
      t'.gpr .rbx = BitVec.ofNat 64 (n / 16 - (b + k)) ∧ t'.gpr .r14 = BitVec.ofNat 64 (1 + (b + k)) ∧
      t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (b + k)) ∧ t'.zf = some (decide (b + k = n / 16)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by crun [h15, rk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, hbx]
    rw [show n / 16 - (b + k) = n / 16 - b - k by omega]
    exact VG.Proof.AesCcm.X86_64.ofNat_sub (by omega) (by omega)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, h14]
    rw [VG.Proof.AesCcm.X86_64.ofNat_add_ofNat, Nat.add_assoc]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, h12, VG.Proof.AesCcm.X86_64.ofNat_add_ofNat,
      BitVec.add_assoc]
    rw [show 16 * b + (k + k + (k + k) + (k + k + (k + k)) + (k + k + (k + k) + (k + k + (k + k)))) =
      16 * (b + k) by omega]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, hbx]
    rw [VG.Proof.AesCcm.X86_64.ofNat_sub (by omega) (by omega), VG.Proof.AesCcm.X86_64.and_self_beq (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- The state after a chunk of `k` blocks. -/
theorem chunk_inv {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {b k : Nat} {t : State} (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n b t)
    (hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32) (hkb : b + k ≤ n / 16) {t₅ t₆ t₇ : State}
    (f₅ : Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem)
    (hc₅ : bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b))
    (hsp : t₅.gpr .rsp = SP)
    (h : VG.Proof.AesCcm.X86_64.CtrPost t₅ K (W + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 384) R k t₆)
    (hm₇ : t₇.mem = t₆.mem) :
    Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem t₇.mem ∧
      bytesAt t₇.mem D (16 * (b + k)) =
        xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D (16 * (b + k))) ∧
      bytesAt t₇.mem (D + BitVec.ofNat 64 (16 * (b + k))) (n - 16 * (b + k)) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * (b + k))) (n - 16 * (b + k)) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  have cR : Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8] t.mem t₇.mem := by
    have fc := h.frame
    rw [hsp] at fc
    rw [hm₇]
    refine (f₅.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have toR : ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩,
      ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8],
      ∃ r' ∈ VG.Proof.AesCcm.X86_64.ctrR W SP D n, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨below SP 16, by simp, VG.Proof.AesCcm.X86_64.below8_sub SP⟩
  -- Separation of the data from what the chunk wrote.
  have sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ n →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩,
        ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8],
        (⟨D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    have hB := C.buf.slice (a := a) (k := l) hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint D (by omega) (by omega) (by omega)
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact (hB.stk.sub_left (VG.Proof.AesCcm.X86_64.below8_sub SP)).symm
  have hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    have h₁ : bytesAt t₇.mem D (16 * b) = bytesAt t.mem D (16 * b) := by
      have := VG.Proof.AesCcm.X86_64.bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega)) (by omega)) (by omega)
      rwa [BitVec.add_zero] at this
    have hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock C.h7 C.h13 hk32
        (by have := Nat.lt_of_le_of_lt (Nat.div_le_self n 16) C.hn; omega) i hi
    have hx := ctr32_ccm (by have := C.h13; omega) hinc h.out
    have f₅' : Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
    have hx₅ : bytesAt t₅.mem (D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      have hB := C.buf.slice (a := 16 * b) (k := n - 16 * b) (by omega)
      rw [VG.Proof.AesCcm.X86_64.bytesAt_prefix t₅.mem _ (show 16 * k ≤ n - 16 * b by omega),
        VG.Proof.AesCcm.X86_64.bytesAt_prefix s.mem _ (show 16 * k ≤ n - 16 * b by omega), ← I.rest,
        VG.Proof.AesCcm.X86_64.bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hB.w.sub_right (Lay.wSub (by decide))
          · exact hB.w.sub_right (Lay.wSub (by decide))) (by omega)]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      C.ciph_kept f₅', xorFrom_append _ _ _ (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    have hR' := VG.Proof.AesCcm.X86_64.bytesAt_frame cR (sep (a := 16 * (b + k)) (l := n - 16 * (b + k)) (.inr (Nat.le_refl _))
      (by omega)) (by omega)
    rw [hR', show D + BitVec.ofNat 64 (16 * (b + k)) = D + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (16 * k) by
        rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc, hbk],
      show n - 16 * (b + k) = n - 16 * b - 16 * k by omega, VG.Proof.AesCcm.X86_64.bytesAt_suffix _ _ (show 16 * k ≤ n - 16 * b by omega),
      VG.Proof.AesCcm.X86_64.bytesAt_suffix _ _ (show 16 * k ≤ n - 16 * b by omega), I.rest]

/-- One chunk. -/
theorem chunk_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {b : Nat} {t : State} (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) :
    WP isa (ctrChunk v.callee) t fun t' => ∃ k, k = min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ∧ 1 ≤ k ∧
      b + k ≤ n / 16 ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n (b + k) t' ∧ t'.zf = some (decide (b + k = n / 16)) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine VG.Proof.AesCcm.X86_64.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.kSel_ok I.rbx I.r14 (by omega)) fun t₂ ⟨hm₂, hr8₂, hg₂, hrd₂, hwr₂⟩ => ?_))
  obtain ⟨k, hk⟩ : ∃ k, k = min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at hr8₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + k ≤ n / 16 := by rw [hk]; omega
  have hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  obtain ⟨t₅, run₅, f₅, hc₅, hkO₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ :=
    VG.Proof.AesCcm.X86_64.setup_ok C I hb hm₂ hr8₂ hg₂ hrd₂ hwr₂
  have E₅ : VG.Proof.AesCcm.X86_64.Env K W SP t₅ := I.env.keep (fun r hr => hg₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₅ hwr₅
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  -- The call.
  have hS := (C.buf.of_eq (hrd₅.trans I.rd) (hwr₅.trans I.wr)).slice (a := 16 * b) (k := 16 * k) (by omega)
  have hqc : (⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    hS.w.sub_right (Lay.wSub (by decide))
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩ :=
    C.dk.sub_right (Offset.sub_base D (by omega))
  have hqw : Covers [⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩] t₅.wr := by
    rw [hwr₅, I.wr]; exact VG.Proof.AesCcm.X86_64.covers_off C.dw (by omega) hn64
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctr_call v (VG.Proof.AesCcm.X86_64.cargs L E₅ C.rounds (c := 64) (by decide) (VG.Proof.AesCcm.X86_64.srcBuf hS) hqc hqk hqw
    hdi hsi hdx hcx hr8 hr9)) fun t₆ h => ?_)
  have E₆ : VG.Proof.AesCcm.X86_64.Env K W SP t₆ := E₅.of_saved h.saved h.rd h.wr
  have sv : ∀ r ∈ [Reg.rbx, .r12, .r14], t₆.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl | rfl <;> decide), hg₅ r (by rcases hr with rfl | rfl | rfl <;> simp)]
  have dK : ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨W + BitVec.ofNat 64 384, 2048⟩, below (t₅.gpr .rsp) 8], (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (hS.w.sub_right (Lay.wSub (by decide))).symm
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [E₅.rsp]; exact ((L.stk_w' (by decide)).sub_left (VG.Proof.AesCcm.X86_64.below8_sub _)).symm
  have hkO : t₆.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [h.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) dK (by decide), hkO₅]
  obtain ⟨t₇, run₇, hm₇, hbx₇, h14₇, h12₇, hzf₇, hg₇, hrd₇, hwr₇⟩ :=
    VG.Proof.AesCcm.X86_64.step_ok E₆.r15 (E₆.perm.wR (show 216 + 8 ≤ 2560 by decide)) hkO (by rw [sv .rbx (by simp), I.rbx])
      (by rw [sv .r14 (by simp), I.r14]) (by rw [sv .r12 (by simp), I.r12]) hkb hn64
  obtain ⟨fr, dn, rs⟩ := VG.Proof.AesCcm.X86_64.chunk_inv C I hk32 hkb f₅ hc₅ E₅.rsp h hm₇
  exact WP.of_runBlock ⟨t₇, run₇, k, hk, hk1, hkb, ⟨E₆.keep hg₇ hrd₇ hwr₇, by rw [hrd₇, h.rd, hrd₅, I.rd],
    by rw [hwr₇, h.wr, hwr₅, I.wr], h12₇, hbx₇, h14₇, hkb, fr, dn, rs⟩, hzf₇⟩

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Cmp`. -/
section

/-!
# AES-CCM on x86-64: checking a received tag (`recv`, `cmp o`)

Untrusted: everything here is checked by Lean. These are AES-GCM's pieces,
with AES-CCM's working space: `recv` pads the `rbx` bytes of the received
tag at `rsi` with zeros at `W + 256` (`recv_ok`); `cmp o` pads the first `rbx`
bytes of the tag at `W + o` at `W + 240` and leaves 1 in `rax` if they are
the received ones, 0 if not (`cmp_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp vO rO copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.Cmac (le8)

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes (m : Mem) (P : Addr) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P xs) P 16 =
      xs ++ zeros (16 - xs.length) := by
  have h := VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at ((m.writeW P (0 : BitVec 64)).writeW (P + BitVec.ofNat 64 8) (0 : BitVec 64)) P
    (o := 0) (n := 16) xs (by omega) (by decide)
  rw [BitVec.add_zero] at h
  rw [h, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, List.take_zero, List.nil_append, Nat.zero_add]
  show xs ++ (Spec.Cmac.zeros 16).drop xs.length = _
  simp only [Spec.Cmac.zeros, List.drop_replicate, zeros]

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [VG.Proof.AesCcm.X86_64.le8_inj h₁, VG.Proof.AesCcm.X86_64.le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

theorem zero16_frame (m : Mem) (p : Addr) :
    Frame [⟨p, 16⟩] m ((m.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)) :=
  Proof.Cmac.frame_store2 _ _ _

theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

section
variable {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP)
include L

omit L in
/-- `recv`: the `t` bytes of the received tag at `T` (in `rsi`), padded at `W + 256`. -/
theorem recv_ok {s : State} (he : VG.Proof.AesCcm.X86_64.Env K W SP s) {t : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 t)
    (h1 : 1 ≤ t) (h16 : t ≤ 16) {T : Addr} (hsi : s.gpr .rsi = T) (hT : Covers [⟨T, t⟩] (s.rd ++ s.wr))
    (dW : (⟨T, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) :
    WP isa recv s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧
      bytesAt s'.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem T t ++ zeros (16 - t) ∧
      Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧ s'.gpr .rbx = s.gpr .rbx ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 256 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 264 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi₁, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 rO) .rax, .store (at_ .r15 (rO + 8)) .rax] ++
        ptr .rdi .r15 rO ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 256 ∧ s₁.gpr .rsi = T ∧ s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [rO, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, VG.Proof.AesCcm.X86_64.add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hsi]
    · simp [gpr_setReg, hbx]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have lp : LoopPre s₁ T (W + BitVec.ofNat 64 256) t :=
    ⟨hsi₁, hdi, hcx, h1, by omega, by rw [hrd₁, hwr₁]; exact hT, he₁.perm.wC (by omega),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
  have fz : Frame [⟨W + BitVec.ofNat 64 256, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact VG.Proof.AesCcm.X86_64.zero16_frame _ _
  have hR : bytesAt s₁.mem T t = bytesAt s.mem T t :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := VG.Proof.AesCcm.X86_64.length_bytesAt s₁.mem T t
  refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂, ?_, ?_, ?_,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [hm₂, hm₁, VG.Proof.AesCcm.X86_64.pad_bytes _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact h16), VG.Proof.AesCcm.X86_64.length_bytesAt, ← hm₁, hR]
  · refine fz.trans ?_
    rw [hm₂]
    exact (VG.Proof.AesCcm.X86_64.writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide) (by decide) (by decide)]

/-- `cmp o`: 1 in `rax` iff the first `t` bytes of the tag at `W + o` are
the received tag `T`, padded at `W + 256`. -/
theorem cmp_ok {o : Nat} (ho : o + 16 ≤ 240) {s : State} (he : VG.Proof.AesCcm.X86_64.Env K W SP s) {t : Nat}
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {T : List Byte} (hTl : T.length = t)
    (hT : bytesAt s.mem (W + BitVec.ofNat 64 256) 16 = T ++ zeros (16 - t)) :
    WP isa (cmp o) s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 o) t = T then 1 else 0) ∧
      Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h15 := he.r15
  have w₁ := he.perm.wW (show 240 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 248 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      ([.mov32 .rax (imm 0), .store (at_ .r15 vO) .rax, .store (at_ .r15 (vO + 8)) .rax] ++
        ptr .rdi .r15 vO ++ ptr .rsi .r15 o ++ [.mov .rcx (.reg .rbx)]) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .rdi = W + BitVec.ofNat 64 240 ∧ s₁.gpr .rsi = W + BitVec.ofNat 64 o ∧
      s₁.gpr .rcx = BitVec.ofNat 64 t ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have hoi : o < 2 ^ 31 := by omega
    refine ⟨_, by crun [vO, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, VG.Proof.AesCcm.X86_64.add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, h15, VG.Proof.AesCcm.X86_64.imm_eq hoi]
    · simp [gpr_setReg, hbx]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have dW : (⟨W + BitVec.ofNat 64 o, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 240, 16⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 240) t :=
    ⟨hsi, hdi, hcx, h1, by omega, VG.Proof.AesCcm.X86_64.covers_left (he₁.perm.wC (by omega)), he₁.perm.wC (by omega),
      dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have fz : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact VG.Proof.AesCcm.X86_64.zero16_frame _ _
  have hT' : bytesAt s₁.mem (W + BitVec.ofNat 64 o) t = bytesAt s.mem (W + BitVec.ofNat 64 o) t :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW) (by omega)
  have hlen := VG.Proof.AesCcm.X86_64.length_bytesAt s₁.mem (W + BitVec.ofNat 64 o) t
  have f₂ : Frame [⟨W + BitVec.ofNat 64 240, 16⟩] s.mem s₂.mem := by
    refine fz.trans ?_
    rw [hm₂]
    exact (VG.Proof.AesCcm.X86_64.writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  have hV : bytesAt s₂.mem (W + BitVec.ofNat 64 240) 16 =
      bytesAt s.mem (W + BitVec.ofNat 64 o) t ++ zeros (16 - t) := by
    rw [hm₂, hm₁, VG.Proof.AesCcm.X86_64.pad_bytes _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact h16), VG.Proof.AesCcm.X86_64.length_bytesAt, ← hm₁, hT']
  have hT₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = T ++ zeros (16 - t) := by
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hT]
  have he₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have r₁ := he₂.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have r₂ := he₂.perm.wR (show 256 + 8 ≤ 2560 by decide)
  have r₃ := he₂.perm.wR (show 248 + 8 ≤ 2560 by decide)
  have r₄ := he₂.perm.wR (show 264 + 8 ≤ 2560 by decide)
  have h15₂ := he₂.r15
  generalize hX : (s₂.mem.readW (W + BitVec.ofNat 64 240) 64 ^^^ s₂.mem.readW (W + BitVec.ofNat 64 256) 64) |||
    (s₂.mem.readW (W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64 ^^^
      s₂.mem.readW (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) 64) = X
  have hXe : X = 0 ↔ bytesAt s.mem (W + BitVec.ofNat 64 o) t = T := by
    rw [← hX, VG.Proof.AesCcm.X86_64.words_eq, hV, hT₂]
    constructor
    · intro e; exact List.append_cancel_right e
    · intro e; rw [e]
  have e248 : W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 248 := VG.Proof.AesCcm.X86_64.add_ofNat_assoc ..
  have e264 : W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 264 := VG.Proof.AesCcm.X86_64.add_ofNat_assoc ..
  rw [e248, e264] at hX
  obtain ⟨s₃, run₃, hax, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .rax (.mem (at_ .r15 vO)), .alu .xor .rax (.mem (at_ .r15 rO)),
        .mov .rdx (.mem (at_ .r15 (vO + 8))), .alu .xor .rdx (.mem (at_ .r15 (rO + 8))),
        .alu .or .rax (.reg .rdx), .alu .cmp .rax (imm 1), .mov32 .rax (imm 0), .alu32 .adc .rax (imm 0)] s₂ =
        some s₃ ∧ s₃.gpr .rax = (if X = 0 then 1 else 0) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [vO, rO, h15₂, r₁, r₂, r₃, r₄, execAlu32], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags, ite_true, ite_false, reduceCtorEq, hX]
      by_cases e : X = 0
      · subst e; rfl
      · have : ¬ X.toNat < 1 := fun h => e (BitVec.eq_of_toNat_eq (by simp; omega))
        simp only [e, ite_false, show (1#64 : BitVec 64).toNat = 1 from rfl, this, decide_false]
        rfl
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨s₃, run₃, he₂.keep hg₃ hrd₃ hwr₃, by rw [hax]; simp only [hXe], hm₃ ▸ f₂,
    by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁]⟩

end

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Crypt`. -/
section

/-!
# AES-CCM on x86-64: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_ok`, by `chunk_ok`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_ok`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_ok`), which is its encryption (`Proof.AesCcm.crypt_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre xorLoop_ok xorBytes)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `r12`, `rbx` and `r14` for the first chunk. -/
theorem ctrHeadBlk_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)]) s fun s₁ =>
      VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n 0 s₁ ∧ s₁.zf = some (decide (n / 16 = 0)) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have hn64 := C.buf.lt
  have hd := S.data
  have hl := S.len
  obtain ⟨s₁, run₁, hm₁, h12, hbx, h14, hzf, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
        .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .r14 = BitVec.ofNat 64 1 ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, VG.Proof.AesCcm.X86_64.shr4 n hn64]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl,
        VG.Proof.AesCcm.X86_64.shr4 n hn64, VG.Proof.AesCcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨s₁, run₁, ⟨E.keep hg hrd hwr, hrd, hwr, by rw [h12, Nat.mul_zero, BitVec.add_zero],
    by rw [hbx, Nat.sub_zero], h14, Nat.zero_le _, by rw [hm₁]; exact Frame.refl _ _, rfl, by rw [hm₁]⟩, hzf⟩

/-- The whole blocks, in chunks. -/
theorem ctrHead_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) :
    WP isa (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)]) (.ite .e (.block []) (.loop (ctrChunk v.callee) .ne))) s
      (VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n (n / 16)) := by
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctrHeadBlk_ok C E S) fun s₁ ⟨I₀, hzf⟩ => ?_)
  refine WP.ite _ (VG.Proof.AesCcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 := of_decide_eq_true ht
    exact WP.of_runBlock ⟨s₁, rfl, by rw [h0]; exact I₀⟩
  · have h0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = n / 16 - b ∧ b < n / 16 ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n b t) ?_
      (n / 16 - 0) s₁ ⟨0, rfl, by omega, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (VG.Proof.AesCcm.X86_64.chunk_ok v C I hb) fun t' ⟨k, _, hk1, hkb, I', hz⟩ => ?_
    by_cases he : b + k = n / 16
    · left; exact ⟨(VG.Proof.AesCcm.X86_64.eval_ne hz).trans (by simp [he]), by rw [← he]; exact I'⟩
    · right; exact ⟨(VG.Proof.AesCcm.X86_64.eval_ne hz).trans (by simp [he]), n / 16 - (b + k), by omega, b + k, rfl, by omega, I'⟩

/-- The arguments of the call for the last bytes: `Ctr₁₊ₙ/₁₆` and a zero
block at `W + 80`. -/
theorem tailSetup_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP t) {R : Nat} {nonce : List Byte} {j : Nat}
    (hRo : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (hj : j < 256 ^ (15 - nonce.length)) (h14 : t.gpr .r14 = BitVec.ofNat 64 j) :
    ∃ t', runBlock isa (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
        ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++ ([.mov32 .r8 (imm 1)] : List Instr) ++
        ptr .r9 .r15 scrO) t = some t' ∧
      Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce j ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 ∧
      t'.gpr .rdi = K ∧ t'.gpr .rsi = BitVec.ofNat 64 R ∧ t'.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t'.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t'.gpr .r8 = BitVec.ofNat 64 1 ∧ t'.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp, .r12], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have rR := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  obtain ⟨t₁, run₁, hm₁, hsi₁, hax₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .rsi = BitVec.ofNat 64 R ∧ t₁.gpr .rax = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by crun [h15, rR], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hRo]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h14]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  obtain ⟨t₂, run₂, f₂, hc₂, hg₂, hrd₂, hwr₂⟩ := VG.Proof.AesCcm.X86_64.ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) hj hax₁
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP t₂ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have h15₂ := E₂.r15
  have w₁ := E₂.perm.wW (show 80 + 8 ≤ 2560 by decide)
  have w₂ := E₂.perm.wW (show 88 + 8 ≤ 2560 by decide)
  obtain ⟨t₃, run₃, hm₃, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      (zero16 ksO ++ [.mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO) t₂ = some t₃ ∧
      t₃.mem = (t₂.mem.writeW (W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 88) (0 : BitVec 64) ∧
      t₃.gpr .rdi = K ∧ t₃.gpr .rsi = BitVec.ofNat 64 R ∧ t₃.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₃.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t₃.gpr .r8 = BitVec.ofNat 64 1 ∧ t₃.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp, .r12], t₃.gpr r = t.gpr r) ∧ t₃.rd = t.rd ∧ t₃.wr = t.wr := by
    refine ⟨_, by crun [zero16, h15₂, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E₂.r13]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg₂ .rsi (by decide) (by decide) (by decide), hsi₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq] <;>
        rw [hg₂ _ (by decide) (by decide) (by decide), hg₁ _ (by decide) (by decide)]
    · simp only [rd_setReg, rd_arithFlags]; rw [hrd₂, hrd₁]
    · simp only [wr_setReg, wr_arithFlags]; rw [hwr₂, hwr₁]
  have e88 : W + BitVec.ofNat 64 88 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 := by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc]
  have c80 : ∀ d, 80 ≤ d → d + 8 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => Offset.contains W (by omega) (by omega) (by decide)
  refine ⟨t₃, ?_, ?_, ?_, ?_, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩
  · simp only [List.append_assoc]
    rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, VG.Proof.AesCcm.X86_64.runBlock_append, run₂, Option.bind_some]
    simpa only [List.append_assoc] using run₃
  · rw [hm₃, ← hm₁]
    exact ((f₂.sub fun r hr => ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 80 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 88 (by decide) (by decide))
  · have fz : Frame [⟨W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))
    have dz : ∀ r ∈ [(⟨W + BitVec.ofNat 64 80, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame fz dz (by decide), hc₂]
  · rw [hm₃, e88, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

/-- The last `r = n mod 16` bytes, from `t` after the whole blocks, with `r`
in `rbp`. -/
theorem tail_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {t t₀ : State} (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n (n / 16) t)
    (hm₀ : t₀.mem = t.mem) (hg₀ : ∀ r, r ≠ .rbp → t₀.gpr r = t.gpr r)
    (hbp : t₀.gpr .rbp = BitVec.ofNat 64 (n % 16)) (hrd₀ : t₀.rd = t.rd) (hwr₀ : t₀.wr = t.wr) (h0 : n % 16 ≠ 0) :
    WP isa (.seq (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
          ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++
          ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO))
      (.seq (callCtr v.callee)
        (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 ksO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop))) t₀
      fun t' => VG.Proof.AesCcm.X86_64.Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem t'.mem ∧
        bytesAt t'.mem D n = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D n) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  have E₀ : VG.Proof.AesCcm.X86_64.Env K W SP t₀ := I.env.keep (fun r hr => hg₀ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₀ hwr₀
  have hq16 : n / 16 < 256 ^ (15 - nonce.length) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) C.hn
  obtain ⟨t₁, run₁, f₁, hc₁, hz₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ :=
    VG.Proof.AesCcm.X86_64.tailSetup_ok E₀ (by rw [hm₀, C.readW_kept I.frame (by omega), C.ro]) C.h7 C.h13
      (by rw [hm₀, C.bytes_kept I.frame (by omega), C.c0]) (j := 1 + n / 16) (by have := C.hn; omega)
      (by rw [hg₀ _ (by decide), I.r14])
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP t₁ := E₀.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The keystream block.
  have hq := VG.Proof.AesCcm.X86_64.srcW (s := t₁) L E₁.perm (t := 80) (k := 16 * 1) (by decide)
  have hqc : (⟨W + BitVec.ofNat 64 80, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    L.w_w (.inr (by decide)) (by decide) (by decide)
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 80, 16 * 1⟩ := L.k_w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctr_call v (VG.Proof.AesCcm.X86_64.cargs L E₁ C.rounds (c := 64) (by decide) hq hqc hqk
    (E₁.perm.wC (d := 80) (n := 16 * 1) (by decide)) hdi hsi hdx hcx hr8 hr9)) fun t₂ h => ?_)
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP t₂ := E₁.of_saved h.saved h.rd h.wr
  have h15₂ := E₂.r15
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := by rw [h.saved _ (by decide), hg₁ _ (by simp), hbp]
  have h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [h.saved _ (by decide), hg₁ _ (by simp), hg₀ _ (by decide), I.r12]
  obtain ⟨t₃, run₃, hm₃, hdi₃, hsi₃, hcx₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r15 ksO ++ [.mov .rcx (.reg .rbp)]) t₂ = some t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.gpr .rdi = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₃.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₃.gpr .rcx = BitVec.ofNat 64 (n % 16) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t₃.gpr r = t₂.gpr r) ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by crun [h15₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.X86_64.Env K W SP t₃ := E₂.keep hg₃ hrd₃ hwr₃
  have rd₃ : t₃.rd = s.rd := by rw [hrd₃, h.rd, hrd₁, hrd₀, I.rd]
  have wr₃ : t₃.wr = s.wr := by rw [hwr₃, h.wr, hwr₁, hwr₀, I.wr]
  have hS := C.buf.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have lp : LoopPre t₃ (W + BitVec.ofNat 64 80) (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    ⟨hsi₃, hdi₃, hcx₃, by omega, by omega, VG.Proof.AesCcm.X86_64.covers_left (E₃.perm.wC (d := 80) (n := n % 16) (by omega)),
      by rw [wr₃]; exact VG.Proof.AesCcm.X86_64.covers_off C.dw (by omega) hn64, (hS.w.sub_right (Lay.wSub (by omega))).symm⟩
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  -- What the tail wrote.
  have hsp : t₁.gpr .rsp = SP := E₁.rsp
  have cT : Frame [⟨W + BitVec.ofNat 64 64, 32⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8] t.mem t₃.mem := by
    have fc := h.frame
    rw [hsp] at fc
    rw [hm₃, ← hm₀]
    refine (f₁.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  have sep : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8], (⟨D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    have hB := C.buf.slice (a := a) (k := l) hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact (hB.stk.sub_left (VG.Proof.AesCcm.X86_64.below8_sub SP)).symm
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (W + BitVec.ofNat 64 80) (n % 16) :=
    ⟨_, rfl⟩
  rw [← hxs] at hm₄
  have hxl : xs.length = n % 16 := by simp [hxs, xorBytes, VG.Proof.AesCcm.X86_64.length_bytesAt]
  have fw : Frame [⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] t₃.mem t₄.mem := by
    rw [hm₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨E₃.keep (fun r hr => hg₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      hrd₄ hwr₄, by rw [hrd₄, rd₃], by rw [hwr₄, wr₃], ?_, ?_⟩
  · refine I.frame.trans ((cT.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below SP 16, by simp, VG.Proof.AesCcm.X86_64.below8_sub SP⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
  · -- The bytes.
    have h₁ : bytesAt t₃.mem D (16 * (n / 16)) = bytesAt t.mem D (16 * (n / 16)) := by
      have := VG.Proof.AesCcm.X86_64.bytesAt_frame cT (sep (a := 0) (l := 16 * (n / 16)) (by omega)) (by omega)
      rwa [BitVec.add_zero] at this
    have h₂ : bytesAt t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
      rw [VG.Proof.AesCcm.X86_64.bytesAt_frame cT (sep (by omega)) (by omega), show n % 16 = n - 16 * (n / 16) by omega, I.rest]
    have f₁' : Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem t₁.mem := I.frame.trans (by
      rw [← hm₀]; exact f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩)
    have hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem K R) := fun x => Proof.Cmac.aesWith_length _ _ x
    have hks : bytesAt t₃.mem (W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem K R (Spec.Ccm.ctrBlock nonce (1 + n / 16)) := by
      have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + n / 16) (by have := C.h13; omega) (fun i hi => by
        rw [show i = 0 by omega, Nat.add_zero]
        show Spec.Gcm.ofBytes _ = _
        rw [hc₁]) h.out
      rw [Nat.mul_one] at hx
      rw [hm₃, hx, hz₁, C.ciph_kept f₁', xorFrom_zeros hBC]
    have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem K R) nonce (1 + n / 16)
      (d := bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; omega)
    rw [VG.Proof.AesCcm.X86_64.length_bytesAt, hBC] at ht
    have ht' := ht.resolve_right (by omega)
    rw [hm₄, VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at t₃.mem D xs (by rw [hxl]; omega) hn64,
      List.drop_eq_nil_of_le (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt, hxl]; omega), List.append_nil,
      ← VG.Proof.AesCcm.X86_64.bytesAt_prefix t₃.mem D (show 16 * (n / 16) ≤ n by omega), h₁, I.done, hxs, xorBytes, h₂,
      VG.Proof.AesCcm.X86_64.bytesAt_prefix t₃.mem (W + BitVec.ofNat 64 80) (show n % 16 ≤ 16 by omega), hks, ht']
    conv => rhs; rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
    rw [Proof.Cmac.Stream.bytesAt_append, xorFrom_append _ _ _ (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _), Nat.add_comm 1 (n / 16)]

/-- `rbp = n mod 16`, and ZF set when there are no last bytes. -/
theorem ctrB3_ok {K W SP : Addr} {t : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP t) {n : Nat}
    (hl : t.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n) (hn64 : n < 2 ^ 64) :
    WP isa (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .and .rbp (imm 15), .alu .test .rbp (.reg .rbp)]) t
      fun t₀ => t₀.mem = t.mem ∧ t₀.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
        (∀ r, r ≠ .rbp → t₀.gpr r = t.gpr r) ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr := by
  have h15 := E.r15
  have rl := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  refine WP.of_runBlock ⟨_, by crun [h15, rl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, VG.Proof.AesCcm.X86_64.and15',
      VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hn64]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, VG.Proof.AesCcm.X86_64.and15',
      VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hn64, VG.Proof.AesCcm.X86_64.and_self_beq (show n % 16 < 2 ^ 64 by omega)]
  · intro r h₁; simp only [gpr_setReg, gpr_arithFlags, h₁, ite_false]
  all_goals rfl

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) :
    WP isa (ctr v.callee) s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D n) := by
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine VG.Proof.AesCcm.X86_64.seq_assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctrHead_ok v C E S) fun t I => ?_))
  have hl : t.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by
    rw [C.readW_kept I.frame (by omega)]; exact S.len
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctrB3_ok I.env hl hn64) fun t₀ ⟨hm₀, hbp, hzf, hg₀, hrd₀, hwr₀⟩ => ?_)
  refine WP.ite _ (VG.Proof.AesCcm.X86_64.eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨t₀, rfl, I.env.keep (fun r hr => hg₀ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      hrd₀ hwr₀, by rw [hrd₀, I.rd], by rw [hwr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (n / 16) = n by omega] at hd
    rw [hm₀, hd]
  · exact VG.Proof.AesCcm.X86_64.tail_ok v C I hm₀ hg₀ hbp hrd₀ hwr₀ (of_decide_eq_false hf)

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Mac`. -/
section

/-!
# AES-CCM on x86-64: the MAC (`mac y`)

Untrusted: everything here is checked by Lean. `mac y` chains `B₀`, the
formatted associated data and the payload padded into the MAC state at
`W + y`, from a zero block: CBC-MAC of the formatted blocks (`mac_ok`), whose
first `t` bytes are CCM's MAC (`Proof.AesCcm.mac_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : VG.Proof.AesCcm.X86_64.Buf K W SP s A al) (hD : VG.Proof.AesCcm.X86_64.Buf K W SP s D n) :
    WP isa (mac v.callee v.suffix y) s (@VG.Proof.AesCcm.X86_64.MacStep K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem A al) (bytesAt s.mem D n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.b0_ok v L E S hR hnl h7 h13 ht4 ht16 hte hA.lt hn hc0 hy)
    fun s₁ ⟨E₁, f₁, h₁, hrd₁, hwr₁⟩ => ?_)
  -- The slots, which the pieces of the MAC keep.
  have kept : ∀ {m m' : Mem}, Frame (VG.Proof.AesCcm.X86_64.macR W SP y) m m' → VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl m → VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl m' :=
    fun hf hs => by
      have k : ∀ d, 160 ≤ d → d + 8 ≤ 240 → _ := fun d h₁ h₂ =>
        hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rcases hy with rfl | rfl
            · exact L.w_w (.inr (by omega)) (by omega) (by decide)
            · exact L.w_w (.inr (by omega)) (by omega) (by decide)
          · exact L.w_w (.inr (by omega)) (by omega) (by decide)
          · exact L.w_w (.inl (by omega)) (by omega) (by decide)
          · exact (L.stk_w' (by omega)).symm) (by decide)
      exact ⟨by rw [k 232 (by decide) (by decide)]; exact hs.rounds, by rw [k 160 (by decide) (by decide)]; exact hs.nonce,
        by rw [k 168 (by decide) (by decide)]; exact hs.nlen, by rw [k 176 (by decide) (by decide)]; exact hs.aad,
        by rw [k 184 (by decide) (by decide)]; exact hs.alen, by rw [k 192 (by decide) (by decide)]; exact hs.data,
        by rw [k 200 (by decide) (by decide)]; exact hs.len, by rw [k 208 (by decide) (by decide)]; exact hs.tl⟩
  have S₁ := kept f₁ S
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.aad_ok v L E₁ S₁ hR hy (hA.of_eq hrd₁ hwr₁)) fun s₂ M₂ => ?_)
  have S₂ := kept M₂.frame S₁
  have E₂ := M₂.env
  have h15 := E₂.r15
  have r₁ := E₂.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E₂.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have hd₂ := S₂.data
  have hl₂ := S₂.len
  obtain ⟨s₃, run₃, hm₃, h12, hbp, hg₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] s₂ = some s₃ ∧
      s₃.mem = s₂.mem ∧ s₃.gpr .r12 = D ∧ s₃.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hd₂]
    · simp [gpr_setReg, hl₂]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesCcm.X86_64.Env K W SP s₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hRo₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [hm₃]; exact S₂.rounds
  have rd₃ : s₃.rd = s.rd := by rw [hrd₃, M₂.rd, hrd₁]
  have wr₃ : s₃.wr = s.wr := by rw [hwr₃, M₂.wr, hwr₁]
  refine WP.mono (VG.Proof.AesCcm.X86_64.absorbPad_ok v L E₃ hR hRo₃ hy (hD.of_eq rd₃ wr₃) h12 hbp) fun s₄ A₄ => ?_
  have f₃ : Frame (VG.Proof.AesCcm.X86_64.macR W SP y) s.mem s₃.mem := by rw [hm₃]; exact f₁.trans M₂.frame
  have hk := VG.Proof.AesCcm.X86_64.k_macR L hy16
  refine ⟨A₄.env, f₃.trans A₄.frame, ?_, by rw [A₄.rd, rd₃], by rw [A₄.wr, wr₃]⟩
  have hl : nonce.length ≤ 15 := by omega
  have f₂ : Frame (VG.Proof.AesCcm.X86_64.macR W SP y) s.mem s₂.mem := f₁.trans M₂.frame
  rw [A₄.out, hm₃, M₂.out, h₁, VG.Proof.AesCcm.X86_64.ctxCiph_frame f₂ hk hRb, VG.Proof.AesCcm.X86_64.ctxCiph_frame f₁ hk hRb, VG.Proof.AesCcm.X86_64.buf_kept hD hy16 f₂,
    VG.Proof.AesCcm.X86_64.buf_kept hA hy16 f₁, format_eq tl hl, VG.Proof.AesCcm.X86_64.length_bytesAt, VG.Proof.AesCcm.X86_64.length_bytesAt, Proof.Cmac.chain_append,
    Proof.Cmac.chain_append]

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.MacCT`. -/
section

/-!
# AES-CCM on x86-64: the MAC is constant time

Untrusted: everything here is checked by Lean. The code between the calls
of `vg_cmac_aes_update` passes the taint analysis from the public slots and
registers (`rel_taintC`); each call has the same arguments in both runs, by
correctness (`upd_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop minLen)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs upd_rel)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks)
open VG.WriteBytes

/-! ## `updBlock` -/

/-- The arguments of `updBlock`'s call. -/
theorem updArgsBlk_ok {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (updArgs y ++ ptr .rcx .r15 bO ++ ([.mov32 .r8 (imm 1)] : List Instr))) s fun s₁ =>
      UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP := by
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rdi = K ∧ s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₁.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s₁.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₁.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, VG.Proof.AesCcm.X86_64.imm_eq hy']
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep hg₁ hrd₁ hwr₁
  have hq := VG.Proof.AesCcm.X86_64.srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨W + BitVec.ofNat 64 32, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  exact WP.of_runBlock ⟨s₁, run₁, VG.Proof.AesCcm.X86_64.uargs L E₁ hR (by omega) hq hqy (by decide) hdi hsi hdx hcx hr8 hr9, E₁.rsp⟩

theorem updArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT []) (.block (updArgs y ++ ptr .rcx .r15 bO ++ ([.mov32 .r8 (imm 1)] : List Instr))) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `updBlock y` in two runs. -/
theorem updBlock_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl [] s₁ s₂) :
    RelCT isa P (updBlock v.callee v.suffix y) fun _ _ => True := by
  have a := (VG.Proof.AesCcm.X86_64.rel_taintC [] hDW hn hP (c := .block (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]))
    (VG.Proof.AesCcm.X86_64.updArgs_check hy)).wp
    (F₁ := fun (s₁ : State) => UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP)
    (F₂ := fun (s₁ : State) => UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP)
    fun s₁ s₂ (h : P s₁ s₂) => ⟨VG.Proof.AesCcm.X86_64.updArgsBlk_ok L (hP _ _ h).e₁ hR (hP _ _ h).sl₁.rounds hy,
      VG.Proof.AesCcm.X86_64.updArgsBlk_ok L (hP _ _ h).e₂ hR (hP _ _ h).sl₂.rounds hy⟩
  exact RelCT.seq a (upd_rel v _ fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

/-! ## `b0` -/

/-- A run whose `W + 48` holds `Ctr₀` for some nonce of `nl` bytes. -/
def C0 (W : Addr) (nl : Nat) (s : State) : Prop :=
  ∃ nonce : List Byte, nonce.length = nl ∧ bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Pre_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT []) (.seq (.block [.mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .mov32 .rcx (imm 14),
        .alu .sub .rcx (.mem (at_ .r15 nlenO)), .alu .add .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 alenO)),
        .alu .test .rcx (.reg .rcx)])
      (.seq (.ite .e (.block []) (.block [.alu .add .rax (imm 64)]))
      (.block (([.mov .rcx (.mem (at_ .r15 c0O)), .mov .rdx (.mem (at_ .r15 (c0O + 8))),
        .mov .rsi (.mem (at_ .r15 lenO)), .store (at_ .r15 bO) .rcx, .store8 (at_ .r15 bO) .rax, .bswap .rsi,
        .alu .or .rsi (.reg .rdx), .store (at_ .r15 (bO + 8)) .rsi] : List Instr) ++ zero16 y)))) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- Both runs, after a frame within what the pieces write. -/
theorem Both.frame {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} (L : VG.Proof.AesCcm.X86_64.Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s₁ s₂ s₁' s₂' : State}
    (h : VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl [] s₁ s₂) (E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁') (E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂')
    (hrd₁ : s₁'.wr = s₁.wr) (hrd₂ : s₂'.wr = s₂.wr)
    (f₁ : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s₁.mem s₁'.mem) (f₂ : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s₂.mem s₂'.mem) :
    VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl [] s₁' s₂' :=
  ⟨E₁, E₂, VG.Proof.AesCcm.X86_64.slots_mut L hDW f₁ h.sl₁, VG.Proof.AesCcm.X86_64.slots_mut L hDW f₂ h.sl₂, hrd₁.trans h.wr₁, hrd₂.trans h.wr₂,
    fun _ h => nomatch h⟩

/-- `b0 y` in two runs. -/
theorem b0_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64)
    (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl [] s₁ s₂ ∧ VG.Proof.AesCcm.X86_64.C0 W nl s₁ ∧ VG.Proof.AesCcm.X86_64.C0 W nl s₂) :
    RelCT isa P (b0 v.callee v.suffix y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega
  have pre : ∀ s, VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl [] s s → VG.Proof.AesCcm.X86_64.C0 W nl s → WP isa _ s fun s' =>
      VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem := fun s hb ⟨nonce, hl, hc⟩ =>
    WP.mono (VG.Proof.AesCcm.X86_64.b0Pre_ok L hb.e₁ hb.sl₁ hl h7 h13 ht4 ht16 hte hal hn' hc hy) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hB : ∀ s₁ s₂, P s₁ s₂ → ∀ s, (s = s₁ ∨ s = s₂) → VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl [] s s ∧ VG.Proof.AesCcm.X86_64.C0 W nl s :=
    fun s₁ s₂ h s hs => by
      obtain ⟨b, c₁, c₂⟩ := hP _ _ h
      rcases hs with rfl | rfl
      · exact ⟨⟨b.e₁, b.e₁, b.sl₁, b.sl₁, b.wr₁, b.wr₁, fun _ h => nomatch h⟩, c₁⟩
      · exact ⟨⟨b.e₂, b.e₂, b.sl₂, b.sl₂, b.wr₂, b.wr₂, fun _ h => nomatch h⟩, c₂⟩
  have a := (VG.Proof.AesCcm.X86_64.rel_taintC [] hDW hn (fun s₁ s₂ h => (hP s₁ s₂ h).1) (VG.Proof.AesCcm.X86_64.b0Pre_check hy)).wpDep
    (F := fun (s s' : State) => VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl [] s s ∧ VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem)
    fun s₁ s₂ (h : P s₁ s₂) => ⟨WP.mono (pre s₁ (hB _ _ h s₁ (.inl rfl)).1 (hB _ _ h s₁ (.inl rfl)).2) fun _ q =>
        ⟨(hB _ _ h s₁ (.inl rfl)).1, q⟩,
      WP.mono (pre s₂ (hB _ _ h s₂ (.inr rfl)).1 (hB _ _ h s₂ (.inr rfl)).2) fun _ q =>
        ⟨(hB _ _ h s₂ (.inr rfl)).1, q⟩⟩
  refine VG.Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq a (VG.Proof.AesCcm.X86_64.updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁' s₂' h => ?_))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨b₁, E₁, -, w₁, f₁⟩, ⟨b₂, E₂, -, w₂, f₂⟩⟩ := h
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region), ⟨W + BitVec.ofNat 64 y, 16⟩],
      ∃ r' ∈ VG.Proof.AesCcm.X86_64.mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W hy16⟩
  exact ⟨E₁, E₂, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₁.sub hm) b₁.sl₁, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₂.sub hm) b₂.sl₁, w₁.trans b₁.wr₁,
    w₂.trans b₂.wr₁, fun _ h => nomatch h⟩

/-! ## `absorbPad` -/

theorem absorbW1_ok {s : State} {len : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 len) (hl : len < 2 ^ 64) :
    WP isa (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)]) s fun s₁ =>
      s₁.mem = s.mem ∧ s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hbp, VG.Proof.AesCcm.X86_64.shr4 len hl]
  · intro r a; simp [gpr_setReg, gpr_setFlags, a]
  all_goals rfl

theorem absorbWArgs_ok {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 (len / 16)) :
    WP isa (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) s fun s₂ =>
      UArgs s₂ K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧ s₂.gpr .rsp = SP := by
  have hl := hP.lt
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega
  obtain ⟨s₂, run₂, hdi, hsi, hdx, hcx, hr8₂, hr9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      (updArgs y ++ [.mov .rcx (.reg .r12)]) s = some s₂ ∧
      s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₂.gpr .rcx = P ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, VG.Proof.AesCcm.X86_64.imm_eq hy']
    · simp [gpr_setReg, h12]
    · simp [gpr_setReg, h8]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E.keep hg₂ hrd₂ hwr₂
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hq := VG.Proof.AesCcm.X86_64.srcBuf ((hP.take hb).of_eq (s' := s₂) hrd₂ hwr₂)
  have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ :=
    (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega))
  exact WP.of_runBlock ⟨s₂, run₂, VG.Proof.AesCcm.X86_64.uargs L E₂ hR (by omega) hq hqy (by omega) hdi hsi hdx hcx hr8₂ hr9, E₂.rsp⟩

theorem absorbT1_ok {s : State} {len : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 len) (hl : len < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)]) s fun s₁ =>
      s₁.mem = s.mem ∧ s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.zf = some (decide (len % 16 = 0)) := by
  refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hbp, VG.Proof.AesCcm.X86_64.and15', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hl]
  · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
  · rfl
  · rfl
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, hbp, VG.Proof.AesCcm.X86_64.and15', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hl,
      VG.Proof.AesCcm.X86_64.and_self_beq (show len % 16 < 2 ^ 64 by omega)]

theorem absorbT2_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {P : Addr} {len : Nat}
    (hP : VG.Proof.AesCcm.X86_64.Buf K W SP s P len) (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    WP isa (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
        ptr .rdi .r15 bO)) copyLoop) s fun s' =>
      VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hl := hP.lt
  have h15 := E.r15
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, hsi, hdi, hcx₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
        ptr .rdi .r15 bO) s = some s₂ ∧
      s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧
      s₂.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) ∧ s₂.gpr .rdi = W + BitVec.ofNat 64 32 ∧
      s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by crun [zero16, h15, w₁, w₂, VG.Proof.AesCcm.X86_64.add_ofNat_assoc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp, h12, hcx]
      rw [VG.Proof.AesCcm.X86_64.ofNat_sub (by omega) hl, BitVec.add_comm, show len - len % 16 = 16 * (len / 16) by omega]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hcx]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesCcm.X86_64.Env K W SP s₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega)).of_eq (s' := s₂) hrd₂ hwr₂
  have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (W + BitVec.ofNat 64 32) (len % 16) :=
    ⟨hsi, hdi, hcx₂, by omega, by omega, hT.rd, E₂.perm.wC (by omega), hT.w.sub_right (Lay.wSub (by omega))⟩
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ⟨E₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃, ?_,
    by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂]⟩
  have fZ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains W (d := 32) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains W (d := 40) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))
  refine fZ.trans ?_
  rw [hm₃]
  exact writeBytes_frame _ _ _ (by
    rw [VG.Proof.AesCcm.X86_64.length_bytesAt]
    exact Offset.contains W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega) (by decide))

/-- What a run of `absorbPad` needs: the `len` bytes at `P` in `r12`, `rbp`. -/
structure AbsPre (K W SP : Addr) (P : Addr) (len : Nat) (s : State) : Prop where
  buf : VG.Proof.AesCcm.X86_64.Buf K W SP s P len
  r12 : s.gpr .r12 = P
  rbp : s.gpr .rbp = BitVec.ofNat 64 len

theorem absW1_check : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmT [.r12, .rbp])
    (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)]) hc).map (·.flags)) = some true :=
  ⟨_, by taint_decide⟩

theorem absWArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [.r12, .r8]) (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The whole blocks, in two runs. -/
theorem absorbWhole_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧
      VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₂) :
    RelCT isa Q (.seq (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)])
      (.ite .e (.block []) (.seq (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) (callUpdate v.callee v.suffix))))
      fun _ _ => True := by
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_flagsC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (VG.Proof.AesCcm.X86_64.agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) VG.Proof.AesCcm.X86_64.absW1_check).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ ∧
      (s'.mem = σ.mem ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ (h : Q s₁ s₂) => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.absorbW1_ok a₁.rbp a₁.buf.lt) fun _ q => ⟨o₁, a₁, q⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.absorbW1_ok a₂.rbp a₂.buf.lt) fun _ q => ⟨o₂, a₂, q⟩⟩
  -- After the first block, in each run.
  have after : ∀ σ s', VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ → VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ →
      (s'.mem = σ.mem ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr) →
      VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s' ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s' ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) :=
    fun σ s' o a ⟨hm, h8, hg, hrd, hwr⟩ =>
      ⟨⟨o.env.keep (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
          hrd hwr, hm ▸ o.sl, hwr.trans o.wr⟩,
        ⟨a.buf.of_eq hrd hwr, by rw [hg _ (by decide), a.r12], by rw [hg _ (by decide), a.rbp]⟩, h8⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => VG.Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ₁ ∧ (s₁.mem = σ₁.mem ∧
        s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧
        s₁.wr = σ₁.wr)) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ₂ ∧ (s₂.mem = σ₂.mem ∧
        s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧
        s₂.wr = σ₂.wr))) ∧ isa.eval .e s₁ = some false →
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₁ ∧ s₁.gpr .r8 = BitVec.ofNat 64 (len / 16)) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₂ ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16)) :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, a₁, q₁⟩, ⟨o₂, a₂, q₂⟩⟩, _⟩ => ⟨after σ₁ s₁ o₁ a₁ q₁, after σ₂ s₂ o₂ a₂ q₂⟩
  have r₂ := (VG.Proof.AesCcm.X86_64.rel_taintC [.r12, .r8] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩⟩ := hA s₁ s₂ h
    exact Both.of o₁ o₂ (VG.Proof.AesCcm.X86_64.agree_of (l := [(.r12, P), (.r8, BitVec.ofNat 64 (len / 16))])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact h₁)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact h₂))) (VG.Proof.AesCcm.X86_64.absWArgs_check hy)).wp
    (F₁ := fun (s : State) => UArgs s K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧
      s.gpr .rsp = SP)
    (F₂ := fun (s : State) => UArgs s K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧
      s.gpr .rsp = SP)
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩⟩ := hA s₁ s₂ h
      exact ⟨VG.Proof.AesCcm.X86_64.absorbWArgs_ok L o₁.env hR o₁.sl.rounds hy a₁.buf a₁.r12 h₁,
        VG.Proof.AesCcm.X86_64.absorbWArgs_ok L o₂.env hR o₂.sl.rounds hy a₂.buf a₂.r12 h₂⟩
  exact RelCT.seq r₂ (upd_rel v _ fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

theorem absT1_check : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmT [.r12, .rbp])
    (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)]) hc).map (·.flags)) =
      some true := ⟨_, by taint_decide⟩

theorem absT2_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [.rcx, .r12, .rbp])
    (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
      ptr .rdi .r15 bO)) copyLoop) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The last bytes, in two runs. -/
theorem absorbTail_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧
      VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₂) :
    RelCT isa Q (.seq (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block [])
          (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
              ptr .rdi .r15 bO))
            (.seq copyLoop (updBlock v.callee v.suffix y)))))
      fun _ _ => True := by
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_flagsC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (VG.Proof.AesCcm.X86_64.agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) VG.Proof.AesCcm.X86_64.absT1_check).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ ∧
      (s'.mem = σ.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ s'.zf = some (decide (len % 16 = 0))))
    fun s₁ s₂ (h : Q s₁ s₂) => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.absorbT1_ok a₁.rbp a₁.buf.lt) fun _ q => ⟨o₁, a₁, q⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.absorbT1_ok a₂.rbp a₂.buf.lt) fun _ q => ⟨o₂, a₂, q⟩⟩
  have after : ∀ σ s', VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ → VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ →
      (s'.mem = σ.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ s'.zf = some (decide (len % 16 = 0))) →
      VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s' ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s' ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) :=
    fun σ s' o a ⟨hm, hc, hg, hrd, hwr, _⟩ =>
      ⟨⟨o.env.keep (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
          hrd hwr, hm ▸ o.sl, hwr.trans o.wr⟩,
        ⟨a.buf.of_eq hrd hwr, by rw [hg _ (by decide), a.r12], by rw [hg _ (by decide), a.rbp]⟩, hc⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => VG.Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ₁ ∧ (s₁.mem = σ₁.mem ∧
        s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧
        s₁.wr = σ₁.wr ∧ s₁.zf = some (decide (len % 16 = 0)))) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ₂ ∧ (s₂.mem = σ₂.mem ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧
        s₂.wr = σ₂.wr ∧ s₂.zf = some (decide (len % 16 = 0))))) ∧ isa.eval .e s₁ = some false →
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (len % 16)) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₂ ∧ s₂.gpr .rcx = BitVec.ofNat 64 (len % 16)) ∧
      len % 16 ≠ 0 :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, a₁, q₁⟩, ⟨o₂, a₂, q₂⟩⟩, he⟩ => by
      refine ⟨after σ₁ s₁ o₁ a₁ q₁, after σ₂ s₂ o₂ a₂ q₂, fun h0 => ?_⟩
      rw [show isa.eval .e s₁ = s₁.zf from rfl, q₁.2.2.2.2.2, h0] at he; cases he
  have r₂ := (VG.Proof.AesCcm.X86_64.rel_taintC [.rcx, .r12, .rbp] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩, -⟩ := hA s₁ s₂ h
    exact Both.of o₁ o₂ (VG.Proof.AesCcm.X86_64.agree_of (l := [(.rcx, BitVec.ofNat 64 (len % 16)), (.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl
                      · exact h₁
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl
                      · exact h₂
                      · exact a₂.r12
                      · exact a₂.rbp))) VG.Proof.AesCcm.X86_64.absT2_check).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧
      (VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] σ.mem s'.mem ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩, h0⟩ := hA s₁ s₂ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.absorbT2_ok o₁.env a₁.buf a₁.r12 a₁.rbp h₁ h0) fun _ q => ⟨o₁, q⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.absorbT2_ok o₂.env a₂.buf a₂.r12 a₂.rbp h₂ h0) fun _ q => ⟨o₂, q⟩⟩
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], ∃ r' ∈ VG.Proof.AesCcm.X86_64.mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  refine VG.Proof.AesCcm.X86_64.rel_assoc (RelCT.seq r₂ (VG.Proof.AesCcm.X86_64.updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, E₁, f₁, -, w₁⟩, ⟨o₂, E₂, f₂, -, w₂⟩⟩ := h
  exact ⟨E₁, E₂, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₁.sub hm) o₁.sl, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₂.sub hm) o₂.sl, w₁.trans o₁.wr,
    w₂.trans o₂.wr, fun _ h => nomatch h⟩

/-- What the pieces of the MAC write, within what the pieces may write. -/
theorem macR_mut (W SP D : Addr) (n : Nat) {y : Nat} (hy : y + 16 ≤ 112) :
    ∀ r ∈ VG.Proof.AesCcm.X86_64.macR W SP y, ∃ r' ∈ VG.Proof.AesCcm.X86_64.mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W hy⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- After a piece of the MAC, the public facts of a run. -/
theorem One.macR {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} (L : VG.Proof.AesCcm.X86_64.Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {y : Nat} (hy : y + 16 ≤ 112) {s s' : State}
    (o : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s) (E : VG.Proof.AesCcm.X86_64.Env K W SP s') (hf : Frame (VG.Proof.AesCcm.X86_64.macR W SP y) s.mem s'.mem)
    (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s' :=
  ⟨E, VG.Proof.AesCcm.X86_64.slots_mut L hDW (hf.sub (VG.Proof.AesCcm.X86_64.macR_mut W SP D n hy)) o.sl, hwr.trans o.wr⟩

/-- `absorbPad y` in two runs. -/
theorem absorbPad_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧
      VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len s₂) :
    RelCT isa Q (absorbPad v.callee v.suffix y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega
  have r₁ := (VG.Proof.AesCcm.X86_64.absorbWhole_rel v L hR hDW hn hy hQ).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P len σ ∧
      ∃ Y, @VG.Proof.AesCcm.X86_64.Absorbed K W SP σ y P len Y s')
    fun s₁ s₂ h => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.absorbWhole_ok v L o₁.env hR o₁.sl.rounds hy a₁.buf a₁.r12 a₁.rbp) fun _ q => ⟨o₁, a₁, _, q⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.absorbWhole_ok v L o₂.env hR o₂.sl.rounds hy a₂.buf a₂.r12 a₂.rbp) fun _ q => ⟨o₂, a₂, _, q⟩⟩
  refine VG.Proof.AesCcm.X86_64.rel_assoc (RelCT.seq r₁ (VG.Proof.AesCcm.X86_64.absorbTail_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al)
    (tl := tl) (P := P) (len := len) fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, a₁, _, A₁⟩, ⟨o₂, a₂, _, A₂⟩⟩ := h
  exact ⟨o₁.macR L hDW hy16 A₁.env A₁.frame A₁.wr, o₂.macR L hDW hy16 A₂.env A₂.frame A₂.wr,
    ⟨a₁.buf.of_eq A₁.rd A₁.wr, A₁.r12, A₁.rbp⟩, ⟨a₂.buf.of_eq A₂.rd A₂.wr, A₂.r12, A₂.rbp⟩⟩

/-! ## `aad` -/

theorem aadHeadPre_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [.r12, .rbp]) (.seq header (.seq minLen
    (.seq (.block [.mov .rsi (.reg .r12), .mov .rdi (.reg .r15), .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm bO),
      .alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)]) copyLoop))) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The first block of the associated data, in two runs. -/
theorem aadHead_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {a : Nat} (ha0 : 0 < a) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧
      VG.Proof.AesCcm.X86_64.AbsPre K W SP P a s₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP P a s₂) :
    RelCT isa Q (aadHead v.callee v.suffix y) fun _ _ => True := by
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_taintC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (VG.Proof.AesCcm.X86_64.agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 a)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) VG.Proof.AesCcm.X86_64.aadHeadPre_check).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧
      (VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] σ.mem s'.mem))
    fun s₁ s₂ h => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.aadHeadPre_ok o₁.env a₁.buf ha0 a₁.r12 a₁.rbp) fun _ q => ⟨o₁, q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.aadHeadPre_ok o₂.env a₂.buf ha0 a₂.r12 a₂.rbp) fun _ q => ⟨o₂, q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩⟩
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], ∃ r' ∈ VG.Proof.AesCcm.X86_64.mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  refine VG.Proof.AesCcm.X86_64.rel_assoc4 (RelCT.seq r₁ (VG.Proof.AesCcm.X86_64.updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, E₁, -, w₁, f₁⟩, ⟨o₂, E₂, -, w₂, f₂⟩⟩ := h
  exact ⟨E₁, E₂, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₁.sub hm) o₁.sl, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₂.sub hm) o₂.sl, w₁.trans o₁.wr,
    w₂.trans o₂.wr, fun _ h => nomatch h⟩

theorem aadBlk_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (ha : al < 2 ^ 64) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .alu .test .rbp (.reg .rbp)])
      s fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧
        s₁.zf = some (decide (al = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧
        s₁.wr = s.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hAp := S.aad
  have hal := S.alen
  refine WP.of_runBlock ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, gpr_arithFlags, hAp]
  · simp [gpr_setReg, gpr_arithFlags, hal]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hal, VG.Proof.AesCcm.X86_64.and_self_beq ha]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals rfl

theorem aadBlk_check : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmT [])
    (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .alu .test .rbp (.reg .rbp)])
    hc).map (·.flags)) = some true := ⟨_, by taint_decide⟩

/-- The associated data, in two runs. -/
theorem aad_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧
      VG.Proof.AesCcm.X86_64.Buf K W SP s₁ A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₂ A al) :
    RelCT isa Q (aad v.callee v.suffix y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_flagsC [] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, -, -⟩ := hQ _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) VG.Proof.AesCcm.X86_64.aadBlk_check).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ A al ∧
      (s'.mem = σ.mem ∧ s'.gpr .r12 = A ∧ s'.gpr .rbp = BitVec.ofNat 64 al ∧
        s'.zf = some (decide (al = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s'.gpr r = σ.gpr r) ∧ s'.rd = σ.rd ∧
        s'.wr = σ.wr))
    fun s₁ s₂ h => by
      obtain ⟨o₁, o₂, b₁, b₂⟩ := hQ _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.aadBlk_ok o₁.env o₁.sl b₁.lt) fun _ q => ⟨o₁, b₁, q⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.aadBlk_ok o₂.env o₂.sl b₂.lt) fun _ q => ⟨o₂, b₂, q⟩⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => VG.Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The associated data is not empty.
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₁ A al ∧ (s₁.mem = σ₁.mem ∧ s₁.gpr .r12 = A ∧
        s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.zf = some (decide (al = 0)) ∧
        (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧ s₁.wr = σ₁.wr)) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₂ A al ∧ (s₂.mem = σ₂.mem ∧ s₂.gpr .r12 = A ∧
        s₂.gpr .rbp = BitVec.ofNat 64 al ∧ s₂.zf = some (decide (al = 0)) ∧
        (∀ r ∈ [Reg.r13, .r15, .rsp], s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧ s₂.wr = σ₂.wr))) ∧
      isa.eval .e s₁ = some false →
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP A al s₁) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP A al s₂) ∧ 0 < al :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, b₁, m₁, h₁, p₁, z₁, g₁, rd₁, wr₁⟩, ⟨o₂, b₂, m₂, h₂, p₂, _, g₂, rd₂, wr₂⟩⟩, he⟩ => by
      refine ⟨⟨⟨o₁.env.keep g₁ rd₁ wr₁, m₁ ▸ o₁.sl, wr₁.trans o₁.wr⟩, ⟨b₁.of_eq rd₁ wr₁, h₁, p₁⟩⟩,
        ⟨⟨o₂.env.keep g₂ rd₂ wr₂, m₂ ▸ o₂.sl, wr₂.trans o₂.wr⟩, ⟨b₂.of_eq rd₂ wr₂, h₂, p₂⟩⟩, ?_⟩
      rcases Nat.eq_zero_or_pos al with h0 | h0
      · rw [show isa.eval .e s₁ = s₁.zf from rfl, z₁, h0] at he; cases he
      · exact h0
  rcases Nat.eq_zero_or_pos al with h0 | h0
  · exact RelCT.of_false fun s₁ s₂ h => by have := (hA s₁ s₂ h).2.2; omega
  have hl : headLen al ≤ al := by unfold headLen; have := Proof.AesCcm.hdrLen_le al; omega
  have r₂ := (VG.Proof.AesCcm.X86_64.aadHead_rel v L hR hDW hn hy h0 (P := A) (A := A) (N := N) (nl := nl) (tl := tl)
    fun s₁ s₂ h => by obtain ⟨⟨o₁, a₁⟩, ⟨o₂, a₂⟩, -⟩ := hA s₁ s₂ h; exact ⟨o₁, o₂, a₁, a₂⟩).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.AbsPre K W SP A al σ ∧
      ∃ Y, @VG.Proof.AesCcm.X86_64.Absorbed K W SP σ y (A + BitVec.ofNat 64 (headLen al)) (al - headLen al) Y s')
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁⟩, ⟨o₂, a₂⟩, -⟩ := hA s₁ s₂ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.aadHead_ok v L o₁.env hR o₁.sl.rounds hy a₁.buf h0 a₁.r12 a₁.rbp) fun _ q => ⟨o₁, a₁, _, q⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.aadHead_ok v L o₂.env hR o₂.sl.rounds hy a₂.buf h0 a₂.r12 a₂.rbp) fun _ q => ⟨o₂, a₂, _, q⟩⟩
  refine RelCT.seq r₂ (VG.Proof.AesCcm.X86_64.absorbPad_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := A + BitVec.ofNat 64 (headLen al)) (len := al - headLen al)
    fun s₁ s₂ h => ?_)
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, a₁, _, A₁⟩, ⟨o₂, a₂, _, A₂⟩⟩ := h
  exact ⟨o₁.macR L hDW hy16 A₁.env A₁.frame A₁.wr, o₂.macR L hDW hy16 A₂.env A₂.frame A₂.wr,
    ⟨(a₁.buf.drop hl).of_eq A₁.rd A₁.wr, A₁.r12, A₁.rbp⟩, ⟨(a₂.buf.drop hl).of_eq A₂.rd A₂.wr, A₂.r12, A₂.rbp⟩⟩

/-! ## `mac` and `tag` -/

theorem macBlk_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) s fun s₃ =>
      s₃.mem = s.mem ∧ s₃.gpr .r12 = D ∧ s₃.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have hd := S.data
  have hl := S.len
  refine WP.of_runBlock ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hd]
  · simp [gpr_setReg, hl]
  · intro r a b; simp [gpr_setReg, a, b]
  all_goals rfl

theorem macBlk_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The MAC, in two runs. -/
theorem mac_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64)
    (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.C0 W nl s₁ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₁ A al ∧
      VG.Proof.AesCcm.X86_64.Buf K W SP s₁ D n) ∧ (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ VG.Proof.AesCcm.X86_64.C0 W nl s₂ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₂ A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₂ D n)) :
    RelCT isa Q (mac v.callee v.suffix y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega
  have r₁ := (VG.Proof.AesCcm.X86_64.b0_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' hy (P := Q) fun s₁ s₂ h => by
    obtain ⟨⟨o₁, c₁, -⟩, ⟨o₂, c₂, -⟩⟩ := hQ _ _ h
    exact ⟨Both.of o₁ o₂ (fun _ h => nomatch h), c₁, c₂⟩).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ D n ∧
      (VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ Frame (VG.Proof.AesCcm.X86_64.macR W SP y) σ.mem s'.mem ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, ⟨_, l₁, c₁⟩, a₁, d₁⟩, ⟨o₂, ⟨_, l₂, c₂⟩, a₂, d₂⟩⟩ := hQ _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.b0_ok v L o₁.env o₁.sl hR l₁ h7 h13 ht4 ht16 hte hal hn' c₁ hy) fun _ q =>
          ⟨o₁, a₁, d₁, q.1, q.2.1, q.2.2.2.1, q.2.2.2.2⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.b0_ok v L o₂.env o₂.sl hR l₂ h7 h13 ht4 ht16 hte hal hn' c₂ hy) fun _ q =>
          ⟨o₂, a₂, d₂, q.1, q.2.1, q.2.2.2.1, q.2.2.2.2⟩⟩
  have hB : ∀ s₁ s₂, (True ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₁ A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₁ D n ∧
        (VG.Proof.AesCcm.X86_64.Env K W SP s₁ ∧ Frame (VG.Proof.AesCcm.X86_64.macR W SP y) σ₁.mem s₁.mem ∧ s₁.rd = σ₁.rd ∧ s₁.wr = σ₁.wr)) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₂ A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₂ D n ∧
        (VG.Proof.AesCcm.X86_64.Env K W SP s₂ ∧ Frame (VG.Proof.AesCcm.X86_64.macR W SP y) σ₂.mem s₂.mem ∧ s₂.rd = σ₂.rd ∧ s₂.wr = σ₂.wr))) →
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₁ A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₁ D n) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₂ A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₂ D n) :=
    fun s₁ s₂ ⟨_, σ₁, σ₂, _, ⟨o₁, a₁, d₁, E₁, f₁, rd₁, wr₁⟩, ⟨o₂, a₂, d₂, E₂, f₂, rd₂, wr₂⟩⟩ =>
      ⟨⟨o₁.macR L hDW hy16 E₁ f₁ wr₁, a₁.of_eq rd₁ wr₁, d₁.of_eq rd₁ wr₁⟩,
        ⟨o₂.macR L hDW hy16 E₂ f₂ wr₂, a₂.of_eq rd₂ wr₂, d₂.of_eq rd₂ wr₂⟩⟩
  have r₂ := (VG.Proof.AesCcm.X86_64.aad_rel v L hR hDW hn hy (A := A) (N := N) (nl := nl) (tl := tl) fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, -⟩, ⟨o₂, a₂, -⟩⟩ := hB s₁ s₂ h; exact ⟨o₁, o₂, a₁, a₂⟩).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ D n ∧
      ∃ Y, @VG.Proof.AesCcm.X86_64.MacStep K W SP σ y Y s')
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, d₁⟩, ⟨o₂, a₂, d₂⟩⟩ := hB s₁ s₂ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.aad_ok v L o₁.env o₁.sl hR hy a₁) fun _ q => ⟨o₁, d₁, _, q⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.aad_ok v L o₂.env o₂.sl hR hy a₂) fun _ q => ⟨o₂, d₂, _, q⟩⟩
  have hC : ∀ (PP : State → State → Prop) s₁ s₂, (True ∧ ∃ σ₁ σ₂, PP σ₁ σ₂ ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₁ D n ∧ ∃ Y, @VG.Proof.AesCcm.X86_64.MacStep K W SP σ₁ y Y s₁) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ₂ D n ∧ ∃ Y, @VG.Proof.AesCcm.X86_64.MacStep K W SP σ₂ y Y s₂)) →
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₁ D n) ∧ (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s₂ D n) :=
    fun _ s₁ s₂ ⟨_, σ₁, σ₂, _, ⟨o₁, d₁, _, M₁⟩, ⟨o₂, d₂, _, M₂⟩⟩ =>
      ⟨⟨o₁.macR L hDW hy16 M₁.env M₁.frame M₁.wr, d₁.of_eq M₁.rd M₁.wr⟩,
        ⟨o₂.macR L hDW hy16 M₂.env M₂.frame M₂.wr, d₂.of_eq M₂.rd M₂.wr⟩⟩
  refine RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq ((VG.Proof.AesCcm.X86_64.rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A)
      (nl := nl) (al := al) (tl := tl) [] hDW hn ?hb VG.Proof.AesCcm.X86_64.macBlk_check).wpDep
    (F := fun (σ s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ ∧ VG.Proof.AesCcm.X86_64.Buf K W SP σ D n ∧
      (s'.mem = σ.mem ∧ s'.gpr .r12 = D ∧ s'.gpr .rbp = BitVec.ofNat 64 n ∧
        (∀ r, r ≠ .r12 → r ≠ .rbp → s'.gpr r = σ.gpr r) ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr)) ?hw)
    (VG.Proof.AesCcm.X86_64.absorbPad_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl) (P := D) (len := n) ?hq)))
  case hb =>
    intro s₁ s₂ h
    obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hC _ s₁ s₂ h; exact Both.of o₁ o₂ fun _ h => nomatch h
  case hw =>
    intro s₁ s₂ h
    obtain ⟨⟨o₁, d₁⟩, ⟨o₂, d₂⟩⟩ := hC _ s₁ s₂ h
    exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.macBlk_ok o₁.env o₁.sl) fun _ q => ⟨o₁, d₁, q⟩,
      WP.mono (VG.Proof.AesCcm.X86_64.macBlk_ok o₂.env o₂.sl) fun _ q => ⟨o₂, d₂, q⟩⟩
  intro s₁ s₂ h
  obtain ⟨_, σ₁, σ₂, _, ⟨o₁, d₁, m₁, h12₁, hbp₁, g₁, rd₁, wr₁⟩, ⟨o₂, d₂, m₂, h12₂, hbp₂, g₂, rd₂, wr₂⟩⟩ := h
  have keep : ∀ {σ s' : State}, VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ → s'.mem = σ.mem →
      (∀ r, r ≠ .r12 → r ≠ .rbp → s'.gpr r = σ.gpr r) → s'.rd = σ.rd → s'.wr = σ.wr →
      VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s' := fun o m g rd wr =>
    ⟨o.env.keep (fun r hr => g r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd wr, m ▸ o.sl, wr.trans o.wr⟩
  exact ⟨keep o₁ m₁ g₁ rd₁ wr₁, keep o₂ m₂ g₂ rd₂ wr₂, ⟨d₁.of_eq rd₁ wr₁, h12₁, hbp₁⟩, ⟨d₂.of_eq rd₂ wr₂, h12₂, hbp₂⟩⟩

theorem tagArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [])
    (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov32 .rax (imm 0)] : List Instr) ++ ctrAt ++ ([.mov .rdi (.reg .r13)] : List Instr) ++
      ptr .rdx .r15 c1O ++ ptr .rcx .r15 y ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The tag, in two runs. -/
theorem tag_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) {y : Nat} (hy : y = 0 ∨ y = 96) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.C0 W nl s₁) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ VG.Proof.AesCcm.X86_64.C0 W nl s₂)) :
    RelCT isa Q (tag v.callee y) fun _ _ => True := by
  have a := (VG.Proof.AesCcm.X86_64.rel_taintC [] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hQ _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) (VG.Proof.AesCcm.X86_64.tagArgs_check hy)).wp
    (F₁ := fun (s : State) => VG.Proof.AesCcm.X86_64.CtrCall s K (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 384) R 1 ∧
      s.gpr .rsp = SP)
    (F₂ := fun (s : State) => VG.Proof.AesCcm.X86_64.CtrCall s K (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 384) R 1 ∧
      s.gpr .rsp = SP)
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, _, l₁, c₁⟩, ⟨o₂, _, l₂, c₂⟩⟩ := hQ _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.tagArgs_ok L o₁.env hR o₁.sl.rounds (by omega) (by omega) c₁ hy) fun _ q => ⟨q.2.1, q.1.rsp⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.tagArgs_ok L o₂.env hR o₂.sl.rounds (by omega) (by omega) c₂ hy) fun _ q => ⟨q.2.1, q.1.rsp⟩⟩
  exact RelCT.seq a (VG.Proof.AesCcm.X86_64.ctr_rel v fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT`. -/
section

/-!
# AES-CCM on x86-64: counter mode is constant time

Untrusted: everything here is checked by Lean. Both runs go through the same
chunks: the number of blocks of each, `k`, depends only on the length and
the blocks done (`chunk_ok`), and it is kept at `W + 216`, which the taint
analysis then takes as public (`ccmTk`) for the end of the chunk; the calls
of `vg_aes_ctr32` have the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The taint of `ccmT rs`, with `k` at `W + 216` public too. -/
def ccmTk (rs : List Reg) : X86_64.Taint.T :=
  { VG.Proof.AesCcm.X86_64.ccmT rs with slots := [(1, 160, 56), (1, 232, 8), (1, 216, 8)] }

theorem both_agree_k {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h : VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂) {v : BitVec 64}
    (hk₁ : s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = v) (hk₂ : s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = v) :
    X86_64.Taint.Agree (VG.Proof.AesCcm.X86_64.ccmTk rs) s₁ s₂ := by
  have a := VG.Proof.AesCcm.X86_64.both_agree hDW hn h
  refine ⟨a.rf, a.wr, a.wf₁, a.wf₂, fun sl hsl => ?_, fun sl hsl k hk₁' hk₂' => ?_, a.lo⟩
  · simp only [VG.Proof.AesCcm.X86_64.ccmTk, VG.Proof.AesCcm.X86_64.ccmT, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl | rfl <;> simp [VG.Proof.AesCcm.X86_64.ccmTk, VG.Proof.AesCcm.X86_64.ccmT]
  · simp only [VG.Proof.AesCcm.X86_64.ccmTk, List.mem_cons, List.not_mem_nil, or_false] at hsl
    rcases hsl with rfl | rfl | rfl
    · exact a.slots _ (List.Mem.head _) k hk₁' hk₂'
    · exact a.slots _ (List.Mem.tail _ (List.Mem.head _)) k hk₁' hk₂'
    · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
        fun s hw => by simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ,
          List.getD_cons_zero]
      simp only at hk₁' hk₂'
      rw [hb s₁ h.wr₁, hb s₂ h.wr₂, show W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 216 + BitVec.ofNat 64 (k - 216)
        by rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc, show 216 + (k - 216) = k by omega]]
      exact VG.Proof.AesCcm.X86_64.word_byte hk₁ hk₂ (by omega)

/-- Code the taint analysis checks from `ccmTk rs`, leaving the flags public. -/
theorem rel_flagsCk {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.X86_64.Both K W SP R N A D nl al n tl rs s₁ s₂ ∧ ∃ v,
      s₁.mem.readW (W + BitVec.ofNat 64 216) 64 = v ∧ s₂.mem.readW (W + BitVec.ofNat 64 216) 64 = v)
    (hc : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmTk rs) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hb, v, h₁, h₂⟩ := hP _ _ hp
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (VG.Proof.AesCcm.X86_64.both_agree_k hDW hn hb h₁ h₂) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

/-- The number of blocks of the chunk after `b`. -/
def chunkK (n b : Nat) : Nat := min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32)

/-- A chunk up to its call: the arguments. -/
theorem chunkPre_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n) {b : Nat} {t : State} (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) :
    WP isa (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)])
      (.seq (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))
      (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++
        ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ([.mov .rcx (.reg .r12)] : List Instr) ++
        ptr .r9 .r15 scrO)))) t fun t₅ =>
      VG.Proof.AesCcm.X86_64.CtrCall t₅ K (W + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 384) R
        (VG.Proof.AesCcm.X86_64.chunkK n b) ∧ VG.Proof.AesCcm.X86_64.Env K W SP t₅ ∧ t₅.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (VG.Proof.AesCcm.X86_64.chunkK n b) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.kSel_ok I.rbx I.r14 (by omega)) fun t₂ ⟨hm₂, hr8₂, hg₂, hrd₂, hwr₂⟩ => ?_))
  have hk1 : 1 ≤ VG.Proof.AesCcm.X86_64.chunkK n b := by unfold VG.Proof.AesCcm.X86_64.chunkK; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + VG.Proof.AesCcm.X86_64.chunkK n b ≤ n / 16 := by unfold VG.Proof.AesCcm.X86_64.chunkK; omega
  obtain ⟨t₅, run₅, f₅, _, hkO₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ :=
    VG.Proof.AesCcm.X86_64.setup_ok C I hb hm₂ hr8₂ hg₂ hrd₂ hwr₂
  have E₅ : VG.Proof.AesCcm.X86_64.Env K W SP t₅ := I.env.keep (fun r hr => hg₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₅ hwr₅
  have hS := (C.buf.of_eq (hrd₅.trans I.rd) (hwr₅.trans I.wr)).slice (a := 16 * b) (k := 16 * VG.Proof.AesCcm.X86_64.chunkK n b) (by omega)
  have hqc : (⟨D + BitVec.ofNat 64 (16 * b), 16 * VG.Proof.AesCcm.X86_64.chunkK n b⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    hS.w.sub_right (Lay.wSub (by decide))
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * b), 16 * VG.Proof.AesCcm.X86_64.chunkK n b⟩ :=
    C.dk.sub_right (Offset.sub_base D (by omega))
  have hqw : Covers [⟨D + BitVec.ofNat 64 (16 * b), 16 * VG.Proof.AesCcm.X86_64.chunkK n b⟩] t₅.wr := by
    rw [hwr₅, I.wr]; exact VG.Proof.AesCcm.X86_64.covers_off C.dw (by omega) hn64
  exact WP.of_runBlock ⟨t₅, run₅, VG.Proof.AesCcm.X86_64.cargs L E₅ C.rounds (c := 64) (by decide) (VG.Proof.AesCcm.X86_64.srcBuf hS) hqc hqk hqw
    hdi hsi hdx hcx hr8 hr9, E₅, hkO₅, hg₅, hrd₅, hwr₅, f₅⟩

theorem chunkPre_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [.rbx, .r12, .r14])
    (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)])
      (.seq (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))
      (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++
        ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ([.mov .rcx (.reg .r12)] : List Instr) ++
        ptr .r9 .r15 scrO)))) hc).isSome = true := ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmTk [.rbx, .r12, .r14])
    (.block [.mov .rax (.mem (at_ .r15 kO)), .alu .sub .rbx (.reg .rax), .alu .add .r14 (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .r12 (.reg .rax), .alu .test .rbx (.reg .rbx)]) hc).map (·.flags)) = some true := ⟨_, by taint_decide⟩

/-- A run after `b` blocks of counter mode, from `σ`. -/
theorem CtrInv.one {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {nonce : List Byte} {σ t : State}
    {b : Nat} (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ R nonce D n) (O : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ)
    (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP σ R nonce D n b t) : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl t :=
  ⟨I.env, VG.Proof.AesCcm.X86_64.slots_mut C.lay C.buf.w (I.frame.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n)) O.sl, I.wr.trans O.wr⟩

/-- What the call of a chunk is given, in a run from `σ`. -/
def ChunkArgs (K W SP : Addr) (R : Nat) (D : Addr) (n b : Nat) (σ t : State) : Prop :=
  VG.Proof.AesCcm.X86_64.CtrCall t K (W + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 384) R (VG.Proof.AesCcm.X86_64.chunkK n b) ∧
    VG.Proof.AesCcm.X86_64.Env K W SP t ∧ t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (VG.Proof.AesCcm.X86_64.chunkK n b) ∧
    t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) ∧ t.gpr .r12 = D + BitVec.ofNat 64 (16 * b) ∧
    t.gpr .r14 = BitVec.ofNat 64 (1 + b) ∧ t.rd = σ.rd ∧ t.wr = σ.wr ∧ Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) σ.mem t.mem

/-- What the call of a chunk leaves, in a run from `σ`. -/
def ChunkCalled (K W SP : Addr) (D : Addr) (n b : Nat) (σ t : State) : Prop :=
  VG.Proof.AesCcm.X86_64.Env K W SP t ∧ t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 (VG.Proof.AesCcm.X86_64.chunkK n b) ∧
    t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) ∧ t.gpr .r12 = D + BitVec.ofNat 64 (16 * b) ∧
    t.gpr .r14 = BitVec.ofNat 64 (1 + b) ∧ t.wr = σ.wr ∧ Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) σ.mem t.mem

theorem chunkArgs_ok {K W SP : Addr} {σ : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ R nonce D n) {b : Nat} {t : State} (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP σ R nonce D n b t)
    (hb : b < n / 16) :
    WP isa (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)])
      (.seq (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))
      (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++
        ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ([.mov .rcx (.reg .r12)] : List Instr) ++
        ptr .r9 .r15 scrO)))) t (VG.Proof.AesCcm.X86_64.ChunkArgs K W SP R D n b σ) :=
  WP.mono (VG.Proof.AesCcm.X86_64.chunkPre_ok C I hb) fun _ ⟨cc, E, k, g, rd, wr, f⟩ =>
    ⟨cc, E, k, by rw [g _ (by simp), I.rbx], by rw [g _ (by simp), I.r12], by rw [g _ (by simp), I.r14],
      by rw [rd, I.rd], by rw [wr, I.wr], I.frame.trans (f.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩)⟩

theorem chunkCalled_ok (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {D : Addr} {n b : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hkb : 16 * b + 16 * VG.Proof.AesCcm.X86_64.chunkK n b ≤ n) {σ t : State}
    (h : VG.Proof.AesCcm.X86_64.ChunkArgs K W SP R D n b σ t) :
    WP isa (.call v.callee.name v.callee.code) t (VG.Proof.AesCcm.X86_64.ChunkCalled K W SP D n b σ) := by
  obtain ⟨cc, E, k, h₁, h₂, h₃, _, wr, f⟩ := h
  refine WP.mono (VG.Proof.AesCcm.X86_64.ctr_call v cc) fun t' p => ⟨E.of_saved p.saved p.rd p.wr, ?_, by rw [p.saved _ (by decide), h₁],
    by rw [p.saved _ (by decide), h₂], by rw [p.saved _ (by decide), h₃], by rw [p.wr, wr], ?_⟩
  · have hDs : Region.Sub ⟨D + BitVec.ofNat 64 (16 * b), 16 * VG.Proof.AesCcm.X86_64.chunkK n b⟩ ⟨D, n⟩ := Offset.sub_base D hkb
    rw [p.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact ((hDW.sub_left hDs).sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E.rsp]; exact ((L.stk_w' (by decide)).sub_left (VG.Proof.AesCcm.X86_64.below8_sub _)).symm) (by decide), k]
  · have fc := p.frame
    rw [E.rsp] at fc
    exact f.trans (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D hkb⟩
      · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below SP 16, by simp, VG.Proof.AesCcm.X86_64.below8_sub SP⟩)

/-- A chunk, in two runs (from `σ₁` and `σ₂`) that have done the same blocks. -/
theorem chunk_rel (v : Ctr32Impl) {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {σ₁ σ₂ : State}
    {nonce₁ nonce₂ : List Byte} (C₁ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₁ R nonce₁ D n) (C₂ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₂ R nonce₂ D n)
    (O₁ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁) (O₂ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂) {b : Nat} (hb : b < n / 16) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n b t₁ ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n b t₂)
      (ctrChunk v.callee) fun t₁ t₂ => t₁.zf = t₂.zf := by
  have L := C₁.lay
  have hDW := C₁.buf.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt C₁.buf.lt
  have hkb : 16 * b + 16 * VG.Proof.AesCcm.X86_64.chunkK n b ≤ n := by unfold VG.Proof.AesCcm.X86_64.chunkK; omega
  have hreg : ∀ {t₁ t₂ : State}, t₁.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) → t₂.gpr .rbx = BitVec.ofNat 64 (n / 16 - b) →
      t₁.gpr .r12 = D + BitVec.ofNat 64 (16 * b) → t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * b) →
      t₁.gpr .r14 = BitVec.ofNat 64 (1 + b) → t₂.gpr .r14 = BitVec.ofNat 64 (1 + b) →
      ∀ r ∈ [Reg.rbx, .r12, .r14], t₁.gpr r = t₂.gpr r := fun a₁ a₂ b₁ b₂ c₁ c₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [b₁, b₂]
    · rw [c₁, c₂]
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_taintC [.rbx, .r12, .r14] hDW hn (fun t₁ t₂ (h : VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n b t₁ ∧
      VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n b t₂) =>
    Both.of (h.1.one C₁ O₁) (h.2.one C₂ O₂) (hreg h.1.rbx h.2.rbx h.1.r12 h.2.r12 h.1.r14 h.2.r14))
    VG.Proof.AesCcm.X86_64.chunkPre_check).wp (F₁ := VG.Proof.AesCcm.X86_64.ChunkArgs K W SP R D n b σ₁) (F₂ := VG.Proof.AesCcm.X86_64.ChunkArgs K W SP R D n b σ₂)
    fun t₁ t₂ h => ⟨VG.Proof.AesCcm.X86_64.chunkArgs_ok C₁ h.1 hb, VG.Proof.AesCcm.X86_64.chunkArgs_ok C₂ h.2 hb⟩
  have r₂ := (VG.Proof.AesCcm.X86_64.ctr_rel v (P := fun t₁ t₂ => True ∧ VG.Proof.AesCcm.X86_64.ChunkArgs K W SP R D n b σ₁ t₁ ∧ VG.Proof.AesCcm.X86_64.ChunkArgs K W SP R D n b σ₂ t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1.rsp, h.2.2.2.1.rsp]⟩).wp
    (F₁ := VG.Proof.AesCcm.X86_64.ChunkCalled K W SP D n b σ₁) (F₂ := VG.Proof.AesCcm.X86_64.ChunkCalled K W SP D n b σ₂)
    fun t₁ t₂ h => ⟨VG.Proof.AesCcm.X86_64.chunkCalled_ok v L hDW hkb h.2.1, VG.Proof.AesCcm.X86_64.chunkCalled_ok v L hDW hkb h.2.2⟩
  have r₃ := VG.Proof.AesCcm.X86_64.rel_flagsCk (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun t₁ t₂ => True ∧ VG.Proof.AesCcm.X86_64.ChunkCalled K W SP D n b σ₁ t₁ ∧ VG.Proof.AesCcm.X86_64.ChunkCalled K W SP D n b σ₂ t₂)
    [.rbx, .r12, .r14] hDW hn (fun t₁ t₂ ⟨_, ⟨E₁, k₁, a₁, b₁, c₁, w₁, f₁⟩, ⟨E₂, k₂, a₂, b₂, c₂, w₂, f₂⟩⟩ =>
      ⟨Both.of ⟨E₁, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₁.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n)) O₁.sl, w₁.trans O₁.wr⟩
        ⟨E₂, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₂.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n)) O₂.sl, w₂.trans O₂.wr⟩ (hreg a₁ a₂ b₁ b₂ c₁ c₂),
        _, k₁, k₂⟩) VG.Proof.AesCcm.X86_64.chunkEnd_check
  exact VG.Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq r₁ (RelCT.seq r₂ (r₃.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-! ## The last bytes -/

/-- Before the last bytes, in a run from `σ`: after the whole blocks, with
`n mod 16` in `rbp`. -/
def TailIn (K W SP : Addr) (R : Nat) (nonce : List Byte) (D : Addr) (n : Nat) (σ t₀ : State) : Prop :=
  ∃ t, VG.Proof.AesCcm.X86_64.CtrInv K W SP σ R nonce D n (n / 16) t ∧ t₀.mem = t.mem ∧ (∀ r, r ≠ .rbp → t₀.gpr r = t.gpr r) ∧
    t₀.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr

/-- What the call for the last bytes is given. -/
def TailArgs (K W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (σ t : State) : Prop :=
  VG.Proof.AesCcm.X86_64.CtrCall t K (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 384) R 1 ∧ VG.Proof.AesCcm.X86_64.Env K W SP t ∧
    t.gpr .r12 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t.rd = σ.rd ∧
    t.wr = σ.wr ∧ Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) σ.mem t.mem

/-- What the call for the last bytes leaves. -/
def TailCalled (K W SP : Addr) (D : Addr) (n : Nat) (σ t : State) : Prop :=
  VG.Proof.AesCcm.X86_64.Env K W SP t ∧ t.gpr .r12 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧
    t.wr = σ.wr ∧ Frame (VG.Proof.AesCcm.X86_64.ctrR W SP D n) σ.mem t.mem

theorem tailArgs_ok {K W SP : Addr} {σ : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ R nonce D n) {t₀ : State} (h : VG.Proof.AesCcm.X86_64.TailIn K W SP R nonce D n σ t₀) (h0 : n % 16 ≠ 0) :
    WP isa (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
      ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++
      ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) t₀ (VG.Proof.AesCcm.X86_64.TailArgs K W SP R D n σ) := by
  obtain ⟨t, I, hm₀, hg₀, hbp, hrd₀, hwr₀⟩ := h
  have L := C.lay
  have E₀ : VG.Proof.AesCcm.X86_64.Env K W SP t₀ := I.env.keep (fun r hr => hg₀ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₀ hwr₀
  obtain ⟨t₁, run₁, f₁, _, _, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ :=
    VG.Proof.AesCcm.X86_64.tailSetup_ok E₀ (by rw [hm₀, C.readW_kept I.frame (by omega), C.ro]) C.h7 C.h13
      (by rw [hm₀, C.bytes_kept I.frame (by omega), C.c0]) (j := 1 + n / 16) (by have := C.hn; omega)
      (by rw [hg₀ _ (by decide), I.r14])
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP t₁ := E₀.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₁ hwr₁
  have hq := VG.Proof.AesCcm.X86_64.srcW (s := t₁) L E₁.perm (t := 80) (k := 16 * 1) (by decide)
  have hqc : (⟨W + BitVec.ofNat 64 80, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    L.w_w (.inr (by decide)) (by decide) (by decide)
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 80, 16 * 1⟩ := L.k_w.sub_right (Lay.wSub (by decide))
  exact WP.of_runBlock ⟨t₁, run₁, VG.Proof.AesCcm.X86_64.cargs L E₁ C.rounds (c := 64) (by decide) hq hqc hqk
    (E₁.perm.wC (d := 80) (n := 16 * 1) (by decide)) hdi hsi hdx hcx hr8 hr9, E₁,
    by rw [hg₁ _ (by simp), hg₀ _ (by decide), I.r12], by rw [hg₁ _ (by simp), hbp],
    by rw [hrd₁, hrd₀, I.rd], by rw [hwr₁, hwr₀, I.wr],
    I.frame.trans (by rw [← hm₀]; exact f₁.sub fun r hr => ⟨r, by
      simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩)⟩

theorem tailCalled_ok (v : Ctr32Impl) {K W SP : Addr} {R : Nat} {D : Addr} {n : Nat} {σ t : State}
    (h : VG.Proof.AesCcm.X86_64.TailArgs K W SP R D n σ t) :
    WP isa (.call v.callee.name v.callee.code) t (VG.Proof.AesCcm.X86_64.TailCalled K W SP D n σ) := by
  obtain ⟨cc, E, h12, hbp, _, wr, f⟩ := h
  refine WP.mono (VG.Proof.AesCcm.X86_64.ctr_call v cc) fun t' p => ⟨E.of_saved p.saved p.rd p.wr, by rw [p.saved _ (by decide), h12],
    by rw [p.saved _ (by decide), hbp], by rw [p.wr, wr], ?_⟩
  have fc := p.frame
  rw [E.rsp] at fc
  exact f.trans (fc.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨below SP 16, by simp, VG.Proof.AesCcm.X86_64.below8_sub SP⟩)

theorem tailArgs_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [.r12, .r14, .rbp])
    (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
      ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++
      ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) hc).isSome = true := ⟨_, by taint_decide⟩

theorem tailEnd_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [.r12, .rbp])
    (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 ksO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- The last bytes, in two runs. -/
theorem tail_rel (v : Ctr32Impl) {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {σ₁ σ₂ : State}
    {nonce₁ nonce₂ : List Byte} (C₁ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₁ R nonce₁ D n) (C₂ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₂ R nonce₂ D n)
    (O₁ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁) (O₂ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂) (h0 : n % 16 ≠ 0) :
    RelCT isa (fun t₁ t₂ => VG.Proof.AesCcm.X86_64.TailIn K W SP R nonce₁ D n σ₁ t₁ ∧ VG.Proof.AesCcm.X86_64.TailIn K W SP R nonce₂ D n σ₂ t₂)
      (.seq (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
          ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++
          ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO))
        (.seq (callCtr v.callee)
          (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 ksO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop)))
      fun _ _ => True := by
  have L := C₁.lay
  have hDW := C₁.buf.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt C₁.buf.lt
  have oneIn : ∀ {σ t₀ : State} {nonce : List Byte}, VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ R nonce D n →
      VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ → VG.Proof.AesCcm.X86_64.TailIn K W SP R nonce D n σ t₀ →
      VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl t₀ ∧ t₀.gpr .r12 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧
        t₀.gpr .r14 = BitVec.ofNat 64 (1 + n / 16) ∧ t₀.gpr .rbp = BitVec.ofNat 64 (n % 16) :=
    fun C O ⟨t, I, hm₀, hg₀, hbp, hrd₀, hwr₀⟩ =>
      ⟨⟨I.env.keep (fun r hr => hg₀ r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
          hrd₀ hwr₀, hm₀ ▸ (I.one C O).sl, hwr₀.trans (I.one C O).wr⟩,
        by rw [hg₀ _ (by decide), I.r12], by rw [hg₀ _ (by decide), I.r14], hbp⟩
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_taintC [.r12, .r14, .rbp] hDW hn (fun t₁ t₂ (h : VG.Proof.AesCcm.X86_64.TailIn K W SP R nonce₁ D n σ₁ t₁ ∧
      VG.Proof.AesCcm.X86_64.TailIn K W SP R nonce₂ D n σ₂ t₂) => by
    obtain ⟨o₁, a₁, b₁, c₁⟩ := oneIn C₁ O₁ h.1
    obtain ⟨o₂, a₂, b₂, c₂⟩ := oneIn C₂ O₂ h.2
    exact Both.of o₁ o₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) VG.Proof.AesCcm.X86_64.tailArgs_check).wp (F₁ := VG.Proof.AesCcm.X86_64.TailArgs K W SP R D n σ₁) (F₂ := VG.Proof.AesCcm.X86_64.TailArgs K W SP R D n σ₂)
    fun t₁ t₂ h => ⟨VG.Proof.AesCcm.X86_64.tailArgs_ok C₁ h.1 h0, VG.Proof.AesCcm.X86_64.tailArgs_ok C₂ h.2 h0⟩
  have r₂ := (VG.Proof.AesCcm.X86_64.ctr_rel v (P := fun t₁ t₂ => True ∧ VG.Proof.AesCcm.X86_64.TailArgs K W SP R D n σ₁ t₁ ∧ VG.Proof.AesCcm.X86_64.TailArgs K W SP R D n σ₂ t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1.rsp, h.2.2.2.1.rsp]⟩).wp
    (F₁ := VG.Proof.AesCcm.X86_64.TailCalled K W SP D n σ₁) (F₂ := VG.Proof.AesCcm.X86_64.TailCalled K W SP D n σ₂)
    fun t₁ t₂ h => ⟨VG.Proof.AesCcm.X86_64.tailCalled_ok v h.2.1, VG.Proof.AesCcm.X86_64.tailCalled_ok v h.2.2⟩
  have r₃ := VG.Proof.AesCcm.X86_64.rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun t₁ t₂ => True ∧ VG.Proof.AesCcm.X86_64.TailCalled K W SP D n σ₁ t₁ ∧ VG.Proof.AesCcm.X86_64.TailCalled K W SP D n σ₂ t₂)
    [.r12, .rbp] hDW hn (fun t₁ t₂ ⟨_, ⟨E₁, a₁, b₁, w₁, f₁⟩, ⟨E₂, a₂, b₂, w₂, f₂⟩⟩ =>
      Both.of ⟨E₁, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₁.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n)) O₁.sl, w₁.trans O₁.wr⟩
        ⟨E₂, VG.Proof.AesCcm.X86_64.slots_mut L hDW (f₂.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n)) O₂.sl, w₂.trans O₂.wr⟩ fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [a₁, a₂]
          · rw [b₁, b₂]) VG.Proof.AesCcm.X86_64.tailEnd_check
  exact RelCT.seq r₁ (RelCT.seq r₂ r₃)

/-! ## Counter mode -/

theorem ctrHead_check : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)]) hc).map (·.flags)) = some true := ⟨_, by taint_decide⟩

theorem ctrB3_check : ∃ hc, ((taint.check (VG.Proof.AesCcm.X86_64.ccmT [])
    (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .and .rbp (imm 15), .alu .test .rbp (.reg .rbp)]) hc).map
      (·.flags)) = some true := ⟨_, by taint_decide⟩

/-- The chunks, in two runs that have done the same blocks. -/
theorem chunks_rel (v : Ctr32Impl) {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {σ₁ σ₂ : State}
    {nonce₁ nonce₂ : List Byte} (C₁ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₁ R nonce₁ D n) (C₂ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₂ R nonce₂ D n)
    (O₁ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁) (O₂ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂) (m : Nat) :
    RelCT isa (fun t₁ t₂ => ∃ b, m = n / 16 - b ∧ b < n / 16 ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n b t₁ ∧
        VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n b t₂) (.loop (ctrChunk v.callee) .ne)
      fun t₁ t₂ => VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n (n / 16) t₁ ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n (n / 16) t₂ := by
  refine RelCT.loop (M := isa) (fun (m : Nat) (t₁ t₂ : State) => ∃ b, m = n / 16 - b ∧ b < n / 16 ∧
    VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n b t₁ ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n b t₂) (fun m => ?_) m
  refine RelCT.exists_ (M := isa) (P := fun b (t₁ t₂ : State) => m = n / 16 - b ∧ b < n / 16 ∧
    VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n b t₁ ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n b t₂) fun b => ?_
  by_cases hb : b < n / 16
  swap
  · exact RelCT.of_false fun _ _ h => hb h.2.1
  by_cases hm : m = n / 16 - b
  swap
  · exact RelCT.of_false fun _ _ h => hm h.1
  refine ((VG.Proof.AesCcm.X86_64.chunk_rel v C₁ C₂ O₁ O₂ hb).wp fun t₁ t₂ h => ⟨VG.Proof.AesCcm.X86_64.chunk_ok v C₁ h.1 hb, VG.Proof.AesCcm.X86_64.chunk_ok v C₂ h.2 hb⟩).mono
    (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩) fun t₁ t₂ ⟨hz, ⟨k₁, hk₁, hk1, _, I₁, hz₁⟩, ⟨k₂, hk₂, _, _, I₂, _⟩⟩ => ?_
  subst hk₁ hk₂
  refine ⟨VG.Proof.AesCcm.X86_64.eval_ne_eq hz, fun hf => ?_, fun ht => ?_⟩
  · rw [VG.Proof.AesCcm.X86_64.eval_ne hz₁] at hf
    have he : b + min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) = n / 16 := by simpa using hf
    rw [he] at I₁ I₂
    exact ⟨I₁, I₂⟩
  · rw [VG.Proof.AesCcm.X86_64.eval_ne hz₁] at ht
    have he : b + min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ≠ n / 16 := by simpa using ht
    exact ⟨n / 16 - (b + min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32)), by omega, _, rfl, by omega, I₁, I₂⟩

/-- After the whole blocks: `n mod 16` in `rbp`, and ZF set when there are no
last bytes. -/
theorem tailIn_ok {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {σ t : State}
    {nonce : List Byte} (C : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ R nonce D n) (O : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ)
    (I : VG.Proof.AesCcm.X86_64.CtrInv K W SP σ R nonce D n (n / 16) t) :
    WP isa (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .and .rbp (imm 15), .alu .test .rbp (.reg .rbp)]) t
      fun t₀ => VG.Proof.AesCcm.X86_64.TailIn K W SP R nonce D n σ t₀ ∧ t₀.zf = some (decide (n % 16 = 0)) := by
  have hl : t.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by
    rw [C.readW_kept I.frame (by omega)]; exact O.sl.len
  exact WP.mono (VG.Proof.AesCcm.X86_64.ctrB3_ok I.env hl C.buf.lt) fun t₀ ⟨hm, hbp, hz, hg, hrd, hwr⟩ =>
    ⟨⟨t, I, hm, hg, hbp, hrd, hwr⟩, hz⟩

/-- Counter mode, in two runs from `σ₁` and `σ₂`. -/
theorem crypt_rel (v : Ctr32Impl) {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} {σ₁ σ₂ : State}
    {nonce₁ nonce₂ : List Byte} (C₁ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₁ R nonce₁ D n) (C₂ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP σ₂ R nonce₂ D n)
    (O₁ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₁) (O₂ : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl σ₂) :
    RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) (ctr v.callee) fun _ _ => True := by
  have hDW := C₁.buf.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt C₁.buf.lt
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_flagsC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) [] hDW hn (fun t₁ t₂ h => by
      rw [h.1, h.2]; exact Both.of O₁ O₂ (fun _ h => nomatch h)) VG.Proof.AesCcm.X86_64.ctrHead_check).wp
    (F₁ := fun (t : State) => VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n 0 t ∧ t.zf = some (decide (n / 16 = 0)))
    (F₂ := fun (t : State) => VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n 0 t ∧ t.zf = some (decide (n / 16 = 0)))
    fun t₁ t₂ h => by rw [h.1, h.2]; exact ⟨VG.Proof.AesCcm.X86_64.ctrHeadBlk_ok C₁ O₁.env O₁.sl, VG.Proof.AesCcm.X86_64.ctrHeadBlk_ok C₂ O₂.env O₂.sl⟩
  have r₃ := (VG.Proof.AesCcm.X86_64.rel_flagsC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl) [] hDW hn
    (fun t₁ t₂ (h : VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₁ R nonce₁ D n (n / 16) t₁ ∧ VG.Proof.AesCcm.X86_64.CtrInv K W SP σ₂ R nonce₂ D n (n / 16) t₂) =>
      Both.of (h.1.one C₁ O₁) (h.2.one C₂ O₂) (fun _ h => nomatch h)) VG.Proof.AesCcm.X86_64.ctrB3_check).wp
    fun t₁ t₂ h => ⟨VG.Proof.AesCcm.X86_64.tailIn_ok C₁ O₁ h.1, VG.Proof.AesCcm.X86_64.tailIn_ok C₂ O₂ h.2⟩
  refine RelCT.seq r₁ (RelCT.seq ?_ (RelCT.seq r₃ ?_))
  · refine RelCT.ite (fun t₁ t₂ h => VG.Proof.AesCcm.X86_64.eval_e_eq h.1.2)
      (RelCT.block_nil fun t₁ t₂ ⟨⟨_, ⟨I₁, hz₁⟩, I₂, _⟩, ht⟩ => ?_)
      ((VG.Proof.AesCcm.X86_64.chunks_rel v C₁ C₂ O₁ O₂ (n / 16 - 0)).mono (fun t₁ t₂ ⟨⟨_, ⟨I₁, hz₁⟩, I₂, _⟩, hf⟩ => ?_) fun _ _ h => h)
    · have h0 : n / 16 = 0 := by rw [VG.Proof.AesCcm.X86_64.eval_e hz₁] at ht; simpa using ht
      rw [h0]; exact ⟨I₁, I₂⟩
    · have h0 : n / 16 ≠ 0 := by rw [VG.Proof.AesCcm.X86_64.eval_e hz₁] at hf; simpa using hf
      exact ⟨0, rfl, by omega, I₁, I₂⟩
  · refine RelCT.ite (fun t₁ t₂ h => VG.Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_
    by_cases h0 : n % 16 = 0
    · exact RelCT.of_false fun t₁ t₂ ⟨⟨_, ⟨_, hz₁⟩, _⟩, hf⟩ => by rw [VG.Proof.AesCcm.X86_64.eval_e hz₁] at hf; simp [h0] at hf
    · exact (VG.Proof.AesCcm.X86_64.tail_rel v C₁ C₂ O₁ O₂ h0).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Seal`. -/
section

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `mac y` followed by `tag y`
leaves the MAC of the payload at `D`, encrypted, at `W + y` (`macTag_ok`).
`seal` is `entry`, `Ctr₀` (`ctrs`), the encrypted MAC at `W`, counter mode
over the data (`ctr`), the tag copied to `tag` (`tagOut_ok`) and `restore`
(`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What `mac y` and `tag y` write. -/
abbrev tagR (W SP : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩,
    ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16]

theorem tagR_wR (W SP : Addr) {y : Nat} (hy : y + 16 ≤ 112) : ∀ r ∈ VG.Proof.AesCcm.X86_64.tagR W SP y, ∃ r' ∈ VG.Proof.AesCcm.X86_64.wR W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W hy⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The MAC of the payload at `D`, encrypted with `CIPH_K(Ctr₀)`, at `W + y`. -/
theorem macTag_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : VG.Proof.AesCcm.X86_64.Buf K W SP s A al) (hD : VG.Proof.AesCcm.X86_64.Buf K W SP s D n) {Q : State → Prop}
    (hk : ∀ s', VG.Proof.AesCcm.X86_64.Env K W SP s' → s'.rd = s.rd → s'.wr = s.wr → Frame (VG.Proof.AesCcm.X86_64.tagR W SP y) s.mem s'.mem →
      bytesAt s'.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 →
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 0
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16)
          (Spec.Ccm.format tl nonce (bytesAt s.mem A al) (bytesAt s.mem D n))) → Q s') :
    WP isa (.seq (mac v.callee v.suffix y) (tag v.callee y)) s Q := by
  have hy16 : y + 16 ≤ 112 := by omega
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> subst h <;> decide
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.mac_ok v L E S hR hnl h7 h13 ht4 ht16 hte hn hc0 hy hA hD) fun s₁ M => ?_)
  have fy : Frame (VG.Proof.AesCcm.X86_64.tagR W SP y) s.mem s₁.mem := M.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [VG.Proof.AesCcm.X86_64.rounds_kept L hy M.frame]; exact S.rounds
  have hc₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rcases hy with rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), hc0]
  refine WP.mono (VG.Proof.AesCcm.X86_64.tag_ok v L M.env hR hRo₁ (by omega) (by omega) hc₁ hy)
    fun s₂ ⟨E₂, _, rd₂, wr₂, f₂, h₂⟩ => ?_
  refine hk s₂ E₂ (by rw [rd₂, M.rd]) (by rw [wr₂, M.wr]) (fy.trans (f₂.sub fun r hr => ?_)) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [VG.Proof.AesCcm.X86_64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rcases hy with rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), hc₁]
  · rw [h₂, M.out, VG.Proof.AesCcm.X86_64.ctxCiph_frame M.frame (VG.Proof.AesCcm.X86_64.k_macR L (by omega)) hRb]

/-- The return address is outside what the functions write. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ VG.Proof.AesCcm.X86_64.entryR W :: VG.Proof.AesCcm.X86_64.mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag `T`, whose
address is at `SP + 24`. -/
theorem tagOut_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTw : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa tagOut s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem T (bytesAt s.mem W tl) := by
  have h15 := E.r15
  have hsp := E.rsp
  have rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have htl := S.tl
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rdi = T ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, hsp, rt, hTr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hsp, hT]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, htl]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have lp : LoopPre s₁ W T tl :=
    ⟨hsi, hdi, hcx, by omega, by omega, VG.Proof.AesCcm.X86_64.covers_left (by simpa using E₁.perm.wC (d := 0) (n := tl) (by omega)),
      by rw [hwr₁]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ⟨E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], by rw [hm₂, hm₁]⟩

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86_64.Args s K W SP N A D R nl al n tl) (Tb : VG.Proof.AesCcm.X86_64.TagBuf W SP D n T tl) (hTw : Covers [⟨T, tl⟩] s.wr)
    (hTr : (⟨SP, 8⟩ : Region).Disjoint ⟨T, tl⟩) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» v.callee v.suffix) s fun s' => gprPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem D n)
        (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ :=
    VG.Proof.AesCcm.X86_64.entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, VG.Proof.AesCcm.X86_64.Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => VG.Proof.AesCcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.Ccm.ctxCiph s₁.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    VG.Proof.AesCcm.X86_64.ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.seq ?_
  -- `Ctr₀`.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctrs_ok E₁ S₁ (Ar.nonce.of_eq rd₁ wr₁) Ar.h7 Ar.h13) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have f₂' : Frame (VG.Proof.AesCcm.X86_64.wR W SP) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  have S₂ := VG.Proof.AesCcm.X86_64.slots_mut L Ar.data.w (f₂'.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)) S₁
  -- The encrypted MAC at `W`.
  refine VG.Proof.AesCcm.X86_64.seq_assoc (WP.seq (VG.Proof.AesCcm.X86_64.macTag_ok v L E₂ S₂ Ar.rounds (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.hn c₂ (y := 0) (.inl rfl) (Ar.aad.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁))
    (Ar.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)) fun s₃ E₃ rd₃ wr₃ f₃ c₃ h₃ => ?_))
  have f₁₃ : Frame (VG.Proof.AesCcm.X86_64.wR W SP) s₁.mem s₃.mem := f₂'.trans (f₃.sub (VG.Proof.AesCcm.X86_64.tagR_wR W SP (by decide)))
  have S₃ := VG.Proof.AesCcm.X86_64.slots_mut L Ar.data.w (f₁₃.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)) S₁
  -- Counter mode.
  have C₃ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s₃ R (bytesAt s.mem N nl) D n :=
    ⟨L, Ar.rounds, S₃.rounds, by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.h7, by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.h13,
      by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.hn, c₃, Ar.data.of_eq (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁)),
      by rw [wr₃, wr₂, wr₁]; exact Ar.dw, Ar.dk⟩
  refine WP.mono (VG.Proof.AesCcm.X86_64.ctr_ok v C₃ E₃ S₃) fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_
  have f₁₄ : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s₁.mem s₄.mem := (f₁₃.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)).trans (f₄.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n))
  have fall : Frame (VG.Proof.AesCcm.X86_64.entryR W :: VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem s₄.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₄.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have rd₀₄ : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₀₄ : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  -- The tag copied to `T`.
  have hT₄ : s₄.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by rw [VG.Proof.AesCcm.X86_64.argT_kept fall Ar.argsW Ar.argsD, hT]
  have hTr₄ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 24) 8 := by
    have h := VG.Proof.AesCcm.X86_64.in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc] at h
    rw [rd₀₄, wr₀₄]; exact h
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.tagOut_ok E₄ (VG.Proof.AesCcm.X86_64.slots_mut L Ar.data.w f₁₄ S₁) Ar.t4 Ar.t16 hT₄ hTr₄
    (by rw [wr₀₄]; exact hTw) Tb.w) fun s₅ ⟨E₅, rd₅, wr₅, hm₅⟩ => ?_)
  have hx : (bytesAt s₄.mem W tl).length = tl := VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _
  have f₅ : Frame [⟨T, tl⟩] s₄.mem s₅.mem := by rw [hm₅]; exact VG.Proof.AesCcm.X86_64.writeBytes_frame' _ hx
  -- `restore`.
  have sv₅ : VG.Proof.AesCcm.X86_64.Saved s₅.mem W s.gpr := fun p hp => by
    rw [← VG.Proof.AesCcm.X86_64.saved_mut L Ar.data.w f₁₄ sv₁ p hp]
    have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact f₅.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Tb.w.sub_right (Lay.wSub (by omega))).symm) (by decide)
  obtain ⟨s₆, run₆, hg₆, hm₆, hsp₆, _⟩ := VG.Proof.AesCcm.X86_64.restore_ok E₅ sv₅
  refine WP.of_runBlock ⟨s₆, run₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₆ (.rbx, 112) (by decide)
    · exact hg₆ (.rbp, 120) (by decide)
    · rw [hsp₆, E₅.rsp, hsp]
    · exact hg₆ (.r12, 128) (by decide)
    · exact hg₆ (.r13, 136) (by decide)
    · exact hg₆ (.r14, 144) (by decide)
    · exact hg₆ (.r15, 152) (by decide)
  · rw [hm₆, hsp, f₅.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hTr) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (VG.Proof.AesCcm.X86_64.ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m K R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
    have c₂' : Spec.Ccm.ctxCiph s₂.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [VG.Proof.AesCcm.X86_64.ciph_mut L Ar.dk Ar.rounds (f₂'.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)), hK₁]
    have c₃' : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [VG.Proof.AesCcm.X86_64.ciph_mut L Ar.dk Ar.rounds (f₁₃.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)), hK₁]
    have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [VG.Proof.AesCcm.X86_64.buf_wR Ar.aad f₂', hent Ar.aad]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [VG.Proof.AesCcm.X86_64.buf_wR Ar.data f₂', hent Ar.data]
    have d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by rw [VG.Proof.AesCcm.X86_64.buf_wR Ar.data f₁₃, hent Ar.data]
    have w₄ : bytesAt s₄.mem W tl = bytesAt s₃.mem W tl := VG.Proof.AesCcm.X86_64.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by have := Ar.t16; omega))
          (by have := Ar.t16; omega) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 216) (k := 8) (.inl (by have := Ar.t16; omega))
          (by have := Ar.t16; omega) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 384) (k := 2176) (.inl (by have := Ar.t16; omega))
          (by have := Ar.t16; omega) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by have := Ar.t16; omega))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega))).symm) (by have := Ar.t16; omega)
    have d₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n :=
      VG.Proof.AesCcm.X86_64.bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Tb.d.symm) (by have := Ar.data.lt; omega)
    have t₅ : bytesAt s₅.mem T tl = bytesAt s₄.mem W tl := by
      have e := VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at s₄.mem T (o := 0) (n := tl) (bytesAt s₄.mem W tl) (by rw [hx]; omega)
        (by have := Ar.t16; omega)
      rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
        List.drop_eq_nil_of_le (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt, hx]), List.append_nil] at e
      rw [hm₅, e]
    have e0 : W + BitVec.ofNat 64 0 = W := BitVec.add_zero W
    rw [e0] at h₃
    have hY := congrArg List.length h₃
    rw [VG.Proof.AesCcm.X86_64.length_bytesAt, length_xorFrom] at hY
    simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hm₆, d₅, h₄, c₃', d₃, crypt_eq (hBC _)]
    · rw [hm₆, t₅, w₄, VG.Proof.AesCcm.X86_64.bytesAt_prefix s₃.mem W Ar.t16, h₃, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16,
        ← mac_eq _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; have := Ar.h13; omega), c₂', a₂, d₂]

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp (v : Ctr32Impl) {s : State} (h : sealX86_64.pre s) :
    WP isa («seal» v.callee v.suffix) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  have A := VG.Proof.AesCcm.X86_64.args_of_seal h
  VG.Proof.AesCcm.X86_64.seal_wp' v A.1.1 A.1.2 A.2.1 A.2.2 rfl rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl rfl
    (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.SealCT`. -/
section

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. Between the pieces, each run
has the public arguments, some `Ctr₀`, its buffers and the address of `tag`
on the stack (`Mid`), which every piece keeps (`ctrs_mid`, `mac_mid`,
`tag_mid`, `ctr_mid`); the pieces are related from it (`mac_rel`, `tag_rel`,
`crypt_rel`), and the entry, which loads `W` from the stack first, by the
taint analysis from the public arguments (`entry_rel`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its pieces before the copy
of the tag do not, and run the same from its states with `tag` only readable
(`rel_narrow`). The copy of the tag and the exit are related by the taint
analysis from the registers that correctness says agree (`sealTail_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- The address of `tag`, `T`, at `SP + 24`, apart from what the pieces
write. -/
structure ArgT (W SP D : Addr) (n : Nat) (T : Addr) (s : State) : Prop where
  val : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  rd : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8
  w : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩
  d : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩

theorem ArgT.mut {W SP D T : Addr} {n : Nat} {s s' : State} (h : VG.Proof.AesCcm.X86_64.ArgT W SP D n T s)
    (hf : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesCcm.X86_64.ArgT W SP D n T s' :=
  ⟨by rw [VG.Proof.AesCcm.X86_64.argT_kept (hf.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩) h.w h.d, h.val],
    by rw [hrd, hwr]; exact h.rd, h.w, h.d⟩

/-- A run between the pieces: the public arguments, some `Ctr₀` at `W + 48`,
the associated data and the data in its regions, and the address of the
tag. -/
def Mid (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s ∧ VG.Proof.AesCcm.X86_64.C0 W nl s ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s D n ∧ VG.Proof.AesCcm.X86_64.ArgT W SP D n T s

theorem ctrs_mid {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {s : State}
    (o : VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s) (hN : VG.Proof.AesCcm.X86_64.Buf K W SP s N nl) (hA : VG.Proof.AesCcm.X86_64.Buf K W SP s A al)
    (hD : VG.Proof.AesCcm.X86_64.Buf K W SP s D n) (hT : VG.Proof.AesCcm.X86_64.ArgT W SP D n T s) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa VG.Impl.AesCcm.X86_64.ctrs s (VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) :=
  WP.mono (VG.Proof.AesCcm.X86_64.ctrs_ok o.env o.sl hN h7 h13) fun _ ⟨E, f, c, rd, wr⟩ =>
    have f' : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem _ := (f.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩).sub
      (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)
    ⟨⟨E, VG.Proof.AesCcm.X86_64.slots_mut L hD.w f' o.sl, wr.trans o.wr⟩, ⟨_, VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _, c⟩, hA.of_eq rd wr, hD.of_eq rd wr,
      hT.mut f' rd wr⟩

theorem mac_mid (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s) : WP isa (mac v.callee v.suffix y) s (VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (VG.Proof.AesCcm.X86_64.mac_ok v L o.env o.sl hR hl h7 h13 ht4 ht16 hte hn' c hy hA hD) fun s' M => ?_
  refine ⟨o.macR L hD.w (by omega) M.env M.frame M.wr, ⟨nonce, hl, ?_⟩, hA.of_eq M.rd M.wr, hD.of_eq M.rd M.wr,
    hT.mut (M.frame.sub (VG.Proof.AesCcm.X86_64.macR_mut W SP D n (by omega))) M.rd M.wr⟩
  rw [VG.Proof.AesCcm.X86_64.bytesAt_frame M.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide), c]

theorem tag_mid (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s) : WP isa (tag v.callee y) s (VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (VG.Proof.AesCcm.X86_64.tag_ok v L o.env hR o.sl.rounds (by omega) (by omega) c hy) fun s' ⟨E, _, rd, wr, f, _⟩ => ?_
  have f' : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem s'.mem := f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by omega)⟩
    · exact ⟨VG.Proof.AesCcm.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨⟨E, VG.Proof.AesCcm.X86_64.slots_mut L hD.w f' o.sl, wr.trans o.wr⟩, ⟨nonce, hl, ?_⟩, hA.of_eq rd wr,
    hD.of_eq rd wr, hT.mut f' rd wr⟩
  rw [VG.Proof.AesCcm.X86_64.bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide), c]

/-- The context of counter mode, from a run between the pieces. -/
theorem Mid.ctx {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s) :
    ∃ nonce, VG.Proof.AesCcm.X86_64.CtrCtx K W SP s R nonce D n := by
  obtain ⟨o, ⟨nonce, hl, c⟩, -, hD, -⟩ := h
  exact ⟨nonce, L, hR, o.sl.rounds, by omega, by omega, by rw [hl]; exact hn', c, hD,
    by rw [o.wr]; exact VG.Proof.AesCcm.X86_64.covers_of_mem List.mem_cons_self, hdk⟩

theorem ctr_mid (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s) :
    WP isa (ctr v.callee) s (VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨nonce, C⟩ := h.ctx L hR h7 h13 hn' hdk
  obtain ⟨o, ⟨nonce', hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (VG.Proof.AesCcm.X86_64.ctr_ok v C o.env o.sl) fun s' ⟨E, rd, wr, f, _⟩ => ?_
  refine ⟨⟨E, VG.Proof.AesCcm.X86_64.slots_mut L hD.w (f.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n)) o.sl, wr.trans o.wr⟩, ⟨nonce', hl, ?_⟩,
    hA.of_eq rd wr, hD.of_eq rd wr, hT.mut (f.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n)) rd wr⟩
  rw [VG.Proof.AesCcm.X86_64.bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (hD.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c]

/-- A run after the entry: the public arguments, its buffers and the address
of the tag. -/
def Pre₀ (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s N nl ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s A al ∧ VG.Proof.AesCcm.X86_64.Buf K W SP s D n ∧
    VG.Proof.AesCcm.X86_64.ArgT W SP D n T s

theorem ctrs_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT []) VG.Impl.AesCcm.X86_64.ctrs hc).isSome = true := ⟨_, by taint_decide⟩

theorem restore_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT []) (.block VG.Impl.AesCcm.X86_64.restore) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `seal` after its entry, up to the copy of the tag, in two runs. -/
theorem sealFront_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 64) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.X86_64.Pre₀ K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Pre₀ K W SP R N A D nl al n tl T s₂) :
    RelCT isa P (sealFront v.callee v.suffix) fun s₁ s₂ =>
      True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂ := by
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) VG.Proof.AesCcm.X86_64.ctrs_check).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) fun s₁ s₂ h => by
      obtain ⟨⟨o₁, n₁, a₁, d₁, t₁⟩, ⟨o₂, n₂, a₂, d₂, t₂⟩⟩ := hP _ _ h
      exact ⟨VG.Proof.AesCcm.X86_64.ctrs_mid L o₁ n₁ a₁ d₁ t₁ h7 h13, VG.Proof.AesCcm.X86_64.ctrs_mid L o₂ n₂ a₂ d₂ t₂ h7 h13⟩
  have r₂ := (VG.Proof.AesCcm.X86_64.mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1⟩,
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.1,
      VG.Proof.AesCcm.X86_64.mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.2⟩
  have r₃ := (VG.Proof.AesCcm.X86_64.tag_rel v L hR hDW hn h7 h13 (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.tag_mid v L hR h7 h13 (.inl rfl) h.2.1, VG.Proof.AesCcm.X86_64.tag_mid v L hR h7 h13 (.inl rfl) h.2.2⟩
  have r₄ := (VG.Proof.AesCcm.X86_64.rel_of_pt (c := ctr v.callee)
    (P := fun s₁ s₂ => True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact VG.Proof.AesCcm.X86_64.crypt_rel v C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.ctr_mid v L hR h7 h13 hn' hdk h.2.1, VG.Proof.AesCcm.X86_64.ctr_mid v L hR h7 h13 hn' hdk h.2.2⟩
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (r₄.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩)))

/-- `seal` after its entry, up to the copy of the tag, in one run. -/
theorem sealFront_mid (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {s : State} (h : VG.Proof.AesCcm.X86_64.Pre₀ K W SP R N A D nl al n tl T s) :
    WP isa (sealFront v.callee v.suffix) s (VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, hN, hA, hD, hT⟩ := h
  exact WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctrs_mid L o hN hA hD hT h7 h13) fun _ h₁ =>
    WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h₁) fun _ h₂ =>
    WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.tag_mid v L hR h7 h13 (.inl rfl) h₂) fun _ h₃ => VG.Proof.AesCcm.X86_64.ctr_mid v L hR h7 h13 hn' hdk h₃)))

/-! ## Moving the tag to the regions read only -/

/-- `s` with the tag `⟨T, tl⟩` read only, and the data and `W` its writable
regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T : Addr) (tl : Nat) (W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 2560⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-! ## The copy of the tag and the exit -/

/-- What the copy of the tag needs of a run: `r15` and `rsp` hold `W` and
`SP`, the tag length is in its slot, and the address of the tag `T` on the
stack, all where the run may read them. -/
def SealOut (W SP T : Addr) (tl : Nat) (s : State) : Prop :=
  s.gpr .r15 = W ∧ s.gpr .rsp = SP ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 tl ∧
    InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 ∧ s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8

theorem Mid.sealOut {K W SP : Addr} {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {σ s : State}
    (h : VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T σ) (hg : σ.gpr = s.gpr) (hm : σ.mem = s.mem)
    (hc : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) : VG.Proof.AesCcm.X86_64.SealOut W SP T tl s := by
  obtain ⟨o, -, -, -, hT⟩ := h
  refine ⟨by rw [← hg]; exact o.env.r15, by rw [← hg]; exact o.env.rsp, by rw [← hm]; exact o.sl.tl,
    hc _ _ (o.env.perm.wR (show 208 + 8 ≤ 2560 by decide)), by rw [← hm]; exact hT.val, hc _ _ hT.rd⟩

/-- The arguments of the copy of the tag. -/
theorem tagOutArgs_ok {W SP T : Addr} {tl : Nat} {s : State} (h : VG.Proof.AesCcm.X86_64.SealOut W SP T tl s) :
    WP isa (.block [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))]) s
      fun s' => s'.gpr .rdi = T ∧ s'.gpr .rsi = W ∧ s'.gpr .rcx = BitVec.ofNat 64 tl ∧ s'.gpr .r15 = W := by
  obtain ⟨h15, hsp, htl, r₁, hT, r₂⟩ := h
  refine WP.of_runBlock ⟨_, by crun [h15, hsp, r₁, r₂], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hsp, hT]
  · simp [gpr_setReg, h15]
  · simp [gpr_setReg, htl]
  · simp [gpr_setReg, h15]

theorem tagOutArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r15, .rsp])
    (.block [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))]) hc).isSome =
      true := ⟨_, by taint_decide⟩

theorem tagCopy_check : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rcx, .r15])
    (.seq copyLoop (.block VG.Impl.AesCcm.X86_64.restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `(a; b); c`, related as `a; (b; c)`. -/
theorem rel_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- The copy of the tag and the exit, in two runs with the same `W`, `SP`,
tag length and tag. -/
theorem sealTail_rel {W SP T : Addr} {tl : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesCcm.X86_64.SealOut W SP T tl s₁ ∧ VG.Proof.AesCcm.X86_64.SealOut W SP T tl s₂) :
    RelCT isa P (.seq tagOut (.block VG.Impl.AesCcm.X86_64.restore)) fun _ _ => True := by
  have a := (VG.Proof.AesCcm.X86_64.rel_taintR (P := P) [.r15, .rsp] (fun s₁ s₂ h r hr => by
      obtain ⟨⟨a₁, b₁, -⟩, ⟨a₂, b₂, -⟩⟩ := hP _ _ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) VG.Proof.AesCcm.X86_64.tagOutArgs_check).wp
    (F₁ := fun (s : State) => s.gpr .rdi = T ∧ s.gpr .rsi = W ∧ s.gpr .rcx = BitVec.ofNat 64 tl ∧ s.gpr .r15 = W)
    (F₂ := fun (s : State) => s.gpr .rdi = T ∧ s.gpr .rsi = W ∧ s.gpr .rcx = BitVec.ofNat 64 tl ∧ s.gpr .r15 = W)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.tagOutArgs_ok (hP _ _ h).1, VG.Proof.AesCcm.X86_64.tagOutArgs_ok (hP _ _ h).2⟩
  have b := VG.Proof.AesCcm.X86_64.rel_taintR (P := fun s₁ s₂ => True ∧
      (s₁.gpr .rdi = T ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 tl ∧ s₁.gpr .r15 = W) ∧
      (s₂.gpr .rdi = T ∧ s₂.gpr .rsi = W ∧ s₂.gpr .rcx = BitVec.ofNat 64 tl ∧ s₂.gpr .r15 = W))
    (c := .seq copyLoop (.block VG.Impl.AesCcm.X86_64.restore)) [.rdi, .rsi, .rcx, .r15] (fun _ _ h r hr => by
      obtain ⟨-, ⟨a₁, b₁, c₁, d₁⟩, ⟨a₂, b₂, c₂, d₂⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [d₁, d₂]) VG.Proof.AesCcm.X86_64.tagCopy_check
  exact VG.Proof.AesCcm.X86_64.rel_assoc' (RelCT.seq a b)

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 40) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 40))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by crun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 40))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 40) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 40) 8)
    (hE₁ : WP isa (.block VG.Impl.AesCcm.X86_64.entry) s₀ F₁) (hE₂ : WP isa (.block VG.Impl.AesCcm.X86_64.entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block VG.Impl.AesCcm.X86_64.entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (VG.Proof.AesCcm.X86_64.rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      VG.Proof.AesCcm.X86_64.entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.AesCcm.X86_64.loadW_ok hr₁, VG.Proof.AesCcm.X86_64.loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block VG.Impl.AesCcm.X86_64.entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 40))]) (l₂ := entry.tail) (RelCT.seq l
      (VG.Proof.AesCcm.X86_64.rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) VG.Proof.AesCcm.X86_64.entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

/-- What the entry leaves, for the arguments: the environment, the slots, the
same permissions, and the address of the tag still at `SP + 24`. -/
theorem entry_post {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86_64.Args s K W SP N A D R nl al n tl) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (.block VG.Impl.AesCcm.X86_64.entry) s fun s₁ => VG.Proof.AesCcm.X86_64.Env K W SP s₁ ∧ VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s₁.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ VG.Proof.AesCcm.X86_64.ArgT W SP D n T s₁ := by
  obtain ⟨s₁, run₁, E₁, S₁, _, f₁, rd₁, wr₁⟩ :=
    VG.Proof.AesCcm.X86_64.entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  have hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8 := by
    have h := VG.Proof.AesCcm.X86_64.in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc] at h
    exact h
  refine WP.of_runBlock ⟨s₁, run₁, E₁, S₁, rd₁, wr₁, ⟨?_, by rw [rd₁, wr₁]; exact hTr, Ar.argsW, Ar.argsD⟩⟩
  rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.AesCcm.X86_64.argT_disj (n := n) Ar.argsW Ar.argsD _ List.mem_cons_self) (by decide), hT]

theorem argW_in {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} (Ar : VG.Proof.AesCcm.X86_64.Args s K W SP N A D R nl al n tl)
    (hsp : s.gpr .rsp = SP) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 40) 8 := by
  have h := VG.Proof.AesCcm.X86_64.in_off (d := 32) (n := 8) Ar.args (by decide) (by decide)
  rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc] at h
  rw [hsp]; exact h

theorem pub_regs {s₀ s₀' : State} (hq : VG.Proof.AesCcm.onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-- What the entry of `seal` leaves: with the tag read only, a run after the
entry. -/
def SealIn (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩] ∧ VG.Proof.AesCcm.X86_64.Pre₀ K W SP R N A D nl al n tl T (VG.Proof.AesCcm.X86_64.narrowT D n T tl W s)

theorem sealIn_of {s s₁ : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86_64.Args s K W SP N A D R nl al n tl) (hwr : s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩])
    (h : VG.Proof.AesCcm.X86_64.Env K W SP s₁ ∧ VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ VG.Proof.AesCcm.X86_64.ArgT W SP D n T s₁) :
    VG.Proof.AesCcm.X86_64.SealIn K W SP R N A D nl al n tl T s₁ := by
  obtain ⟨E, S, rd, wr, hT⟩ := h
  have hwr₁ : s₁.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩] := by rw [wr]; exact hwr
  have hc : Covers (s₁.rd ++ s₁.wr) ((VG.Proof.AesCcm.X86_64.narrowT D n T tl W s₁).rd ++ (VG.Proof.AesCcm.X86_64.narrowT D n T tl W s₁).wr) := by
    rw [hwr₁]; exact VG.Proof.AesCcm.X86_64.covers_narrowT _ _ _ _
  have hb : ∀ {P : Addr} {len : Nat}, VG.Proof.AesCcm.X86_64.Buf K W SP s P len → VG.Proof.AesCcm.X86_64.Buf K W SP (VG.Proof.AesCcm.X86_64.narrowT D n T tl W s₁) P len := fun hP =>
    { hP.of_eq rd wr with rd := (hP.of_eq rd wr).rd.trans hc }
  exact ⟨hwr₁, ⟨⟨E.r13, E.r15, E.rsp, E.perm.k.trans hc, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩, S, rfl⟩, hb Ar.nonce, hb Ar.aad, hb Ar.data,
    ⟨hT.val, hc _ _ hT.rd, hT.w, hT.d⟩⟩

theorem entry_seal {s : State} (hp : sealX86_64.pre s) :
    WP isa (.block VG.Impl.AesCcm.X86_64.entry) s (VG.Proof.AesCcm.X86_64.SealIn (s.gpr .rdi) (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .r8)
      (VG.Proof.AesCcm.arg s 0) (s.gpr .rcx).toNat (s.gpr .r9).toNat (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 3).toNat (VG.Proof.AesCcm.arg s 2)) :=
  WP.mono (VG.Proof.AesCcm.X86_64.entry_post (VG.Proof.AesCcm.X86_64.args_of_seal hp).1.1 rfl rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl rfl
      (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm)
    fun _ h => VG.Proof.AesCcm.X86_64.sealIn_of (VG.Proof.AesCcm.X86_64.args_of_seal hp).1.1 hp.2.1 h

/-- The second run, with the first's public arguments. -/
theorem entry_seal_pub {s₀ s₀' : State} (hp' : sealX86_64.pre s₀') (hq : VG.Proof.AesCcm.onePub s₀ s₀') :
    WP isa (.block VG.Impl.AesCcm.X86_64.entry) s₀' (VG.Proof.AesCcm.X86_64.SealIn (s₀.gpr .rdi) (VG.Proof.AesCcm.arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .r8) (VG.Proof.AesCcm.arg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (VG.Proof.AesCcm.arg s₀ 1).toNat (VG.Proof.AesCcm.arg s₀ 3).toNat
      (VG.Proof.AesCcm.arg s₀ 2)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), qa 3 (by decide), qa 4 (by decide), q1, q2, q3, q4,
    q5, q6, q7]
  exact VG.Proof.AesCcm.X86_64.entry_seal hp'

/-- `vg_aes_ccm_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : Ctr32Impl) {s₀ s₀' : State} (hp : sealX86_64.pre s₀) (hp' : sealX86_64.pre s₀')
    (hq : sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callee v.suffix) fun _ _ => True := by
  have Ar := (VG.Proof.AesCcm.X86_64.args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (VG.Proof.AesCcm.X86_64.entry_rel (VG.Proof.AesCcm.X86_64.pub_regs hq) (hq.2.2.2.2.2.2.2 4 (by decide)) (VG.Proof.AesCcm.X86_64.argW_in Ar rfl)
    (VG.Proof.AesCcm.X86_64.argW_in (VG.Proof.AesCcm.X86_64.args_of_seal hp').1.1 rfl) (VG.Proof.AesCcm.X86_64.entry_seal hp) (VG.Proof.AesCcm.X86_64.entry_seal_pub hp' hq)) ?_
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := sealFront v.callee v.suffix)
    (P := fun s₁ s₂ => True ∧
      VG.Proof.AesCcm.X86_64.SealIn (s₀.gpr .rdi) (VG.Proof.AesCcm.arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (VG.Proof.AesCcm.arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (VG.Proof.AesCcm.arg s₀ 1).toNat (VG.Proof.AesCcm.arg s₀ 3).toNat (VG.Proof.AesCcm.arg s₀ 2) s₁ ∧
      VG.Proof.AesCcm.X86_64.SealIn (s₀.gpr .rdi) (VG.Proof.AesCcm.arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (VG.Proof.AesCcm.arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (VG.Proof.AesCcm.arg s₀ 1).toNat (VG.Proof.AesCcm.arg s₀ 3).toNat (VG.Proof.AesCcm.arg s₀ 2) s₂)
    [⟨VG.Proof.AesCcm.arg s₀ 2, (VG.Proof.AesCcm.arg s₀ 3).toNat⟩]
    [⟨VG.Proof.AesCcm.arg s₀ 0, (VG.Proof.AesCcm.arg s₀ 1).toNat⟩, ⟨VG.Proof.AesCcm.arg s₀ 4, 2560⟩]
    (VG.Proof.AesCcm.X86_64.sealFront_rel v L Ar.rounds Ar.data.w hn Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.aad.lt Ar.hn Ar.dk
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨VG.Proof.AesCcm.arg s₀ 0, (VG.Proof.AesCcm.arg s₀ 1).toNat⟩, ⟨VG.Proof.AesCcm.arg s₀ 2, (VG.Proof.AesCcm.arg s₀ 3).toNat⟩, ⟨VG.Proof.AesCcm.arg s₀ 4, 2560⟩] →
          Covers ([⟨VG.Proof.AesCcm.arg s₀ 2, (VG.Proof.AesCcm.arg s₀ 3).toNat⟩] ++ [⟨VG.Proof.AesCcm.arg s₀ 0, (VG.Proof.AesCcm.arg s₀ 1).toNat⟩, ⟨VG.Proof.AesCcm.arg s₀ 4, 2560⟩]) s.wr ∧
          Covers [⟨VG.Proof.AesCcm.arg s₀ 0, (VG.Proof.AesCcm.arg s₀ 1).toNat⟩, ⟨VG.Proof.AesCcm.arg s₀ 4, 2560⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := VG.Proof.AesCcm.X86_64.sealFront_mid v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn Ar.dk p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := VG.Proof.AesCcm.X86_64.sealFront_mid v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn Ar.dk p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (VG.Proof.AesCcm.X86_64.sealTail_rel fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.sealOut g₁ h₁ c₁, m₂.sealOut g₂ h₂ c₂⟩)

theorem seal_ct (v : Ctr32Impl) : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesCcm.X86_64.seal_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Mask`. -/
section

/-!
# AES-CCM on x86-64: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`, for `ok` 1 or 0: the data stays if the tags were equal,
and is zeroed if not (`mask_ok`). Its whole words go 8 bytes at a time
(`maskWords_wp`), the rest one at a time (`maskBytes_wp`); both loops keep
the first `j` bytes masked (`MInv`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hbp : s.gpr .rbp = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rbp)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r12 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h12, h10, BitVec.mul_one]; simp
  refine ⟨_, by crun [maskByte, ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11, mask_byte]
  · simp [gpr_setReg, h10]
  · simp [h10, hbp]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

theorem mask_word (v : BitVec 64) (c : Bool) :
    v &&& ((0 : BitVec 64) - (if c then 1 else 0)) = if c then v else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskWord_ok (s : State) {P : Addr} {j w : Nat} {c : Bool} (h12 : s.gpr .r12 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hcx : s.gpr .rcx = BitVec.ofNat 64 w)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 8) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem maskByte), .alu .and .rax (.reg .r11), .store maskByte .rax,
        .alu .add .r10 (imm 8), .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j)
        (if c then s.mem.readW (P + BitVec.ofNat 64 j) 64 else (0 : BitVec 64)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 8 ∧ s'.gpr .rcx = BitVec.ofNat 64 w - 1 ∧
      s'.zf = some (BitVec.ofNat 64 w - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r12 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h12, h10, BitVec.mul_one]; simp
  refine ⟨_, by crun [maskByte, ea, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h11,
      mask_word]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, hcx]
  · simp [gpr_setReg, hcx]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, VG.Proof.AesCcm.X86_64.length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

theorem mask_add (m : Mem) (P : Addr) (c : Bool) (a b : Nat) :
    (if c then bytesAt m P (a + b) else zeros (a + b)) =
      (if c then bytesAt m P a else zeros a) ++
        (if c then bytesAt m (P + BitVec.ofNat 64 a) b else zeros b) := by
  cases c <;> simp [zeros, VG.Proof.Cmac.Stream.bytesAt_append, ← List.replicate_append_replicate]

/-- A word written is its 8 bytes written. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 64) :
    m.writeW a v = writeBytes m a ((List.range 8).map fun k => v.extractLsb' (8 * k) 8) :=
  write_eq_writeBytes m a 8 v

/-- The word at `a`, or zero, written back: the 8 bytes at `a` masked. -/
theorem writeW_mask (m m' : Mem) (a : Addr) (c : Bool) :
    m'.writeW a (if c then m.readW a 64 else (0 : BitVec 64)) =
      writeBytes m' a (if c then bytesAt m a 8 else zeros 8) := by
  rw [writeW_eq_writeBytes]
  refine congrArg (writeBytes m' a) ?_
  cases c
  · simp [zeros]; decide
  · simp only [ite_true, bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    rw [← Mem.extractLsb'_read m a (n := 8) hk]
    rfl

/-- What both loops keep: the first `j` bytes of the data masked. -/
structure MInv (s s₁ t : State) (D : Addr) (c : Bool) (j : Nat) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j)
  keep : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .rcx → t.gpr r = s₁.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem MInv.frame {s s₁ t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s s₁ t D c j) :
    Frame [⟨D, j⟩] s.mem t.mem := by
  rw [h.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)

/-- The bytes from `j` on are as they were. -/
theorem MInv.at {s s₁ t : State} {D : Addr} {c : Bool} {j i : Nat} (h : MInv s s₁ t D c j) (hi : j ≤ i)
    (hi' : i < 2 ^ 64) : t.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) :=
  (h.frame (D + BitVec.ofNat 64 i) fun r hr hcon => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Mem.sub_ofNat_toNat D hi'] at hcon; omega)

theorem MInv.readW {s s₁ t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s s₁ t D c j)
    (hj : j + 8 < 2 ^ 64) : t.mem.readW (D + BitVec.ofNat 64 j) 64 = s.mem.readW (D + BitVec.ofNat 64 j) 64 := by
  refine Mem.readW_congr fun k hk => ?_
  simp only [Offset.add_add]
  exact h.at (by omega) (by omega)

/-- The words: from `j = 8 i`, with `w − i` words left in `rcx`, to `8 w`. -/
theorem maskWords_wp {s s₁ t : State} {D : Addr} {n : Nat} {c : Bool} {i : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s₁.gpr .r12 = D) (h11 : s₁.gpr .r11 = 0 - (if c then 1 else 0))
    (hi : i < n / 8) (ht : MInv s s₁ t D c (8 * i)) (hcx : t.gpr .rcx = BitVec.ofNat 64 (n / 8 - i)) :
    WP isa maskWords t fun t' => MInv s s₁ t' D c (8 * (n / 8)) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n / 8 - i ∧ i < n / 8 ∧ MInv s s₁ t D c (8 * i) ∧
      t.gpr .rcx = BitVec.ofNat 64 (n / 8 - i)) ?_ (n / 8 - i) t ⟨i, rfl, hi, ht, hcx⟩
  rintro k t ⟨i, rfl, hi, ht, hcx⟩
  have hin : 8 * i + 8 ≤ n := by omega
  have cov (rs : List Region) (h : Covers [⟨D, n⟩] rs) : InRegions rs (D + BitVec.ofNat 64 (8 * i)) 8 :=
    h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hin (by omega)⟩
  obtain ⟨t', run', mem', r10', rcx', zf', g', rd', wr'⟩ := maskWord_ok t (P := D) (j := 8 * i)
    (w := n / 8 - i) (c := c) (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) ht.r10
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h11]) hcx
    (by rw [ht.rd, ht.wr]; exact cov _ hD) (by rw [ht.wr]; exact cov _ hDw)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (8 * (i + 1)) else zeros (8 * (i + 1))) := by
    rw [mem', ht.readW (by omega), ht.mem, writeW_mask, show 8 * (i + 1) = 8 * i + 8 by omega, mask_add,
      ← writeBytes_append _ _ _ _ (by rw [length_mask, length_mask]; omega), length_mask]
  have hcx' : t'.gpr .rcx = BitVec.ofNat 64 (n / 8 - (i + 1)) := by
    rw [rcx', show n / 8 - i = (n / 8 - (i + 1)) + 1 by omega, ← succ_ofNat, BitVec.add_sub_cancel]
  have hz : t'.zf = some (decide (i + 1 = n / 8)) := by
    rw [zf', show BitVec.ofNat 64 (n / 8 - i) - 1 = BitVec.ofNat 64 (n / 8 - (i + 1)) by
      rw [show n / 8 - i = (n / 8 - (i + 1)) + 1 by omega, ← succ_ofNat, BitVec.add_sub_cancel]]
    by_cases he : i + 1 = n / 8
    · rw [he, Nat.sub_self]; simp
    · have : BitVec.ofNat 64 (n / 8 - (i + 1)) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
      rw [beq_eq_false_iff_ne.mpr this]; simp [he]
  have ht' : MInv s s₁ t' D c (8 * (i + 1)) :=
    ⟨by rw [r10', show 8 * (i + 1) = 8 * i + 8 by omega, BitVec.ofNat_add]; rfl, hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂ h₃, ht.keep r h₁ h₂ h₃], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : i + 1 = n / 8
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n / 8 - (i + 1), by omega, i + 1, rfl, by omega, ht', hcx'⟩

/-- The last bytes: from `j < n` to `n`. -/
theorem maskBytes_wp {s s₁ t : State} {D : Addr} {n : Nat} {c : Bool} {j : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h12 : s₁.gpr .r12 = D) (h11 : s₁.gpr .r11 = 0 - (if c then 1 else 0))
    (hbp : s₁.gpr .rbp = BitVec.ofNat 64 n) (hj : j < n) (ht : MInv s s₁ t D c j) :
    WP isa maskBytes t fun t' => MInv s s₁ t' D c n := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ MInv s s₁ t D c j) ?_ (n - j) t ⟨j, rfl, hj, ht⟩
  rintro k t ⟨j, rfl, hj, ht⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (j := j) (L := n) (c := c)
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) ht.r10
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h11])
    (by rw [ht.keep _ (by decide) (by decide) (by decide), hbp]) (by rw [ht.rd, ht.wr]; exact in_of_covers hD hj hn)
    (by rw [ht.wr]; exact in_of_covers hDw hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
    rw [mem', ht.at (Nat.le_refl _) (by omega), ht.mem, mask_succ,
      writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have ht' : MInv s s₁ t' D c (j + 1) :=
    ⟨by rw [r10', succ_ofNat], hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂, ht.keep r h₁ h₂ h₃], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, ht'⟩

theorem ofNat_shr3 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (hD : VG.Proof.AesCcm.X86_64.Buf K W SP s D n) (hDw : Covers [⟨D, n⟩] s.wr) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0) :
    WP isa mask s fun s' => VG.Proof.AesCcm.X86_64.Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have hn := hD.lt
  have hd := S.data
  have hl := S.len
  obtain ⟨s₁, run₁, m₁, h12₁, hbp₁, h11₁, r10₁, rcx₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .mov .rcx (.reg .rbp),
        .shift .shr .rcx 3, .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      s₁.gpr .r11 = 0 - (if c then 1 else 0) ∧ s₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (n / 8) ∧ s₁.zf = some (decide (n / 8 = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂, r₃, execShift], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl, ofNat_shr3 hn]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hl, ofNat_shr3 hn, VG.Proof.AesCcm.X86_64.and_self_beq (show n / 8 < 2 ^ 64 by omega)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep g₁ rd₁ wr₁
  have hD' : Covers [⟨D, n⟩] (s.rd ++ s.wr) := hD.rd
  have inv₀ : MInv s s₁ s₁ D c 0 :=
    ⟨r10₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun _ _ _ _ => rfl, rd₁, wr₁⟩
  -- The words.
  have words : WP isa (.ite .e (.block []) maskWords) s₁ fun t => MInv s s₁ t D c (8 * (n / 8)) := by
    refine WP.ite (decide (n / 8 = 0)) (VG.Proof.AesCcm.X86_64.eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₀
    · exact maskWords_wp hn hD' hDw h12₁ h11₁ (Nat.pos_of_ne_zero (of_decide_eq_false hb))
        (by simpa using inv₀) (by rw [rcx₁, Nat.sub_zero])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono words fun t ht => ?_)
  -- The rest.
  have fin {t : State} (ht : MInv s s₁ t D c n) :
      VG.Proof.AesCcm.X86_64.Env K W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) :=
    ⟨E₁.keep (fun r hr => ht.keep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [ht.rd, rd₁]) (by rw [ht.wr, wr₁]), ht.rd, ht.wr, ht.mem⟩
  obtain ⟨t₁, run₂, zf₂, g₂, m₂, rd₂, wr₂⟩ : ∃ t₁, runBlock isa [.alu .cmp .r10 (.reg .rbp)] t = some t₁ ∧
      t₁.zf = some (decide (8 * (n / 8) = n)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, ht.r10, ht.keep .rbp (by decide) (by decide) (by decide), hbp₁]
      rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    all_goals rfl
  have ht₁ : MInv s s₁ t₁ D c (8 * (n / 8)) :=
    ⟨by rw [g₂, ht.r10], by rw [m₂, ht.mem], fun r h₁ h₂ h₃ => by rw [g₂, ht.keep r h₁ h₂ h₃],
      by rw [rd₂, ht.rd], by rw [wr₂, ht.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₂, ?_⟩)
  refine WP.ite (decide (8 * (n / 8) = n)) (VG.Proof.AesCcm.X86_64.eval_e zf₂) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · rw [← of_decide_eq_true hb] at fin ⊢; exact fin ht₁
  · exact WP.mono (maskBytes_wp hn hD' hDw h12₁ h11₁ hbp₁ (by have := of_decide_eq_false hb; omega) ht₁)
      fun t' ht' => fin ht'

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Open`. -/
section

/-!
# AES-CCM on x86-64: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`,
counter mode over the data (which decrypts it), the encrypted MAC of the
plaintext at `W + 96`, then the comparison of its first `t` bytes with the
received tag at `T`, whose address is on the stack, the mask of the data and
`restore` (`openTail_ok`, `open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The tag length loaded into `rbx`, and the address of the received tag
`T` into `rsi`. -/
theorem loadTag_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8) :
    ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rbx = BitVec.ofNat 64 tl ∧ s₁.gpr .rsi = T ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  have rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have htl := S.tl
  refine ⟨_, by crun [h15, hsp, rt, hTr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, htl]
  · simp [gpr_setReg, hsp, hT]
  · intro r a b; simp [gpr_setReg, a, b]
  all_goals rfl

/-- The comparison of the encrypted MAC at `W + 96` with the received tag at
`T`, and `ok` stored at `W + 224`. -/
theorem openCmp_ok {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (ht1 : 1 ≤ tl) (ht16 : tl ≤ 16) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.block [.store (at_ .r15 okO) .rax])))) s fun s₄ =>
      VG.Proof.AesCcm.X86_64.Env K W SP s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩] s.mem s₄.mem ∧
      s₄.mem.readW (W + BitVec.ofNat 64 224) 64 =
        if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then 1 else 0 := by
  obtain ⟨s₁, run₁, hm₁, hbx₁, hsi₁, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86_64.loadTag_ok E S hT hTr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesCcm.X86_64.Env K W SP s₁ := E.keep (fun r hr => hg₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    hrd₁ hwr₁
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.recv_ok E₁ hbx₁ ht1 ht16 hsi₁ (by rw [hrd₁, hwr₁]; exact hTc)
      (hTW.sub_right (Lay.wSub (by decide)))) fun s₂ ⟨E₂, hR₂, f₂, hbx₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.cmp_ok L (o := 96) (by decide) E₂ (by rw [hbx₂, hbx₁]) ht1 ht16 (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _) hR₂)
    fun s₃ ⟨E₃, hax₃, f₃, rd₃, wr₃⟩ => ?_)
  -- `ok` in `W + 224`.
  have h15₃ := E₃.r15
  have wo := E₃.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₄, run₄, hm₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.store (at_ .r15 okO) .rax] s₃ = some s₄ ∧
      s₄.mem = s₃.mem.writeW (W + BitVec.ofNat 64 224) (s₃.gpr .rax) ∧ s₄.gpr = s₃.gpr ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr := by
    refine ⟨_, by crun [h15₃, wo], ?_, ?_, ?_, ?_⟩ <;> rfl
  have E₄ : VG.Proof.AesCcm.X86_64.Env K W SP s₄ := E₃.keep (fun r _ => by rw [hg₄]) hrd₄ hwr₄
  have f₄ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₃.mem s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₀₄w : Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩] s.mem s₄.mem := by
    rw [← hm₁]
    refine ((f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have rd₀₄ : s₄.rd = s.rd := by rw [hrd₄, rd₃, rd₂, hrd₁]
  have wr₀₄ : s₄.wr = s.wr := by rw [hwr₄, wr₃, wr₂, hwr₁]
  have hV : bytesAt s₂.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem (W + BitVec.ofNat 64 96) tl := by
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide))
      (by omega), hm₁]
  rw [hV, hm₁] at hax₃
  refine WP.of_runBlock ⟨s₄, run₄, E₄, rd₀₄, wr₀₄, f₀₄w, ?_⟩
  rw [hm₄, Mem.readW_writeW_self64, hax₃]

/-- From the encrypted MAC at `W + 96` on: the comparison, the mask and the
restore. -/
theorem openTail_ok {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {s : State} (E : VG.Proof.AesCcm.X86_64.Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : VG.Proof.AesCcm.X86_64.Slots W R N A D nl al n tl s.mem) (hD : VG.Proof.AesCcm.X86_64.Buf K W SP s D n) (hDw : Covers [⟨D, n⟩] s.wr)
    (ht1 : 1 ≤ tl) (ht16 : tl ≤ 16) {g : Reg → BitVec 64} (sv : VG.Proof.AesCcm.X86_64.Saved s.mem W g) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 okO) .rax]) (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++
        VG.Impl.AesCcm.X86_64.restore))))))) s fun s' =>
      (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.gpr .rsp = SP ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then 1 else 0) ∧
      bytesAt s'.mem D n =
        (if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then bytesAt s.mem D n else zeros n) ∧
      Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩, ⟨D, n⟩] s.mem s'.mem := by
  refine VG.Proof.AesCcm.X86_64.seq_assoc4 (WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.openCmp_ok L E S ht1 ht16 hT hTr hTc hTW)
    fun s₄ ⟨E₄, rd₀₄, wr₀₄, f₀₄w, hok'⟩ => ?_))
  have f₀₄ : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem s₄.mem := f₀₄w.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.AesCcm.X86_64.wK W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨VG.Proof.AesCcm.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  have S₄ := VG.Proof.AesCcm.X86_64.slots_mut L hD.w f₀₄ S
  obtain ⟨c, hc⟩ : ∃ c, c = decide (bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl) := ⟨_, rfl⟩
  have hok : s₄.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0 := by
    rw [hok', hc]; simp only [decide_eq_true_eq]
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.mask_ok E₄ S₄ (hD.of_eq rd₀₄ wr₀₄) (by rw [wr₀₄]; exact hDw) hok)
    fun s₅ ⟨E₅, rd₅, wr₅, hm₅⟩ => ?_)
  -- `ok` in `rax`, and the registers back.
  have f₅ : Frame [⟨D, n⟩] s₄.mem s₅.mem := by
    rw [hm₅]; exact VG.Proof.AesCcm.X86_64.writeBytes_frame' _ (VG.Proof.AesCcm.X86_64.length_mask _ _ _ _)
  have hok₅ : s₅.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0 := by
    rw [f₅.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hD.w.sub_right (Lay.wSub (by decide))).symm)
      (by decide), hok]
  have h15₅ := E₅.r15
  have ro := E₅.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₆, run₆, hm₆, hax₆, hg₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₅ = some s₆ ∧
      s₆.mem = s₅.mem ∧ s₆.gpr .rax = (if c then 1 else 0) ∧ (∀ r, r ≠ .rax → s₆.gpr r = s₅.gpr r) ∧
      s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by crun [h15₅, ro], ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, hok₅]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₆ : VG.Proof.AesCcm.X86_64.Env K W SP s₆ := E₅.keep (fun r hr => hg₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₆ hwr₆
  have f₀₆ : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem s₆.mem := by
    rw [hm₆]; exact f₀₄.trans (f₅.sub fun r hr => ⟨r, by simp at hr ⊢; simp [hr], fun _ h => h⟩)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, hax₇⟩ := VG.Proof.AesCcm.X86_64.restore_ok E₆ (VG.Proof.AesCcm.X86_64.saved_mut L hD.w f₀₆ sv)
  refine WP.of_runBlock ⟨s₇, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₆, Option.bind_some, run₇], hg₇,
    by rw [hsp₇, E₆.rsp], ?_, ?_, ?_⟩
  · rw [hax₇, hax₆, hc]; simp only [decide_eq_true_eq]
  · have hx : (if c then bytesAt s₄.mem D n else zeros n).length = n := VG.Proof.AesCcm.X86_64.length_mask _ _ _ _
    have e := VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at s₄.mem D (o := 0) (n := n) (if c then bytesAt s₄.mem D n else zeros n)
      (by rw [hx]; omega) hD.lt
    rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt, hx]), List.append_nil] at e
    have hd₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := VG.Proof.AesCcm.X86_64.bytesAt_frame f₀₄w (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hD.w.sub_right (Lay.wSub (by decide))) (by have := hD.lt; omega)
    rw [hm₇, hm₆, hm₅, e, hc, hd₄]
    simp only [decide_eq_true_eq]
  · rw [hm₇, hm₆]
    exact (f₀₄w.sub fun r hr => ⟨r, by simp at hr ⊢; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩).trans
      (f₅.sub fun r hr => ⟨r, by simp at hr ⊢; simp [hr], fun _ h => h⟩)

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : VG.Proof.AesCcm.X86_64.Args s K W SP N A D R nl al n tl) (Tb : VG.Proof.AesCcm.X86_64.TagBuf W SP D n T tl) (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («open» v.callee v.suffix) s fun s' => gprPreserved s s' ∧
      match Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem D n)
          (bytesAt s.mem A al) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ :=
    VG.Proof.AesCcm.X86_64.entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, VG.Proof.AesCcm.X86_64.Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => VG.Proof.AesCcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.Ccm.ctxCiph s₁.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    VG.Proof.AesCcm.X86_64.ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.seq ?_
  -- `Ctr₀`.
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctrs_ok E₁ S₁ (Ar.nonce.of_eq rd₁ wr₁) Ar.h7 Ar.h13) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have f₂' : Frame (VG.Proof.AesCcm.X86_64.wR W SP) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesCcm.X86_64.wA W, by simp, Offset.sub_base W (by decide)⟩
  have S₂ := VG.Proof.AesCcm.X86_64.slots_mut L Ar.data.w (f₂'.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)) S₁
  -- Counter mode: the plaintext.
  have C₂ : VG.Proof.AesCcm.X86_64.CtrCtx K W SP s₂ R (bytesAt s.mem N nl) D n :=
    ⟨L, Ar.rounds, S₂.rounds, by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.h7, by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.h13,
      by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.hn, c₂, Ar.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁),
      by rw [wr₂, wr₁]; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctr_ok v C₂ E₂ S₂) fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  have f₁₃ : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s₁.mem s₃.mem := (f₂'.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)).trans (f₃.sub (VG.Proof.AesCcm.X86_64.ctrR_mut W SP D n))
  have S₃ := VG.Proof.AesCcm.X86_64.slots_mut L Ar.data.w f₁₃ S₁
  have c₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N nl) 0 := by
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm
      · exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c₂]
  have rd₁₃ : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  have wr₁₃ : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  -- The encrypted MAC of the plaintext at `W + 96`.
  refine VG.Proof.AesCcm.X86_64.macTag_ok v L E₃ S₃ Ar.rounds (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn c₃ (y := 96)
    (.inr rfl) (Ar.aad.of_eq rd₁₃ wr₁₃) (Ar.data.of_eq rd₁₃ wr₁₃) fun s₄ E₄ rd₄ wr₄ f₄ _ h₄ => ?_
  have f₁₄ : Frame (VG.Proof.AesCcm.X86_64.mutR W SP D n) s₁.mem s₄.mem :=
    f₁₃.trans ((f₄.sub (VG.Proof.AesCcm.X86_64.tagR_wR W SP (by decide))).sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n))
  have rd₁₄ : s₄.rd = s.rd := by rw [rd₄, rd₁₃]
  have wr₁₄ : s₄.wr = s.wr := by rw [wr₄, wr₁₃]
  have f₀₄ : Frame (VG.Proof.AesCcm.X86_64.entryR W :: VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem s₄.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₄.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have hT₄ : s₄.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by rw [VG.Proof.AesCcm.X86_64.argT_kept f₀₄ Ar.argsW Ar.argsD, hT]
  have hTr₄ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 24) 8 := by
    have h := VG.Proof.AesCcm.X86_64.in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [VG.Proof.AesCcm.X86_64.add_ofNat_assoc] at h
    rw [rd₁₄, wr₁₄]; exact h
  refine WP.mono (VG.Proof.AesCcm.X86_64.openTail_ok L E₄ (VG.Proof.AesCcm.X86_64.slots_mut L Ar.data.w f₁₄ S₁) (Ar.data.of_eq rd₁₄ wr₁₄)
    (by rw [wr₁₄]; exact Ar.dw) (by have := Ar.t4; omega) Ar.t16 (VG.Proof.AesCcm.X86_64.saved_mut L Ar.data.w f₁₄ sv₁) hT₄ hTr₄
    (by rw [rd₁₄, wr₁₄]; exact hTc) Tb.w)
    fun s₅ ⟨hg₅, hsp₅, hax₅, hd₅, f₅⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₅ (.rbx, 112) (by decide)
    · exact hg₅ (.rbp, 120) (by decide)
    · rw [hsp₅, hsp]
    · exact hg₅ (.r12, 128) (by decide)
    · exact hg₅ (.r13, 136) (by decide)
    · exact hg₅ (.r14, 144) (by decide)
    · exact hg₅ (.r15, 152) (by decide)
  · have fall : Frame (VG.Proof.AesCcm.X86_64.entryR W :: VG.Proof.AesCcm.X86_64.mutR W SP D n) s.mem s₅.mem :=
      f₀₄.trans (f₅.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨VG.Proof.AesCcm.X86_64.wK W, by simp, Offset.sub W (by decide) (by decide)⟩
        · exact ⟨VG.Proof.AesCcm.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩)
    rw [hsp]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (VG.Proof.AesCcm.X86_64.ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The plaintext and the comparison.
    have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m K R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
    have c₂' : Spec.Ccm.ctxCiph s₂.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [VG.Proof.AesCcm.X86_64.ciph_mut L Ar.dk Ar.rounds (f₂'.sub (VG.Proof.AesCcm.X86_64.wR_mut W SP D n)), hK₁]
    have c₃' : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [VG.Proof.AesCcm.X86_64.ciph_mut L Ar.dk Ar.rounds f₁₃, hK₁]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [VG.Proof.AesCcm.X86_64.buf_wR Ar.data f₂', hent Ar.data]
    have a₃ : bytesAt s₃.mem A al = bytesAt s.mem A al := by rw [VG.Proof.AesCcm.X86_64.buf_mut Ar.aad Ar.ad f₁₃, hent Ar.aad]
    have p₃ : bytesAt s₃.mem D n =
        Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n) := by
      rw [h₃, c₂', d₂, crypt_eq (hBC _)]
    have p₄ : bytesAt s₄.mem D n =
        Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n) := by
      rw [VG.Proof.AesCcm.X86_64.buf_wR Ar.data (f₄.sub (VG.Proof.AesCcm.X86_64.tagR_wR W SP (by decide))), p₃]
    have hT : bytesAt s₄.mem T tl = bytesAt s.mem T tl := VG.Proof.AesCcm.X86_64.tag_kept Tb Ar.t16 f₀₄
    rw [c₃', a₃, p₃] at h₄
    have hY := congrArg List.length h₄
    rw [VG.Proof.AesCcm.X86_64.length_bytesAt, length_xorFrom] at hY
    have hl : (bytesAt s.mem N nl).length ≤ 15 := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; have := Ar.h13; omega
    have hV : bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl =
        Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
          (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
            (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))) := by
      rw [VG.Proof.AesCcm.X86_64.bytesAt_prefix s₄.mem _ Ar.t16, h₄, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16, ← mac_eq _ _ hl]
    have hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))).length = tl := by
      rw [mac_eq _ _ hl, List.length_take, ← hY]; have := Ar.t16; omega
    have key : bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl = bytesAt s₄.mem T tl ↔
        Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem T tl) =
          Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
            (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n)) := by
      rw [hV, hT, cryptTag_eq_iff (hBC _) Ar.t16 _ hML (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _), eq_comm]
    simp only [Spec.Ccm.decryptWith]
    by_cases hk : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem T tl) =
        Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))
    · have hk' := key.mpr hk
      simp only [hk, ↓reduceIte]
      exact ⟨by rw [hax₅]; simp only [hk', ↓reduceIte]; rfl, by rw [hd₅]; simp only [hk', ↓reduceIte, p₄]⟩
    · have hk' : ¬ bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl = bytesAt s₄.mem T tl := fun e => hk (key.mp e)
      simp only [hk, ↓reduceIte]
      exact ⟨by rw [hax₅]; simp only [hk', ↓reduceIte]; rfl, by rw [hd₅]; simp only [hk', ↓reduceIte]⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp (v : Ctr32Impl) {s : State} (h : openX86_64.pre s) :
    WP isa («open» v.callee v.suffix) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' :=
  have A := VG.Proof.AesCcm.X86_64.args_of_open h
  VG.Proof.AesCcm.X86_64.open_wp' v A.1.1 A.1.2 A.2 rfl rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl rfl
    (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.OpenCT`. -/
section

/-!
# AES-CCM on x86-64: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`SealCT.lean`),
with counter mode before the MAC; the comparison, which leaves `ok` at
`W + 224`, and the mask and the exit are checked by the taint analysis from
the public arguments, between which correctness says each run keeps them
(`openCmp_ok`), and the received tag is read from the same address `tag`,
which correctness says is still on the stack (`loadTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem openLoad_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [])
    (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem openCmp_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [.rbx, .rsi])
    (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax]))) hc).isSome = true := ⟨_, by taint_decide⟩

theorem openMask_check : ∃ hc, (taint.check (VG.Proof.AesCcm.X86_64.ccmT [])
    (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ VG.Impl.AesCcm.X86_64.restore))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A run with the received tag `T`, of `tl` bytes, which it may read, apart
from `W`. -/
def TagR (W : Addr) (T : Addr) (tl : Nat) (s : State) : Prop :=
  Covers [⟨T, tl⟩] (s.rd ++ s.wr) ∧ (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩

/-- The tag length and the address of the received tag loaded, in a run. -/
theorem openLoad_one {K W SP : Addr} {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {s : State}
    (h : VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) s fun s' =>
      VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T ∧ s'.rd = s.rd := by
  obtain ⟨o, -, -, -, hT⟩ := h
  obtain ⟨s₁, run₁, hm₁, hbx₁, hsi₁, hg₁, hrd₁, hwr₁⟩ := VG.Proof.AesCcm.X86_64.loadTag_ok o.env o.sl hT.val hT.rd
  refine WP.of_runBlock ⟨s₁, run₁, ⟨o.env.keep (fun r hr => hg₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    hrd₁ hwr₁, by rw [hm₁]; exact o.sl, hwr₁.trans o.wr⟩, hbx₁, hsi₁, hrd₁⟩

/-- The comparison keeps the public arguments. -/
theorem openCmp_one {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) {s : State} (h : VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s) (hT : VG.Proof.AesCcm.X86_64.TagR W T tl s) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv
      (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax])))) s (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl) := by
  obtain ⟨o, -, -, hD, hA⟩ := h
  refine WP.mono (VG.Proof.AesCcm.X86_64.openCmp_ok L o.env o.sl (by omega) ht16 hA.val hA.rd hT.1 hT.2) fun s₄ ⟨E₄, _, wr₄, f₄, _⟩ => ?_
  refine ⟨E₄, VG.Proof.AesCcm.X86_64.slots_mut L hD.w (f₄.sub fun r hr => ?_) o.sl, wr₄.trans o.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨VG.Proof.AesCcm.X86_64.wK W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨VG.Proof.AesCcm.X86_64.wC W, by simp, Offset.sub W (by decide) (by decide)⟩

/-- `open` after its entry, up to the comparison, in one run. -/
theorem openFront_mid (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {s : State} (h : VG.Proof.AesCcm.X86_64.Pre₀ K W SP R N A D nl al n tl T s) :
    WP isa (openFront v.callee v.suffix) s fun s' => VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨o, hN, hA, hD, hT⟩ := h
  obtain ⟨t, s', e, q⟩ := WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctrs_mid L o hN hA hD hT h7 h13) fun _ h₁ =>
    WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.ctr_mid v L hR h7 h13 hn' hdk h₁) fun _ h₂ =>
    WP.seq (WP.mono (VG.Proof.AesCcm.X86_64.mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inr rfl) h₂) fun _ h₃ =>
    VG.Proof.AesCcm.X86_64.tag_mid v L hR h7 h13 (.inr rfl) h₃)))
  exact ⟨t, s', e, q, Exec.rdwr e⟩

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : Ctr32Impl) {K W SP : Addr} (L : VG.Proof.AesCcm.X86_64.Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 64) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → (VG.Proof.AesCcm.X86_64.Pre₀ K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.TagR W T tl s₁) ∧
      (VG.Proof.AesCcm.X86_64.Pre₀ K W SP R N A D nl al n tl T s₂ ∧ VG.Proof.AesCcm.X86_64.TagR W T tl s₂)) :
    RelCT isa P (.seq (openFront v.callee v.suffix)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 okO) .rax]) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ VG.Impl.AesCcm.X86_64.restore)))))))) fun _ _ => True := by
  have hy : uO = 0 ∨ uO = 96 := .inr rfl
  have r₁ := (VG.Proof.AesCcm.X86_64.rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨⟨o₁, -⟩, -⟩, ⟨⟨o₂, -⟩, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) VG.Proof.AesCcm.X86_64.ctrs_check).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) fun s₁ s₂ h => by
      obtain ⟨⟨⟨o₁, n₁, a₁, d₁, t₁⟩, -⟩, ⟨⟨o₂, n₂, a₂, d₂, t₂⟩, -⟩⟩ := hP _ _ h
      exact ⟨VG.Proof.AesCcm.X86_64.ctrs_mid L o₁ n₁ a₁ d₁ t₁ h7 h13, VG.Proof.AesCcm.X86_64.ctrs_mid L o₂ n₂ a₂ d₂ t₂ h7 h13⟩
  have r₂ := (VG.Proof.AesCcm.X86_64.rel_of_pt (c := ctr v.callee)
    (P := fun s₁ s₂ => True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact VG.Proof.AesCcm.X86_64.crypt_rel v C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.ctr_mid v L hR h7 h13 hn' hdk h.2.1, VG.Proof.AesCcm.X86_64.ctr_mid v L hR h7 h13 hn' hdk h.2.2⟩
  have r₃ := (VG.Proof.AesCcm.X86_64.mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' hy
    (Q := fun s₁ s₂ => True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1⟩,
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.1, VG.Proof.AesCcm.X86_64.mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.2⟩
  have r₄ := (VG.Proof.AesCcm.X86_64.tag_rel v L hR hDW hn h7 h13 hy
    (Q := fun s₁ s₂ => True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T) (F₂ := VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.tag_mid v L hR h7 h13 hy h.2.1, VG.Proof.AesCcm.X86_64.tag_mid v L hR h7 h13 hy h.2.2⟩
  -- The pieces before the comparison keep the permissions, so the received tag stays readable.
  have front := (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))).wp
    (F₁ := VG.Proof.AesCcm.X86_64.TagR W T tl) (F₂ := VG.Proof.AesCcm.X86_64.TagR W T tl) fun s₁ s₂ h => by
      obtain ⟨⟨p₁, tr₁⟩, ⟨p₂, tr₂⟩⟩ := hP _ _ h
      exact ⟨WP.mono (VG.Proof.AesCcm.X86_64.openFront_mid v L hR h7 h13 ht4 ht16 hte hn' hdk p₁) fun _ ⟨_, rd', wr'⟩ =>
          ⟨by rw [rd', wr']; exact tr₁.1, tr₁.2⟩,
        WP.mono (VG.Proof.AesCcm.X86_64.openFront_mid v L hR h7 h13 ht4 ht16 hte hn' hdk p₂) fun _ ⟨_, rd', wr'⟩ =>
          ⟨by rw [rd', wr']; exact tr₂.1, tr₂.2⟩⟩
  have r₅a := (VG.Proof.AesCcm.X86_64.rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => (True ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₁ ∧ VG.Proof.AesCcm.X86_64.Mid K W SP R N A D nl al n tl T s₂) ∧
      VG.Proof.AesCcm.X86_64.TagR W T tl s₁ ∧ VG.Proof.AesCcm.X86_64.TagR W T tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.1.2.1.1 h.1.2.2.1 fun _ h => nomatch h) VG.Proof.AesCcm.X86_64.openLoad_check).wp
    (F₁ := fun (s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T)
    (F₂ := fun (s' : State) => VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T)
    fun _ _ h => ⟨WP.mono (VG.Proof.AesCcm.X86_64.openLoad_one h.1.2.1) fun _ q => ⟨q.1, q.2.1, q.2.2.1⟩,
      WP.mono (VG.Proof.AesCcm.X86_64.openLoad_one h.1.2.2) fun _ q => ⟨q.1, q.2.1, q.2.2.1⟩⟩
  have r₅b := VG.Proof.AesCcm.X86_64.rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax])))
    (P := fun s₁ s₂ => True ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 tl ∧ s₁.gpr .rsi = T) ∧
      (VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 tl ∧ s₂.gpr .rsi = T)) [.rbx, .rsi] hDW hn
    (fun _ _ h => Both.of h.2.1.1 h.2.2.1 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]) VG.Proof.AesCcm.X86_64.openCmp_check
  have r₅ := (RelCT.seq r₅a r₅b).wp
    (F₁ := VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl) (F₂ := VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl)
    fun _ _ h => ⟨VG.Proof.AesCcm.X86_64.openCmp_one L ht4 ht16 h.1.2.1 h.2.1, VG.Proof.AesCcm.X86_64.openCmp_one L ht4 ht16 h.1.2.2 h.2.2⟩
  have r₆ := VG.Proof.AesCcm.X86_64.rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => True ∧ VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₁ ∧ VG.Proof.AesCcm.X86_64.One K W SP R N A D nl al n tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.2.1 h.2.2 fun _ h => nomatch h) VG.Proof.AesCcm.X86_64.openMask_check
  exact RelCT.seq front (VG.Proof.AesCcm.X86_64.rel_assoc4 (RelCT.seq r₅ r₆))

/-- What the entry of `open` leaves: a run after the entry, with the received
tag readable. -/
theorem entry_open {s : State} (hp : openX86_64.pre s) :
    WP isa (.block VG.Impl.AesCcm.X86_64.entry) s fun s₁ =>
      VG.Proof.AesCcm.X86_64.Pre₀ (s.gpr .rdi) (VG.Proof.AesCcm.arg s 4) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .r8) (VG.Proof.AesCcm.arg s 0)
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (VG.Proof.AesCcm.arg s 1).toNat (VG.Proof.AesCcm.arg s 3).toNat (VG.Proof.AesCcm.arg s 2) s₁ ∧
      VG.Proof.AesCcm.X86_64.TagR (VG.Proof.AesCcm.arg s 4) (VG.Proof.AesCcm.arg s 2) (VG.Proof.AesCcm.arg s 3).toNat s₁ := by
  have A := VG.Proof.AesCcm.X86_64.args_of_open hp
  refine WP.mono (VG.Proof.AesCcm.X86_64.entry_post A.1.1 rfl rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl rfl
    (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesCcm.X86_64.ofNat_toNat64 _).symm) fun _ ⟨E, S, rd, wr, hT⟩ =>
    ⟨⟨⟨E, S, by rw [wr]; exact hp.2.1⟩, A.1.1.nonce.of_eq rd wr, A.1.1.aad.of_eq rd wr, A.1.1.data.of_eq rd wr, hT⟩,
      by rw [rd, wr]; exact A.2, A.1.2.w⟩

/-- The second run, with the first's public arguments. -/
theorem entry_open_pub {s₀ s₀' : State} (hp' : openX86_64.pre s₀') (hq : VG.Proof.AesCcm.onePub s₀ s₀') :
    WP isa (.block VG.Impl.AesCcm.X86_64.entry) s₀' fun s₁ =>
      VG.Proof.AesCcm.X86_64.Pre₀ (s₀.gpr .rdi) (VG.Proof.AesCcm.arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (VG.Proof.AesCcm.arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (VG.Proof.AesCcm.arg s₀ 1).toNat (VG.Proof.AesCcm.arg s₀ 3).toNat (VG.Proof.AesCcm.arg s₀ 2) s₁ ∧
      VG.Proof.AesCcm.X86_64.TagR (VG.Proof.AesCcm.arg s₀ 4) (VG.Proof.AesCcm.arg s₀ 2) (VG.Proof.AesCcm.arg s₀ 3).toNat s₁ := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), qa 3 (by decide), qa 4 (by decide), q1, q2, q3, q4,
    q5, q6, q7]
  exact VG.Proof.AesCcm.X86_64.entry_open hp'

/-- `vg_aes_ccm_open`, in two runs with the same public arguments. -/
theorem open_rel (v : Ctr32Impl) {s₀ s₀' : State} (hp : openX86_64.pre s₀) (hp' : openX86_64.pre s₀')
    (hq : VG.Proof.AesCcm.onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee v.suffix) fun _ _ => True := by
  have A := VG.Proof.AesCcm.X86_64.args_of_open hp
  have Ar := A.1.1
  refine RelCT.seq (VG.Proof.AesCcm.X86_64.entry_rel (VG.Proof.AesCcm.X86_64.pub_regs hq) (hq.2.2.2.2.2.2.2 4 (by decide)) (VG.Proof.AesCcm.X86_64.argW_in Ar rfl)
    (VG.Proof.AesCcm.X86_64.argW_in (VG.Proof.AesCcm.X86_64.args_of_open hp').1.1 rfl) (VG.Proof.AesCcm.X86_64.entry_open hp) (VG.Proof.AesCcm.X86_64.entry_open_pub hp' hq)) ?_
  exact VG.Proof.AesCcm.X86_64.openBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.aad.lt Ar.hn Ar.dk fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Verified`. -/
section

/-!
# AES-CCM on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), states satisfying the preconditions, and the shared
contracts of `Spec/Ccm/Contract.lean` with the working space as a last
argument (`Proof/AesCcm/Scratch.lean`), with 16 bytes of stack: the return
addresses of the call of `vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of
its call of `vg_aes_ctr32`. `Frame.lean` allocates the working space.
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (update_mx update_spSafe)

theorem seal_mx (v : Ctr32Impl) : («seal» v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.allInstrs, update_mx v, v.mxcsr]
  decide +kernel

theorem open_mx (v : Ctr32Impl) : («open» v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.allInstrs, update_mx v, v.mxcsr]
  decide +kernel

theorem seal_spSafe (v : Ctr32Impl) : («seal» v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.all, update_spSafe v, v.spSafe]
  decide +kernel

theorem open_spSafe (v : Ctr32Impl) : («open» v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.all, update_spSafe v, v.spSafe]
  decide +kernel

theorem seal_correct (v : Ctr32Impl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesCcm.X86_64.seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesCcm.X86_64.seal_mx v) he hg, hp⟩

theorem open_correct (v : Ctr32Impl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesCcm.X86_64.open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesCcm.X86_64.open_mx v) he hg, hp⟩

theorem open_ct (v : Ctr32Impl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesCcm.X86_64.open_rel v h₁ h₂ hq.1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 7 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8020 then 4 else if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

theorem seal_verified (v : Ctr32Impl) :
    Verified X86_64.target («seal» v.callee v.suffix) (Proof.AesCcm.sealScratchContract X86_64.abi 16) :=
  Verified.of_correct (VG.Proof.AesCcm.X86_64.seal_correct v) (VG.Proof.AesCcm.X86_64.seal_ct v) (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
      Spec.Ccm.sealPost, Proof.AesCcm.sealX86_64, Proof.AesCcm.sealPre, Proof.AesCcm.oneLay, Proof.AesCcm.onePub,
      X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args, Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using VG.Proof.AesCcm.X86_64.sealSat)

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { VG.Proof.AesCcm.X86_64.sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : Ctr32Impl) :
    Verified X86_64.target («open» v.callee v.suffix) (Proof.AesCcm.openScratchContract X86_64.abi 16) :=
  Verified.of_correct (VG.Proof.AesCcm.X86_64.open_correct v) (VG.Proof.AesCcm.X86_64.open_ct v)
    { pre := by sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_simp [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [openSat, sealSat] using VG.Proof.AesCcm.X86_64.openSat }

end VG.Proof.AesCcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesCcm.X86_64.Frame`. -/
section

/-!
# AES-CCM on x86-64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is passed on the stack
after the six argument registers and four other stack arguments (`data`,
`len`, `tag` and `tag_len`), so the frame of 2608 bytes holds the 2560 bytes
of working space, a copy of those four arguments, the word that stands for
the return address and the address of the working space. The code's own
calls use 16 bytes below it: the return addresses of the call of
`vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of its call of
`vg_aes_ctr32`, which uses no stack (`Ctr32Impl.noStack`). `open`'s leak,
whether it succeeds, reads only its buffers (`openLeak_local`).
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem seal_xdepth : («seal» v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate,
    callCtr, Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.x86_64Depth, v.noStack]
  decide +kernel

theorem open_xdepth : («open» v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.x86_64Depth, v.noStack]
  decide +kernel

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { VG.Proof.AesCcm.X86_64.sealSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract X86_64.abi 2624).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using VG.Proof.AesCcm.X86_64.sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» v.callee v.suffix))
      (Spec.Ccm.sealContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre X86_64.abi.ptrBits)
    (post := Spec.Ccm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2608) (VG.Proof.AesCcm.X86_64.seal_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesCcm.X86_64.seal_spSafe v) (VG.Proof.AesCcm.X86_64.seal_xdepth v) (sealPre_local _) (sealPost_local _) VG.Proof.AesCcm.X86_64.sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { VG.Proof.AesCcm.X86_64.openSat with
                 rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract X86_64.abi 2624).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat, sealSat] using VG.Proof.AesCcm.X86_64.openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callee v.suffix))
      (Spec.Ccm.openContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre X86_64.abi.ptrBits)
    (post := Spec.Ccm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) (VG.Proof.AesCcm.X86_64.open_verified v)
    (by decide) (by decide) (by decide) (VG.Proof.AesCcm.X86_64.open_spSafe v) (VG.Proof.AesCcm.X86_64.open_xdepth v) (openPre_local _)
    (openPost_local _) VG.Proof.AesCcm.X86_64.openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesCcm.X86_64

end
