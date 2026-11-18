module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Env
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Spec.GcmSiv
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `AesGcmSiv.X86_64.Reg.Env`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV in registers on x86-64: the contracts and where everything is

`Proof/AesGcmSiv/X86_64/Env.lean`'s contracts, regions, permissions, buffers
and slots for the working space of `Impl/AesGcmSiv/X86_64Reg.lean`: 744
bytes, which end with the encryption key's schedule.

Untrusted: everything here is checked by Lean. The shared contracts of
`Spec/GcmSiv/Contract.lean`, with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`), imply these (`Verified.lean`). `seal` and `open` call `vg_aes_ctr32`,
`vg_aes_expand_key` and `vg_ghash`, which make no calls: the return address
is in the 8 bytes below the stack pointer (`stk8`), which no buffer
overlaps, nor the return address (`ret`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSivReg

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk8 (s : State) : Region := below (s.gpr .rsp) 8

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop := (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 14

/-- What `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` both need, but for
the permissions: `(schedule = rdi, rounds = rsi, nonce = rdx, aad = rcx,
aad_len = r8, data = r9, len = [rsp + 8], tag = [rsp + 16],
work = [rsp + 24])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 744⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 3) ∧ work.Disjoint (args s 3) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk8 s).Disjoint sch ∧ (stk8 s).Disjoint nonce ∧ (stk8 s).Disjoint aad ∧ (stk8 s).Disjoint data ∧
    (stk8 s).Disjoint tag ∧ (stk8 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧
    (arg s 1).toNat + 16 ≤ 2 ^ 64 ∧ (arg s 2).toNat + 744 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ rounds s

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 744⟩
  s.rd = [sch, nonce, aad, args s 3] ∧ s.wr = [data, tag, work] ∧ oneLay s ∧ (ret s).Disjoint tag

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 744⟩
  s.rd = [sch, nonce, aad, tag, args s 3] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealX86_64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (keyLen (s.gpr .rsi).toNat)
        (bytesAt s.mem (s.gpr .rdx) 12) (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
        (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat, bytesAt s'.mem (arg s 1) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (keyLen (s.gpr .rsi).toNat)
    (bytesAt s.mem (s.gpr .rdx) 12) (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
    (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (arg s 1) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `rax` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : (s'.gpr .rax).setWidth 32 = 1) (hd : bytesAt s'.mem D n = pt) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : (s'.gpr .rax).setWidth 32 = 0) (hd : bytesAt s'.mem D n = zeros n) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- What `vg_aes_gcm_siv_open` may leak (`Spec.GcmSiv.openLeak`): whether it
succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds s then [] else [if (openResult s).isSome then 1 else 0]

/-- `vg_aes_gcm_siv_open`. -/
def openX86_64 : Contract isa where
  pre := openPre
  post s s' := openPost (openResult s) s' (s.gpr .r9) (arg s 0).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesGcmSivReg

/-!
## Where everything is

Untrusted: everything here is checked by Lean. The key schedule of the
key-generating key (240 bytes at `K`), the working space (744 bytes at
`W`) and the 8 bytes of stack below `SP` that the calls use (`Lay`); what a
state may access (`Perm`); the registers holding `K` and `W` and the stack
pointer (`Env`); and the public values the entry keeps in `W` (`Slots`).
The pieces write the parts of `W` in `mutR` (and the data, and the stack
below `SP`), so the slots and our caller's registers saved in `W` stay as
the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (covers_off in_off in_left covers_left)

/-! ## The regions -/

/-- The key schedule, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : Addr) : Prop where
  kw : K.toNat + 240 ≤ 2 ^ 64
  ww : W.toNat + 744 ≤ 2 ^ 64
  k_w : (⟨K, 240⟩ : Region).Disjoint ⟨W, 744⟩
  stk_k : (below SP 8).Disjoint ⟨K, 240⟩
  stk_w : (below SP 8).Disjoint ⟨W, 744⟩
  sp : 8 ≤ SP.toNat

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 744⟩] s.wr

/-- The registers holding the key schedule, `W` and the stack pointer, and
what the state may access. -/
structure Env (K W SP : Addr) (s : State) : Prop where
  r13 : s.gpr .r13 = K
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : Perm K W s

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r13`, `r15`, `rsp` and the permissions. -/
theorem Env.keep {K W SP : Addr} {s s' : State} (h : Env K W SP s)
    (hg : ∀ r ∈ [Reg.r13, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Env K W SP s' :=
  ⟨by rw [hg _ (by simp), h.r13], by rw [hg _ (by simp), h.r15], by rw [hg _ (by simp), h.rsp],
    h.perm.of_eq hrd hwr⟩

theorem Env.of_saved {K W SP : Addr} {s s' : State} (h : Env K W SP s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env K W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 744) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 744⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} (L : Lay K W SP)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 744) (hd : d + k ≤ 744) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha]) (by have := L.ww; omega_using [hd])

theorem k_w' {d k : Nat} (hd : d + k ≤ 744) : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 744) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : Perm K W s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 744) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 744) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 744) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 744) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`, the
key schedule and the stack below `SP`. -/
structure Buf (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

namespace Buf

variable {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : Buf K W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf K W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : Buf K W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega_using [hk]) h.lt
  lt := by have := h.lt; omega_using [this]
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega_using [hk, this])]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega_arith
  w := h.w.sub_left (Offset.sub_base D (by omega_using [hk]))
  stk := h.stk.sub_right (Offset.sub_base D (by omega_using [hk]))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf K W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hk, hc]⟩
  lt := by have := h.lt; omega_using [hk, this]
  wrap := by have := h.wrap; omega_using [hk, this]
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : Buf K W SP s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega_using [hk])).take (by omega_using [hk])

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the rounds, the nonce, the
additional data and its length, and the data and its length. -/
structure Slots (W : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (m : Mem) : Prop where
  rounds : m.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 R
  nonce : m.readW (W + BitVec.ofNat 64 208) 64 = N
  aad : m.readW (W + BitVec.ofNat 64 216) 64 = A
  alen : m.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  data : m.readW (W + BitVec.ofNat 64 232) 64 = D
  len : m.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n

/-- The slots, after code that writes only parts of `W` apart from them, the
stack below `SP` and a buffer apart from `W`. -/
theorem Slots.of_frame {W : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {m m' : Mem}
    {rs : List Region} (S : Slots W R N A D al n m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) : Slots W R N A D al n m' := by
  have k (d : Nat) (hd' : 200 ≤ d ∧ d + 8 ≤ 248) :
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    hf.readW (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by omega_arith) (by omega_arith))) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

/-- The parts of `W` the pieces write: the blocks at `[0, 144)`, `ok` at
`[192, 200)` and `[248, 744)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 144⟩
abbrev wO (W : Addr) : Region := ⟨W + BitVec.ofNat 64 192, 8⟩
abbrev wC (W : Addr) : Region := ⟨W + BitVec.ofNat 64 248, 496⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : Addr) (n : Nat) : List Region := [wA W, wO W, wC W, below SP 8, ⟨D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩)
    {d k : Nat} (hd : 144 ≤ d ∧ d + k ≤ 192 ∨ 200 ≤ d ∧ d + k ≤ 248) :
    ∀ r ∈ mutR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 144) (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
    · exact L.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact (L.stk_w' (by omega_using [hd])).symm
  · exact (hD.sub_right (Lay.wSub (by omega_using [hd]))).symm

end VG.Proof.AesGcmSivReg.X86_64

end

end

/-!
# AES-GCM-SIV on x86-64: the entry, the exit and the arguments

Untrusted: everything here is checked by Lean. `entry` reads the stack
arguments, saves our caller's registers at `W + 144` and keeps the arguments
but `tag` in `W` (`entry_ok`); `restore` reads the registers back (`restore_ok`).
-/

-- separate module: the entry, the exit and the arguments, apart from the pieces

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_off)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc readW_writeW_W)
open VG.Spec.Aes (bytesAt)

/-- Our caller's registers, saved at `W + 144`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The public values `seal` and `open` leave in `W`: our caller's
registers, as on entry (`g`), and the slots. -/
structure KeptW (W : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (g : Reg → BitVec 64) (m : Mem) : Prop where
  saved : Saved m W g
  slots : Slots W R N A D al n m

/-- The save area and the slots, which `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 144, 104⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {s : State} (P : Perm K W s) {R : Nat} {N A D : Addr} {al n : Nat}
    (hsp : s.gpr .rsp = SP) (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 24⟩] (s.rd ++ s.wr))
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧
      Saved s₁.mem W s.gpr ∧ Frame [entryR W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₂₄ := in_off (d := 16) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₂₄
  simp only [Nat.reduceAdd] at a₂₄
  have w₁ := P.wW (show 144 + 8 ≤ 744 by decide)
  have w₂ := P.wW (show 152 + 8 ≤ 744 by decide)
  have w₃ := P.wW (show 160 + 8 ≤ 744 by decide)
  have w₄ := P.wW (show 168 + 8 ≤ 744 by decide)
  have w₅ := P.wW (show 176 + 8 ≤ 744 by decide)
  have w₆ := P.wW (show 184 + 8 ≤ 744 by decide)
  have w₇ := P.wW (show 200 + 8 ≤ 744 by decide)
  have w₈ := P.wW (show 208 + 8 ≤ 744 by decide)
  have w₉ := P.wW (show 216 + 8 ≤ 744 by decide)
  have w₁₀ := P.wW (show 224 + 8 ≤ 744 by decide)
  have w₁₁ := P.wW (show 232 + 8 ≤ 744 by decide)
  have w₁₂ := P.wW (show 240 + 8 ≤ 744 by decide)
  have cE : ∀ d, 144 ≤ d → d + 8 ≤ 248 → (entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains W h₁ (by omega_using [h₂]) (by decide)
  refine ⟨_, by srun [entry, save, saved, List.map_cons, List.map_nil, hW, hsp, hn, a₈, a₂₄, w₁, w₂, w₃, w₄,
      w₅, w₆, w₇, w₈, w₉, w₁₀, w₁₁, w₁₂], ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
  · exact P.of_eq rfl rfl
  iterate 6
    · simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
        ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9, hn]
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64]
  · simp only [mem_setReg]
    repeat (first | exact Frame.refl _ _ |
      refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
  all_goals rfl

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {g : Reg → BitVec 64} (hs : Saved s.mem W g) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 144 + 8 ≤ 744 by decide)
  have r₂ := E.perm.wR (show 152 + 8 ≤ 744 by decide)
  have r₃ := E.perm.wR (show 160 + 8 ≤ 744 by decide)
  have r₄ := E.perm.wR (show 168 + 8 ≤ 744 by decide)
  have r₅ := E.perm.wR (show 176 + 8 ≤ 744 by decide)
  have r₆ := E.perm.wR (show 184 + 8 ≤ 744 by decide)
  have v₁ := hs (.rbx, 144) (by decide)
  have v₂ := hs (.rbp, 152) (by decide)
  have v₃ := hs (.r12, 160) (by decide)
  have v₄ := hs (.r13, 168) (by decide)
  have v₅ := hs (.r14, 176) (by decide)
  have v₆ := hs (.r15, 184) (by decide)
  refine ⟨_, by srun [restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesGcmSivReg.X86_64

/-!
## The arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`TagBuf`, `args_of_seal`, `args_of_open`). Between `entry` and `restore`, the
pieces only write the parts of `W` below 144, from 192 to 200 and from 248
on, the stack below `SP` and the data (`mutR`), so they keep the slots, the
saved registers, the key schedule, the nonce, the additional data and the
tag's address on the stack (`argT_kept`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64
open VG.Impl.AesGcmSiv.X86_64 (saved)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (covers_left covers_of_mem bytesAt_frame)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (12 bytes at `N`), the additional data (`al` bytes at
`A`), the data (`n` bytes at `D`), the working space at `W` and the stack
pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R al n : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 14
  nonce : Buf K W SP s N 12
  aad : Buf K W SP s A al
  data : Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩
  nd : (⟨N, 12⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 744⟩
  argsD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- The tag, the 16 bytes at `T`: apart from the data, `W` and the stack
below `SP`. -/
structure TagBuf (W SP D : Addr) (n : Nat) (T : Addr) : Prop where
  d : (⟨T, 16⟩ : Region).Disjoint ⟨D, n⟩
  w : (⟨T, 16⟩ : Region).Disjoint ⟨W, 744⟩
  stk : (below SP 8).Disjoint ⟨T, 16⟩
  wrap : T.toNat + 16 ≤ 2 ^ 64

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .rdi, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .rdx, 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s 3] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .r9, (arg s 0).toNat⟩] s.wr) (hW : Covers [⟨arg s 2, 744⟩] s.wr) :
    Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (arg s 0).toNat ∧
      TagBuf (arg s 2) (s.gpr .rsp) (s.gpr .r9) (arg s 0).toNat (arg s 1) := by
  sig_split h
  rename_i d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 b20 b21 b22 b23 b24 b25 b26 _
  have hR := h
  clear h
  exact ⟨{
    lay := ⟨b20, b25, d2, d14, d19, b26⟩
    perm := ⟨hk, hW⟩
    rounds := hR
    nonce := ⟨hN, by decide, b21, d4, d15⟩
    aad := ⟨hA, BitVec.isLt _, b22, d6, d16⟩
    data := ⟨covers_left hD, BitVec.isLt _, b23, d9, d17⟩
    dw := hD
    dk := d1
    nd := d3
    ad := d5
    retW := d13
    retD := d12
    args := ha
    argsW := d11.symm
    argsD := d10.symm }, ⟨d7, d8, d18, b24⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    (Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (arg s 0).toNat ∧
      TagBuf (arg s 2) (s.gpr .rsp) (s.gpr .r9) (arg s 0).toNat (arg s 1)) ∧
      Covers [⟨arg s 1, 16⟩] s.wr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨arg s 1, 16⟩ := by
  obtain ⟨hrd, hwr, hl, hrt⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, 12⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
      args s 3], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (arg s 0).toNat⟩ : Region), ⟨arg s 1, 16⟩, ⟨arg s 2, 744⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mwr _ (by simp), hrt⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    (Args s (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9) (s.gpr .rsi).toNat
        (s.gpr .r8).toNat (arg s 0).toNat ∧
      TagBuf (arg s 2) (s.gpr .rsp) (s.gpr .r9) (arg s 0).toNat (arg s 1)) ∧
      Covers [⟨arg s 1, 16⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, 12⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
      ⟨arg s 1, 16⟩, args s 3], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .r9, (arg s 0).toNat⟩ : Region), ⟨arg s 2, 744⟩], Covers [r] s.wr := fun r hr =>
    covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mrd _ (by simp)⟩

/-- The tag as a buffer to read. -/
theorem TagBuf.buf {K W SP D T : Addr} {n : Nat} {s : State} (h : TagBuf W SP D n T)
    (hr : Covers [⟨T, 16⟩] (s.rd ++ s.wr)) : Buf K W SP s T 16 :=
  ⟨hr, by decide, h.wrap, h.w, h.stk⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega_using [hR])]

section
variable {K W SP N A D : Addr} {R al n : Nat} {m m' : Mem}

/-- The tag's address, at `SP + 16`, misses what the entry and the pieces
write. -/
theorem argT_disj (hW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 744⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 16, 8⟩ ⟨SP + BitVec.ofNat 64 8, 24⟩ := by
    rw [show SP + BitVec.ofNat 64 16 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
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

/-- The tag's address, at `SP + 16`, through the entry and the pieces. -/
theorem argT_kept (hf : Frame (entryR W :: mutR W SP D n) m m')
    (hW : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 744⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩) :
    m'.readW (SP + BitVec.ofNat 64 16) 64 = m.readW (SP + BitVec.ofNat 64 16) 64 :=
  hf.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (argT_disj hW hD) (by decide)

/-- The tag, through the entry and the pieces. -/
theorem tag_kept {T : Addr} (hT : TagBuf W SP D n T) (hf : Frame (entryR W :: mutR W SP D n) m m') :
    bytesAt m' T 16 = bytesAt m T 16 :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Region.sub_prefix (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.stk.symm
    · exact hT.d) (by decide)

theorem slots_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩)
    (hf : Frame (mutR W SP D n) m m') (S : Slots W R N A D al n m) : Slots W R N A D al n m' := by
  have k : ∀ d, (144 ≤ d ∧ d + 8 ≤ 192 ∨ 200 ≤ d ∧ d + 8 ≤ 248) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD hd) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : Saved m W g) : Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD (.inl hd))
    (by decide)

end

end VG.Proof.AesGcmSivReg.X86_64

/-!
## The arguments of the functions called

Untrusted: everything here is checked by Lean. The calls are those of
AES-GCM (`Proof.AesGcm.X86_64.ctr_call`, `gh_call`, `key_call`); `cargs`,
`gargs` and `kargs` build their arguments from the environment: the key
schedule of the key-generating key or of the encryption key at
`W + 248` (`keyS`), blocks of `W` as counter blocks, states and data, the
data itself, and the working spaces at `W + 1512` and `W + 1768`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

theorem toNat_W {W : Addr} (hw : W.toNat + 744 ≤ 2 ^ 64) {d : Nat} (hd : d < 744) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hw, hd])]

end VG.Proof.AesGcmSivReg.X86_64
