import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesGcmSiv.X86_64
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-GCM-SIV on x86-64: the contracts, where everything is and running blocks

Untrusted: everything here is checked by Lean. The shared contracts of
`Spec/GcmSiv/Contract.lean`, with the working space as a last argument
(`Proof/AesGcmSiv/Scratch.lean`), imply these (`Verified.lean`). `seal` and `open` call `vg_aes_ctr32`,
`vg_aes_expand_key` and `vg_ghash`, which make no calls: the return address
is in the 8 bytes below the stack pointer (`stk8`), which no buffer
overlaps, nor the return address (`ret`).
-/

namespace VG.Proof.AesGcmSiv

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
  let work : Region := ⟨arg s 2, 3816⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 3) ∧ work.Disjoint (args s 3) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk8 s).Disjoint sch ∧ (stk8 s).Disjoint nonce ∧ (stk8 s).Disjoint aad ∧ (stk8 s).Disjoint data ∧
    (stk8 s).Disjoint tag ∧ (stk8 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧
    (arg s 1).toNat + 16 ≤ 2 ^ 64 ∧ (arg s 2).toNat + 3816 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ rounds s

/-- What `vg_aes_gcm_siv_seal` needs: `oneLay`, with `tag` the 16 bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 3816⟩
  s.rd = [sch, nonce, aad, args s 3] ∧ s.wr = [data, tag, work] ∧ oneLay s ∧ (ret s).Disjoint tag

/-- What `vg_aes_gcm_siv_open` needs: `oneLay`, with the received tag the 16
bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .rdi, 240⟩
  let nonce : Region := ⟨s.gpr .rdx, 12⟩
  let aad : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let tag : Region := ⟨arg s 1, 16⟩
  let work : Region := ⟨arg s 2, 3816⟩
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

end VG.Proof.AesGcmSiv

/-!
## Where everything is

Untrusted: everything here is checked by Lean. The key schedule of the
key-generating key (240 bytes at `K`), the working space (3816 bytes at
`W`) and the 8 bytes of stack below `SP` that the calls use (`Lay`); what a
state may access (`Perm`); the registers holding `K` and `W` and the stack
pointer (`Env`); and the public values the entry keeps in `W` (`Slots`).
The pieces write the parts of `W` in `mutR` (and the data, and the stack
below `SP`), so the slots and our caller's registers saved in `W` stay as
the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (covers_off in_off in_left covers_left)

/-! ## The regions -/

/-- The key schedule, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : Addr) : Prop where
  kw : K.toNat + 240 ≤ 2 ^ 64
  ww : W.toNat + 3816 ≤ 2 ^ 64
  k_w : (⟨K, 240⟩ : Region).Disjoint ⟨W, 3816⟩
  stk_k : (below SP 8).Disjoint ⟨K, 240⟩
  stk_w : (below SP 8).Disjoint ⟨W, 3816⟩
  sp : 8 ≤ SP.toNat

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 3816⟩] s.wr

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

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 240) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 240⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3816) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3816⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} (L : Lay K W SP)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3816) (hd : d + k ≤ 3816) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 3816) : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 3816) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 3816) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 3816) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 3816) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 3816) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`, the
key schedule and the stack below `SP`. -/
structure Buf (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

namespace Buf

variable {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : Buf K W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf K W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : Buf K W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base D (by omega))
  stk := h.stk.sub_right (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf K W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : Buf K W SP s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

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

/-- The parts of `W` the pieces write: the blocks at `[0, 144)`, `ok` at
`[192, 200)` and `[248, 3816)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 144⟩
abbrev wO (W : Addr) : Region := ⟨W + BitVec.ofNat 64 192, 8⟩
abbrev wC (W : Addr) : Region := ⟨W + BitVec.ofNat 64 248, 3568⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : Addr) (n : Nat) : List Region := [wA W, wO W, wC W, below SP 8, ⟨D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    {d k : Nat} (hd : 144 ≤ d ∧ d + k ≤ 192 ∨ 200 ≤ d ∧ d + k ≤ 248) :
    ∀ r ∈ mutR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 144) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

end VG.Proof.AesGcmSiv.X86_64

/-!
## Running blocks

Untrusted: everything here is checked by Lean. `srun [facts]` runs a block
of the instructions the AES-GCM-SIV code uses from a state in which the
`facts` (register values and accessible memory) hold; and the reading of
conditions and sequences of programs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (offset_nat imm_eq setWidth_imm ofNat_add_ofNat toNat_ofNat_of_lt)

/-- A part of `W` read after a write to another part. -/
theorem readW_writeW_W {m : Mem} {W : Addr} {d e w w' : Nat} (v : BitVec w') (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d)
    (hd : d + w / 8 ≤ 2 ^ 64) (he : e + w' / 8 ≤ 2 ^ 64) (hw : w / 8 < 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) w = m.readW (W + BitVec.ofNat 64 d) w :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) hw

/-- Runs a block of the instructions the AES-GCM-SIV code uses. -/
macro "srun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, execAlu32, execShift, State.load64, State.store64, State.load32, State.store32,
    State.load8, State.store8, State.ea, State.setReg32, offset_nat, at_, imm, ptr, tagO, akO, ekO, hO, yO, cmO,
    ccO, bO, okO, roundsO, nonceO, aadO, alenO, dataO, lenO, skO, revO, ghO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, setWidth_imm, and_self, and_true, true_and, BitVec.add_zero,
    readW_writeW_W, $ts,*]) <;> try rfl)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h
theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl
theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => seq_assoc3 h)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

end VG.Proof.AesGcmSiv.X86_64
