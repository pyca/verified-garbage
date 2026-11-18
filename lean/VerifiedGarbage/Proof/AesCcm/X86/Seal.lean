module

import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.X86.Mac
public import VerifiedGarbage.Proof.AesCcm.X86.Run
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86.Loops
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.AesCcm.X86.Run
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.Common
meta import VerifiedGarbage.Proof.AesGcm.X86.Env
meta import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesCcm.X86.Entry
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCcm.X86.Absorb
public import VerifiedGarbage.Proof.AesCcm.X86.Crypt
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `AesCcm.X86.Top`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Args`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86.Contract`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as an eleventh argument, `work`, against the shared contracts
with it appended (`Proof/AesCcm/Scratch.lean`), which imply these
(`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); the calls push their
arguments and return addresses below `esp`: 60 bytes for a call of
`vg_cmac_aes_update` (its own 28 and the 32 of its calls of `vg_aes_ctr32_to`),
which no buffer overlaps, nor the return address.
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The buffers of `vg_aes_ccm_seal(schedule, rounds, nonce, nonce_len, aad, aad_len, data, len, tag, tag_len, work)`
and `vg_aes_ccm_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
abbrev aadR (s : State) : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
abbrev tagR (s : State) : Region := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩
abbrev workR (s : State) : Region := ⟨(arg s 10).setWidth 64, 2560⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 44⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (workR s) ∧ (schR s).Disjoint (argsR' s) ∧
  (nonceR s).Disjoint (dataR s) ∧ (nonceR s).Disjoint (workR s) ∧ (nonceR s).Disjoint (argsR' s) ∧
  (aadR s).Disjoint (dataR s) ∧ (aadR s).Disjoint (workR s) ∧ (aadR s).Disjoint (argsR' s) ∧
  (dataR s).Disjoint (tagR s) ∧ (dataR s).Disjoint (workR s) ∧ (dataR s).Disjoint (argsR' s) ∧
  (tagR s).Disjoint (workR s) ∧ (tagR s).Disjoint (argsR' s) ∧ (workR s).Disjoint (argsR' s) ∧
  (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (nonceR s) ∧ (retR s).Disjoint (aadR s) ∧
  (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (tagR s) ∧ (retR s).Disjoint (workR s) ∧
  (retR s).Disjoint (argsR' s) ∧
  (stackR s).Disjoint (schR s) ∧ (stackR s).Disjoint (nonceR s) ∧ (stackR s).Disjoint (aadR s) ∧
  (stackR s).Disjoint (dataR s) ∧ (stackR s).Disjoint (tagR s) ∧ (stackR s).Disjoint (workR s) ∧
  (stackR s).Disjoint (argsR' s) ∧
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
  (arg s 10).toNat + 2560 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧
  valid (arg s 9).toNat (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat = true

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s] ∧ s.wr = [dataR s, tagR s, workR s, argsR' s] ∧ oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s, tagR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧ oneLay s

/-- All eleven stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 11, arg s₁ i = arg s₂ i

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
    (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

/-- `vg_aes_ccm_seal`. -/
def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (arg s 9).toNat
        (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) (arg s 9).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) then [] else
  [if (openRes s).isSome then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openX86 : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = zeros (arg s 7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`).
Between the entry and the exit, the pieces only write the parts of `W` in
`mutR`, the stack below `SP` and the data, so they keep the slots, the saved
registers, the key schedule, the nonce and the associated data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv argsR argsR_eq below_eq SavedAt savedR ofNat_toNat32)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W SP s N nl
  aad : Buf W SP s A al
  data : Buf W SP s D n
  tag : Buf W SP s T tl
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩
  nd : (⟨w64 N, nl⟩ : Region).Disjoint ⟨w64 D, n⟩
  ad : (⟨w64 A, al⟩ : Region).Disjoint ⟨w64 D, n⟩
  td : (⟨w64 T, tl⟩ : Region).Disjoint ⟨w64 D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  al32 : al < 2 ^ 32
  n32 : n < 2 ^ 32
  retW : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  retD : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 D, n⟩
  retT : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 T, tl⟩
  args : Covers [argsR SP 11] (s.rd ++ s.wr)
  argsW : (argsR SP 11).Disjoint ⟨w64 W, 2560⟩
  fa : SP.toNat + 4 + 4 * 11 ≤ 2 ^ 32

/-- `Args`, from what both preconditions say, with the key schedule, the
nonce, the associated data and the tag readable and the data, the working
space and the arguments writable. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (mrd : ∀ r ∈ [schR s, nonceR s, aadR s, tagR s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [dataR s, workR s, argsR' s], Covers [r] s.wr) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  simp only [oneLay, stackR] at h
  obtain ⟨d1, d2, _, d4, d5, _, d7, d8, _, d10, d11, _, d13, _, d15, _, _, _, d19, d20, d21, _,
    b1, b2, b3, b4, b5, b6, _, f1, f2, f3, f4, f5, f6, hsp, hfa, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  rw [show (60 : Addr) = BitVec.ofNat 64 60 from rfl, below_eq hsp] at b1 b2 b3 b4 b5 b6
  exact {
    lay := ⟨f1, f6, hsp, d2, b1, b6⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), f2, d5, b2⟩
    aad := ⟨mrd _ (by simp), f3, d8, b3⟩
    data := ⟨Proof.AesGcm.X86.covers_left (mwr _ (by simp)), f4, d11, b4⟩
    tag := ⟨mrd _ (by simp), f5, d13, b5⟩
    dw := mwr _ (by simp)
    dk := d1
    nd := d4
    ad := d7
    td := d10.symm
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    al32 := BitVec.isLt _
    n32 := BitVec.isLt _
    retW := d21
    retD := d19
    retT := d20
    args := by rw [argsR_eq]; exact Proof.AesGcm.X86.covers_left (mwr _ (by simp))
    argsW := by rw [argsR_eq]; exact d15.symm
    fa := by omega_using [hfa] }

theorem args_of_seal {s : State} (h : sealPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine args_of_lay hl (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)

/-- In `seal`, the tag is writable. -/
theorem tag_wr {s : State} (h : sealPre s) : Covers [tagR s] s.wr :=
  covers_of_mem (by rw [h.2.1]; simp)

theorem args_of_open {s : State} (h : openPre s) :
    Args s (arg s 0) (arg s 10) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 8) (arg s 1).toNat
      (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat (arg s 9).toNat := by
  obtain ⟨hrd, hwr, hl⟩ := h
  exact args_of_lay hl (fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)))
    (fun r hr => covers_of_mem (by rw [hwr]; exact hr))

/-! ## What the pieces keep -/

section
variable {K W SP D : BitVec 32} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {s₀ : State} (S : SavedAt m W s₀) : SavedAt m' W s₀ :=
  S.frame hf fun r hr => (kept_mut L hD (d := 128) (k := 16) (.inl ⟨by decide, by decide⟩) r hr)

theorem ciph_mut (L : Lay K W SP) (hdk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hf : Frame (mutR W SP D n) m m') :
    Spec.Ccm.ctxCiph m' (w64 K) R = Spec.Ccm.ctxCiph m (w64 K) R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    (hPD : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega_using [this])

end

/-- Every region of `rs` is part of one of `mutR`. -/
abbrev InMut (W SP D : BitVec 32) (n : Nat) (rs : List Region) : Prop :=
  ∀ r ∈ rs, ∃ r' ∈ mutR W SP D n, Region.Sub r r'

theorem inMut_macR (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) : InMut W SP D n (macR W SP y) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩

theorem inMut_ctrR (W SP D : BitVec 32) (n : Nat) : InMut W SP D n (ctrR W SP D n) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem frame_toMut {W SP D : BitVec 32} {n : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : InMut W SP D n rs) : Frame (mutR W SP D n) m m' := hf.sub h

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: the start of both functions

Untrusted: everything here is checked by Lean. `seal` and `open` both start
with the entry and `Ctr₀` (`start_ok`); after them, the slots hold the
arguments and `W + 48` holds `Ctr₀`, and the key schedule, the nonce, the
associated data, the data, the received tag and the return address are as
they were (`Started`). The pieces after them write only `mutR`, which keeps
all of that but the data (`Started.mut`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt ret_below ofNat_toNat32)

/-- After the entry and `Ctr₀`. -/
structure Started (s : State) (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s' : State) : Prop where
  env : Env K W SP s'
  slots : Slots W K R N A D T nl al n tl s'.mem
  saved : SavedAt s'.mem W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  c0 : bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0
  ciph : Spec.Ccm.ctxCiph s'.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R
  aadB : bytesAt s'.mem (w64 A) al = bytesAt s.mem (w64 A) al
  dataB : bytesAt s'.mem (w64 D) n = bytesAt s.mem (w64 D) n
  tagB : bytesAt s'.mem (w64 T) tl = bytesAt s.mem (w64 T) tl
  ret : s'.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32

/-- The entry and `Ctr₀`. -/
theorem start_ok {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) :
    WP isa (.seq ccmEntry ctrs) s (Started s K W SP N A D T R nl al n tl) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (entry_ok a10 Ar.perm.w (by rw [hsp]; exact Ar.args) (by rw [hsp]; exact Ar.argsW)
    (by rw [hsp]; exact Ar.fa) L.fw) fun s₁ E₀ => ?_)
  have E₁ : Env K W SP s₁ := ⟨E₀.ebp, by rw [E₀.esp, hsp], Ar.perm.of_eq E₀.rd E₀.wr⟩
  have sl : ∀ p ∈ entryPs, slotv s₁.mem W p.2 = arg s p.1 := E₀.slots
  have S₁ : Slots W K R N A D T nl al n tl s₁.mem :=
    ⟨by rw [sl (0, ctxO) (by simp), a0], by rw [sl (1, roundsO) (by simp), a1],
      by rw [sl (2, nonceO) (by simp), a2], by rw [sl (3, nlenO) (by simp), a3],
      by rw [sl (4, aadO) (by simp), a4], by rw [sl (5, alenO) (by simp), a5],
      by rw [sl (6, dataO) (by simp), a6], by rw [sl (7, lenO) (by simp), a7],
      by rw [sl (9, Impl.AesGcm.X86.tglO) (by simp), a9], by rw [sl (8, Impl.AesGcm.X86.tpO) (by simp), a8]⟩
  have fE := E₀.frame
  have bE : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₁.mem (w64 P) len = bytesAt s.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_using [this])
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have cE : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    ctxCiph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.mono (ctrs_ok L E₁ S₁.nonce S₁.nlen (Ar.nonce.of_eq E₀.rd E₀.wr) Ar.h7 Ar.h13)
    fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_
  have f₂' : Frame (mutR W SP D n) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  have b₂ : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₂.mem (w64 P) len = bytesAt s₁.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_using [this])
  refine ⟨E₂, slots_mut L Ar.data.w f₂' S₁, saved_mut L Ar.data.w f₂' E₀.saved, by rw [rd₂, E₀.rd],
    by rw [wr₂, E₀.wr], by rw [c₂, bE Ar.nonce], ?_, by rw [b₂ Ar.aad, bE Ar.aad], by rw [b₂ Ar.data, bE Ar.data],
    ?_, ?_⟩
  · rw [ctxCiph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb, cE]
  · rw [b₂ Ar.tag, bE Ar.tag]
  · rw [Proof.AesGcm.X86.ret_kept f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide))),
      Proof.AesGcm.X86.ret_kept fE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide)))]

/-- What the pieces after the start keep. -/
theorem Started.mut {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) {s₁ : State} (St : Started s K W SP N A D T R nl al n tl s₁) {m : Mem}
    (hf : Frame (mutR W SP D n) s₁.mem m) :
    Slots W K R N A D T nl al n tl m ∧ SavedAt m W s ∧
      Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R ∧
      bytesAt m (w64 A) al = bytesAt s.mem (w64 A) al ∧ m.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
  have L := Ar.lay
  refine ⟨slots_mut L Ar.data.w hf St.slots, saved_mut L Ar.data.w hf St.saved,
    by rw [ciph_mut L Ar.dk Ar.rounds hf, St.ciph], by rw [buf_mut Ar.aad Ar.ad hf, St.aadB], ?_⟩
  rw [Proof.AesGcm.X86.ret_kept hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ar.retW.sub_right (Region.sub_prefix (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact ret_below L.sp
    · exact Ar.retD), St.ret]

end VG.Proof.AesCcm.X86

end

end

/-! ### `AesCcm.X86.Mask`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86: masking the data, and the tag copied out

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`: the data if `ok = 1`, zeros if `ok = 0` (`mask_ok`).
`tagOut` copies the first `tag_len` bytes of the tag at `W` to `tag`
(`tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop tglO tpO rO)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv in_of_covers covers_left succ_ofNat32 add_zero32 pred_count pred_beq bytesAt_succ
  length_bytesAt and_self_beq32 WEnv padLoop_ok zero4_fold toNat_ofNat32 LoopPre CopyPost copyLoop_ok CT)

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hb, mask_byte32]
  · cregs [hs, succ_ofNat32]
  · cregs [hc]
  · cmems [hc]
  · intro r h₁ h₂ h₃; cregs [h₁, h₂, h₃]
  all_goals cmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else zeros n) := by
  obtain ⟨s₁, run₁, m₁, cx₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hlen]
    · cmems [hlen]; rw [and_self_beq32 hn32]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : Env K W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    have hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
    refine ⟨_, by crun [bp₁, L.aW, E₁.perm.wR, hok₁, hd₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [m₁]
    · cregs [hok₁]; rfl
    · cregs [hd₁]
    · cregs [cx₁]
    · cregs [bp₁]
    · cregs [sp₁]
    · cmems [rd₁]
    · cmems [wr₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := hD.wrap
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [di₂, add_zero32], by rw [cx₂, Nat.sub_zero], by
      rw [m₂]; cases c <;> simp [Spec.Aes.bytesAt, zeros, writeBytes_nil], fun r _ _ _ => rfl, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega_arith))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega_arith))
    (by rw [wr]; exact in_of_covers hDw hj (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  have hmem : t'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have E' : Env K W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The tag copied out -/

/-- `tagOut`: the first `t` bytes at `W` written to `tag` (kept at `W + tpO`). -/
theorem tagOut_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {T : BitVec 32} {t : Nat}
    (hv : slotv s.mem W tglO = BitVec.ofNat 32 t) (hT : slotv s.mem W tpO = T) (ht1 : 1 ≤ t) (ht : t ≤ 16)
    (Tb : Buf W SP s T t) (tw : Covers [⟨w64 T, t⟩] s.wr) :
    WP isa tagOut s fun s' => s'.mem = writeBytes s.mem (w64 T) (bytesAt s.mem (w64 W) t) ∧ Env K W SP s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (.reg .ebp), .mov .edx (slot tpO), .mov .ecx (slot tglO)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .edi = W ∧ s₁.gpr .edx = T ∧ s₁.gpr .ecx = BitVec.ofNat 32 t ∧ s₁.gpr .ebp = W ∧
      s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems []
    · cregs [E.ebp]
    · cregs [hT]
    · cregs [hv]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ W T t := ⟨hdi, hdx, hcx, ht1, by omega_arith, by have := L.fw; omega_arith, Tb.wrap,
    by rw [hrd₁, hwr₁]; simpa using covers_left (E.perm.wC (d := 0) (n := t) (by omega_arith)),
    by rw [hwr₁]; exact tw, (Tb.w.sub_right (Region.sub_prefix (by omega_arith))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, hm₁], ⟨?_, ?_, E.perm.of_eq ?_ ?_⟩, ?_, ?_⟩
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hbp]
  · rw [P.other _ (by decide) (by decide) (by decide) (by decide), hsp]
  all_goals first | rw [P.rd, hrd₁] | rw [P.wr, hwr₁]

theorem tagOut_ct {K W SP T : BitVec 32} {t : Nat} {I : State → Prop} (L : Lay K W SP)
    (h : ∀ s, I s → Env K W SP s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t ∧ slotv s.mem W tpO = T) :
    CT I tagOut := by
  refine CT.seq (J := fun s => s.gpr .edi = W ∧ s.gpr .edx = T ∧ s.gpr .ecx = BitVec.ofNat 32 t)
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => ?_) (Proof.AesGcm.X86.copyLoop_ct fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2])
  obtain ⟨E, hv, hT⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hv, hT], by cregs [E.ebp], by cregs [hT], by cregs [hv]⟩

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is the start (the
entry and `Ctr₀`, `start_ok`), the MAC of the payload at `W` (`mac_ok`),
encrypted (`tag_ok`), counter mode over the data (`ctr_ok`), the tag copied
to `tag` (`tagOut_ok`) and the exit (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left writeBytes_frame'
  bytesAt_writeBytes_self)

/-- What `tag y` writes, in `mutR`. -/
theorem inMut_tag (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) :
    InMut W SP D n [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 60] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 60, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack keeps its bytes across a frame of
parts of `W` and the stack. -/
theorem buf_kept' {W SP : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 60) {m m' : Mem}
    (hf : Frame rs m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    rcases hrs r hr with h | rfl
    · exact hP.w.sub_right h
    · exact hP.stk.symm) (by have := hP.lt; omega_using [this])

/-- `Ctr₀` is kept by a frame of parts of `W` apart from it. -/
theorem c0_kept {W : BitVec 32} {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) {m m' : Mem} (hf : Frame rs m m') :
    bytesAt m' (w64 W + BitVec.ofNat 64 48) 16 = bytesAt m (w64 W + BitVec.ofNat 64 48) 16 :=
  Proof.AesGcm.X86.bytesAt_frame hf hrs (by decide)

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) (tw : Covers [⟨w64 T, tl⟩] s.wr) :
    WP isa («seal» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)
        (bytesAt s.mem (w64 A) al) = (bytesAt s'.mem (w64 D) n, bytesAt s'.mem (w64 T) tl) := by
  have L := Ar.lay
  obtain hnl := length_bytesAt s.mem (w64 N) nl
  obtain h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  refine seq_assoc (WP.seq (WP.mono (start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- The MAC.
  refine WP.seq (WP.mono (mac_ok v L St.env Ar.rounds St.slots hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 St.c0 (y := 0) (.inl rfl) (Ar.aad.of_eq St.rd St.wr) (Ar.data.of_eq St.rd St.wr)) fun s₃ A₃ => ?_)
  obtain f₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frame_toMut A₃.frame (inMut_macR W SP D n (.inl rfl))
  obtain ⟨S₃, -, -, -, -⟩ := St.mut Ar f₃
  obtain hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) A₃.frame, St.c0]
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L A₃.env Ar.rounds S₃.ctx S₃.rounds h7' h13' hc₃ (y := 0) (.inl rfl))
    fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_)
  obtain f₂₄ : Frame (mutR W SP D n) s₂.mem s₄.mem := f₃.trans (frame_toMut f₄ (inMut_tag W SP D n (.inl rfl)))
  obtain ⟨S₄, -, -, -, -⟩ := St.mut Ar f₂₄
  obtain hc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) f₄, hc₃]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, A₃.rd, St.rd]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, A₃.wr, St.wr]
  obtain hD₄ : bytesAt s₄.mem (w64 D) n = bytesAt s.mem (w64 D) n := by
    rw [buf_kept' Ar.data (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr rfl) f₄,
      buf_kept Ar.data (y := 0) (by decide) A₃.frame, St.dataB]
  -- Counter mode.
  obtain C₄ : CtrCtx K W SP s₄ R (bytesAt s.mem (w64 N) nl) D n :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, hc₄, Ar.data.of_eq rd₄' wr₄',
      by rw [wr₄']; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v C₄ E₄ S₄.ctx S₄.rounds S₄.data S₄.len) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  obtain f₂₅ : Frame (mutR W SP D n) s₂.mem s₅.mem := f₂₄.trans (frame_toMut f₅ (inMut_ctrR W SP D n))
  obtain ⟨S₅, sv₅, ci₅, -, rt₅⟩ := St.mut Ar f₂₅
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄']
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄']
  -- The tag copied out.
  refine WP.seq (WP.mono (tagOut_ok L E₅ S₅.tl S₅.tp (by have := Ar.t4; omega_using [this]) Ar.t16
    (Ar.tag.of_eq rd₅' wr₅') (by rw [wr₅']; exact tw)) fun s₆ ⟨m₆', E₆, rd₆, wr₆⟩ => ?_)
  obtain hTl : tl < 2 ^ 64 := by have := Ar.t16; omega_using [this]
  obtain fT : Frame [⟨w64 T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆']; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain tW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 T, tl⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.tag.w.sub_right (Lay.wSub hk)).symm
  obtain sv₆ : SavedAt s₆.mem W s := sv₅.frame fT (tW (by decide))
  obtain rt₆ : s₆.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT), rt₅]
  -- The exit.
  refine WP.mono (exit_ok (W := W) (s₀ := s) E₆.ebp (by rw [E₆.esp, hsp])
    (by rw [rd₆, wr₆, rd₅', wr₅']; exact covers_left Ar.perm.w) L.fw sv₆ (by rw [hsp]; exact rt₆))
    fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  obtain ci₄ : Spec.Ccm.ctxCiph s₄.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₂₄).2.2.1
  obtain ci₃ : Spec.Ccm.ctxCiph s₃.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₃).2.2.1
  obtain hW₅ : bytesAt s₅.mem (w64 W) tl = bytesAt s₄.mem (w64 W) tl := by
    have ht := Ar.t16
    exact Proof.AesGcm.X86.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by omega_using [ht])) (by omega_using [ht]) (by decide)
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 240) (k := 2320) (.inl (by omega_using [ht])) (by omega_using [ht])
          (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by omega_using [ht]))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by omega_using [ht]))).symm) (by omega_using [hTl])
  obtain e0 : w64 W + BitVec.ofNat 64 0 = w64 W := BitVec.add_zero _
  have o₃ := A₃.out
  rw [e0] at h₄ o₃
  obtain hY := congrArg List.length o₃
  rw [length_bytesAt] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [m₇, Proof.AesGcm.X86.bytesAt_frame fT (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by have := Ar.data.lt; omega_using [this]), h₅, ci₄, hD₄, crypt_eq (hBC _)]
  · have hT₇ : bytesAt s₇.mem (w64 T) tl = bytesAt s₅.mem (w64 W) tl := by
      have := bytesAt_writeBytes_self s₅.mem (w64 T) (bytesAt s₅.mem (w64 W) tl) (by rw [length_bytesAt]; omega_using [hTl])
      rw [length_bytesAt] at this
      rw [m₇, m₆', this]
    rw [hT₇, hW₅, Proof.AesCcm.bytesAt_prefix s₄.mem (w64 W) Ar.t16, h₄,
      take_xorFrom_zero (hBC _) _ (by rw [length_bytesAt]) Ar.t16, o₃, ci₃,
      ← Proof.AesCcm.mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega_using [this]), St.ciph, St.aadB, St.dataB]

end VG.Proof.AesCcm.X86
