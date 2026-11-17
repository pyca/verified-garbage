module

import VerifiedGarbage.Proof.AesCcm.X86.Entry
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCcm.X86.Absorb
public import VerifiedGarbage.Proof.AesCcm.X86.Crypt
public import VerifiedGarbage.Proof.AesGcm.X86.Fn
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ccm

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
