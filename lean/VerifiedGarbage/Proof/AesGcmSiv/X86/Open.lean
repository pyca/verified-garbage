module

public import VerifiedGarbage.Proof.AesGcmSiv.X86.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.GcmSiv.Words
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.GcmSiv
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesGcmSiv.X86.Entry`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.X86.Contract`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as a ninth argument, `work`, against the shared contracts
with it appended (`Proof/AesGcmSiv/Scratch.lean`), which imply these
(`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments are on
the stack, from `[esp + 4]` (cdecl), and may be overwritten (`writeArgs`);
the calls of `vg_aes_ctr32_to`, `vg_aes_expand_key` and `vg_ghash`, which make
no calls, push their arguments and return addresses in the 32 bytes below
`esp`, which no buffer overlaps, nor the return address.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The buffers of `vg_aes_gcm_siv_seal(schedule, rounds, nonce, aad, aad_len, data, len, tag, work)`
and `vg_aes_gcm_siv_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, 12⟩
abbrev aadR (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
abbrev tagR (s : State) : Region := ⟨(arg s 7).setWidth 64, 16⟩
abbrev workR (s : State) : Region := ⟨(arg s 8).setWidth 64, 2816⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 36⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩

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
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 12 ≤ 2 ^ 32 ∧
  (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧
  (arg s 7).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 8).toNat + 2816 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 14)

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s] ∧ s.wr = [dataR s, tagR s, workR s, argsR' s] ∧ oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s, tagR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧ oneLay s

/-- All nine stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 9, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (keyLen (arg s 1).toNat)
        (bytesAt s.mem ((arg s 2).setWidth 64) 12) (bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
        (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) =
      (bytesAt s'.mem ((arg s 5).setWidth 64) (arg s 6).toNat, bytesAt s'.mem ((arg s 7).setWidth 64) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (keyLen (arg s 1).toNat)
    (bytesAt s.mem ((arg s 2).setWidth 64) 12) (bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
    (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) (bytesAt s.mem ((arg s 7).setWidth 64) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `eax` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem D n = pt
  | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .eax = 1) (hd : bytesAt s'.mem D n = pt) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .eax = 0) (hd : bytesAt s'.mem D n = zeros n) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openX86 : Contract isa where
  pre := openPre
  post s s' := openPost (openResult s) s' ((arg s 5).setWidth 64) (arg s 6).toNat
  pub := onePub

end VG.Proof.AesGcmSiv.X86

end

end


/-!
# AES-GCM-SIV on x86: the arguments and the entry

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the public arguments (`prmOf`), how they lie (`lay_of`) and what the
state may access (`perm_of`). The entry saves our caller's registers in `W`
(AES-GCM's `save_ok`) and copies the stack arguments into their slots
(`keeps_ok`): after it, `Env` holds (`entry_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok
  keepR runBlock_app_of in_off below_eq covers_left)

/-- What both preconditions say: the layout, and that the buffers may be
read (the key schedule, the nonce, the additional data and the tag) or
written (the data, `work` and the arguments). -/
structure onePre (s : State) : Prop where
  lay : oneLay s
  rd : ∀ r ∈ [schR s, nonceR s, aadR s, tagR s], Covers [r] (s.rd ++ s.wr)
  wr : ∀ r ∈ [dataR s, workR s, argsR' s], Covers [r] s.wr

theorem onePre_seal {s : State} (h : sealPre s) : onePre s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine ⟨hl, fun r hr => ?_, fun r hr => ?_⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))

theorem onePre_open {s : State} (h : openPre s) : onePre s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine ⟨hl, fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)),
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)⟩

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := arg s 0
  W := arg s 8
  N := arg s 2
  A := arg s 3
  D := arg s 5
  T := arg s 7
  SP := s.gpr .esp
  R := (arg s 1).toNat
  al := (arg s 4).toNat
  n := (arg s 6).toNat

/-- What the precondition says of the stack arguments. -/
structure ArgsOk (s : State) : Prop where
  rA : Covers [argsR (s.gpr .esp) 9] (s.rd ++ s.wr)
  aw : (argsR (s.gpr .esp) 9).Disjoint ⟨w64 (arg s 8), 2816⟩
  fa : (s.gpr .esp).toNat + 4 + 4 * 9 ≤ 2 ^ 32

theorem lay_of {s : State} (h : onePre s) : Lay (prmOf s) := by
  obtain ⟨sd, sw, _, nd, nw, _, ad, aw, _, dt, dw, _, tw, _, _, _, _, _, rd, rt, rw, _, bs, bn, ba, bd, bt, bw, _,
    fK, fN, fA, fD, fT, fW, sp32, _, hR⟩ := h.lay
  simp only [stackR] at bs bn ba bd bt bw
  rw [show (32 : Addr) = BitVec.ofNat 64 32 from rfl, below_eq sp32] at bs bn ba bd bt bw
  exact ⟨fK, fW, fN, fA, fD, fT, sp32, sw, sd, nw, nd, aw, ad, dw, tw, dt.symm, bs, bn, ba, bd, bw, bt, hR,
    BitVec.isLt _, BitVec.isLt _, rw, rd, rt⟩

theorem perm_of {s : State} (h : onePre s) : Perm (prmOf s) s :=
  ⟨h.rd (schR s) (by simp), h.rd (nonceR s) (by simp), h.rd (aadR s) (by simp), h.wr (dataR s) (by simp),
    h.wr (workR s) (by simp), h.rd (tagR s) (by simp)⟩

theorem argsOk_of {s : State} (h : onePre s) : ArgsOk s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, wa, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, spf, -⟩ := h.lay
  refine ⟨?_, ?_, by omega_using [spf]⟩
  · rw [argsR_eq]; exact covers_left (h.wr (argsR' s) (by simp))
  · rw [argsR_eq]; exact wa.symm

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, nonceO), (3, aadO), (4, alenO), (5, dataO), (6, lenO), (7, tpO)]

theorem sivEntry_eq : sivEntry = entry 8 (entryPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (p : Prm) (s' : State) : Prop where
  env : Env p s'
  saved : SavedAt s'.mem p.W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 128, 48⟩] s.mem s'.mem

/-- The entry. -/
theorem entry_ok {s : State} (h : onePre s) : WP isa sivEntry s (Entered s (prmOf s)) := by
  have L := lay_of h
  have P := perm_of h
  have Ao := argsOk_of h
  rw [sivEntry_eq]
  generalize hSP : s.gpr .esp = SP at Ao
  have rA := Ao.rA
  have aw := Ao.aw
  have fa := Ao.fa
  rw [hSP] at rA aw fa
  have fw : (arg s 8).toNat + 2560 ≤ 2 ^ 32 := by have := L.ww; simp only [prmOf] at this; omega_using [this]
  have wW : Covers [⟨w64 (arg s 8), 2560⟩] s.wr := P.w2560
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 8) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 8) 32)).gpr .eax = arg s 8 := by
    rw [gpr_setReg_self, ← hSP]; rfl
  let s₀ := s.setReg .eax (s.mem.readW (argA SP 8) 32)
  try rewrite [show s.setReg .eax (s.mem.readW (argA SP 8) 32) = s₀ from rfl] at *
  have hs₀ : s₀ = s.setReg .eax (s.mem.readW (argA SP 8) 32) := rfl
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have argW : ∀ {i}, i < 9 → ∀ {d k : Nat}, d + k ≤ 2816 →
      ∀ r ∈ [(⟨w64 (arg s 8) + BitVec.ofNat 64 d, k⟩ : Region)], (⟨argA SP i, 4⟩ : Region).Disjoint r :=
    fun hi _ _ hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (aw.sub_left (argA_sub hi fa)).sub_right (Lay.wSub hk)
  have hA₁ : ∀ i < 9, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
    exact rfl
  have aw' : (argsR SP 9).Disjoint ⟨w64 (arg s 8), 2560⟩ := aw.sub_right (Region.sub_prefix (by decide))
  have ke : KeepEnv (arg s 8) SP 9 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw', fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = arg s 8 := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 (arg s 8) + BitVec.ofNat 64 128, 48⟩] s.mem s₃.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem (arg s 8) s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  have sl : ∀ q ∈ entryPs, slotv s₃.mem (arg s 8) q.2 = arg s q.1 := fun q hq => by
    have e := sl₃ q hq
    have hq1 : q.1 < 9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hA₁ q.1 hq1] at e
    exact e
  have ofN : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  refine ⟨⟨bp₃, by rw [sp₃, ← hSP]; rfl, P.of_eq (by rw [rd₃, rd₁]; rfl) (by rw [wr₃, wr₁]; rfl),
    ⟨sl (0, ctxO) (by simp), by simp only [prmOf]; rw [sl (1, roundsO) (by simp)]; exact (ofN _).symm,
      sl (2, nonceO) (by simp), sl (3, aadO) (by simp),
      by simp only [prmOf]; rw [sl (4, alenO) (by simp)]; exact (ofN _).symm, sl (5, dataO) (by simp),
      by simp only [prmOf]; rw [sl (6, lenO) (by simp)]; exact (ofN _).symm, sl (7, tpO) (by simp)⟩⟩, hsv, by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, f₃'⟩

end VG.Proof.AesGcmSiv.X86

end

end

/-! ### `AesGcmSiv.X86.Seal`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the tag
copied out to `tag` and the restore compute `encryptWith` (RFC 8452 §4) of
the arguments (`seal_wp`), given that the tag input computed with GHASH is
the RFC's (`Proof.GcmSiv.Words.tagInputG`, related to it by
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`). Each
piece writes only `mutR`, which keeps the slots, our caller's registers,
the return address, the key schedule, the nonce and the additional data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : Prm} (L : Lay p) {s₀ t : State} (E : Env p t) (hsp : p.SP = s₀.gpr .esp)
    (hs : SavedAt t.mem p.W s₀) (hret : t.mem.readW (w64 p.SP) 32 = s₀.mem.readW (w64 p.SP) 32) :
    WP isa (.block Impl.AesGcm.X86.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .eax = t.gpr .eax :=
  WP.mono (Proof.AesGcm.X86.exit_ok E.ebp (by rw [E.esp, hsp]) (covers_left E.perm.w2560)
    (by have := L.ww; omega_using [this]) hs (by rw [← hsp]; exact hret)) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩

/-- What the entry wrote is in our caller's registers and the slots. -/
theorem entered_mut {s : State} {p : Prm} {s₁ : State} (L : Lay p) (En : Entered s p s₁) :
    s₁.mem.readW (w64 p.SP) 32 = s.mem.readW (w64 p.SP) 32 ∧
      Spec.GcmSiv.ctxCiph s₁.mem (w64 p.K) p.R = Spec.GcmSiv.ctxCiph s.mem (w64 p.K) p.R ∧
      bytesAt s₁.mem (w64 p.N) 12 = bytesAt s.mem (w64 p.N) 12 ∧
      bytesAt s₁.mem (w64 p.A) p.al = bytesAt s.mem (w64 p.A) p.al ∧
      bytesAt s₁.mem (w64 p.D) p.n = bytesAt s.mem (w64 p.D) p.n ∧
      bytesAt s₁.mem (w64 p.W) 16 = bytesAt s.mem (w64 p.W) 16 := by
  have f := En.frame
  obtain d : ∀ {P : Addr} {k : Nat}, (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 128, 48⟩ : Region)], (⟨P, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  refine ⟨Proof.AesGcm.X86.ret_kept f (d L.retW), ?_, Proof.AesGcm.X86.bytesAt_frame f (d L.n_w) (by decide),
    Proof.AesGcm.X86.bytesAt_frame f (d L.a_w) (by have := L.al32; omega_using [this]),
    Proof.AesGcm.X86.bytesAt_frame f (d L.d_w) (by have := L.n32; omega_using [this]),
    Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := p.W) (a := 0) (n := 16) (d := 128) (k := 48) (.inl (by decide)) (by decide)
        (by decide)) (by decide)⟩
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame f (d (L.k_w.sub_left (Region.sub_prefix L.rounds_le)))
    (by have := L.rounds_le; omega_using [this])]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (hs : sealPre s) :
    WP isa («seal» v.callees) s fun s' => abiPreserved s s' ∧ sealX86.post s s' := by
  obtain h := onePre_seal hs
  obtain tW : Covers [⟨w64 (prmOf s).T, 16⟩] s.wr := covers_of_mem (by rw [hs.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (entry_ok h) fun s₁ En => ?_)
  obtain ⟨ret₁, hK₁, n₁, a₁, d₁, -⟩ := entered_mut L En
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L En.env) fun s₂ Ky => ?_)
  obtain f₂ := frame_toMut Ky.frame (inMut_keyR _)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  obtain f₃ := frame_toMut Po.frame (inMut_polyR _)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  obtain f₄ := frame_toMut Tg.frame (inMut_tagWr _ (by decide))
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  obtain f₅ := frame_toMut Cr.frame (inMut_cryR _)
  obtain f₂₅ := (f₂.trans f₃).trans (f₄.trans f₅)
  -- The tag copied out.
  obtain tW₅ : Covers [⟨w64 (prmOf s).T, 16⟩] s₅.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, En.wr]; exact tW
  refine WP.seq (WP.mono (tagOut_ok L Cr.env tW₅) fun s₆ ⟨tg₆, f₆, bp₆, sp₆, _, rd₆, wr₆⟩ => ?_)
  obtain E₆ := Cr.env.tag L bp₆ sp₆ rd₆ wr₆ f₆
  obtain sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (SavedAt.mut L f₂₅ En.saved).frame f₆ (w_t L (d := 128) (k := 16) (by decide))
  obtain rT : ∀ q ∈ [(⟨w64 (prmOf s).T, 16⟩ : Region)], (⟨w64 (prmOf s).SP, 4⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.retT
  obtain ret₆ : s₆.mem.readW (w64 (prmOf s).SP) 32 = s.mem.readW (w64 (prmOf s).SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept f₆ rT, ret_mut L f₂₅, ret₁]
  obtain d₆ : bytesAt s₆.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_d.symm) (by omega_using [hn])
  -- `restore`.
  refine WP.mono (exit_ok L E₆ rfl sv₆ ret₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
      (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)
      (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al) =
    (bytesAt s'.mem (w64 (prmOf s).D) (prmOf s).n, bytesAt s'.mem (w64 (prmOf s).T) 16)
  rw [hm, d₆, tg₆]
  -- What the pieces read.
  obtain n₂ : bytesAt s₂.mem (w64 (prmOf s).N) 12 = bytesAt s.mem (w64 (prmOf s).N) 12 := by
    rw [nonce_mut L f₂, n₁]
  obtain a₂ : bytesAt s₂.mem (w64 (prmOf s).A) (prmOf s).al = bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al := by
    rw [aad_mut L f₂, a₁]
  obtain dk₂ : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).D, (prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  obtain d₂ : bytesAt s₂.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dk₂ (by omega_using [hn]), d₁]
  obtain d₄ : bytesAt s₄.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega_using [hn]),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact absorbR_buf L.d_w L.bd r hr) (by omega_using [hn]), d₂]
  obtain dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])]
  obtain key₃ : Spec.GcmSiv.ctxCiph s₃.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    refine dS (fun r hr => ?_) Po.frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain key₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    refine (dS (fun r hr => ?_) Tg.frame).trans key₃
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain t₅ : bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 := by
    refine Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.d_w' (by decide)).symm
    · exact (L.bw' (by decide)).symm
  rw [BitVec.add_zero] at t₅
  have tg := Tg.out
  rw [BitVec.add_zero] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.X86

end

end

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the received tag
copied to `W`, the keys, counter mode on the data from it, POLYVAL of the
result and the tag input, its tag at `W + 240`, the comparison, the mask and
the restore compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left length_bytesAt)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- Counter mode after the keys keeps what POLYVAL starts from. -/
theorem keys_crypt {p : Prm} (L : Lay p) {σ s₂ s₃ : State} (Ky : KeysPost p σ s₂) (Cr : CryptPost p s₂ s₃) :
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 80) = 0 ∧
    bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 := by
  obtain dCr : ∀ {d : Nat}, 16 ≤ d → d + 16 ≤ 96 → ∀ r ∈ cryR p,
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact (L.d_w' (by omega_using [h₂])).symm
    · exact (L.bw' (by omega_using [h₂])).symm
  obtain a₃ : bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame Cr.frame (dCr (by decide) (by decide)) (by decide)
  refine ⟨?_, ?_, a₃⟩
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.hkey, a₃]
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.acc]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (hs : openPre s) :
    WP isa («open» v.callees) s fun s' => abiPreserved s s' ∧ openX86.post s s' := by
  obtain h := onePre_open hs
  obtain L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (entry_ok h) fun s₀ En => ?_)
  obtain ⟨ret₀, hK₀, n₀, a₀, d₀, -⟩ := entered_mut L En
  -- The received tag.
  refine WP.seq (WP.mono (recvTag_ok L En.env) fun s₁ ⟨E₁, tg₁, fr₁, _, _⟩ => ?_)
  obtain fr₁' : Frame (mutR (prmOf s)) s₀.mem s₁.mem := frame_toMut fr₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using inMut_w (prmOf s) (d := 0) (k := 16) (.inl (by decide))
  obtain ret₁ : s₁.mem.readW (w64 (prmOf s).SP) 32 = s.mem.readW (w64 (prmOf s).SP) 32 := by
    rw [ret_mut L fr₁', ret₀]
  obtain hK₁ := (ciph_mut L fr₁').trans hK₀
  obtain n₁ := (nonce_mut L fr₁').trans n₀
  obtain a₁ := (aad_mut L fr₁').trans a₀
  obtain d₁ : bytesAt s₁.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n :=
    (Proof.AesGcm.X86.bytesAt_frame fr₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.d_w.sub_right (Region.sub_prefix (by decide)))
      (by omega_using [hn])).trans d₀
  obtain tag₁ : bytesAt s₁.mem (w64 (prmOf s).W) 16 = bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [tg₁]
    exact Proof.AesGcm.X86.bytesAt_frame En.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_w.sub_right (Lay.wSub (by decide))) (by decide)
  obtain sv₁ := SavedAt.mut L fr₁' En.saved
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  obtain f₂ := frame_toMut Ky.frame (inMut_keyR _)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v L Ky.env) fun s₃ Cr => ?_)
  obtain f₃ := frame_toMut Cr.frame (inMut_cryR _)
  obtain ⟨hG₃, hY₃, a₃⟩ := keys_crypt L Ky Cr
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Cr.env hG₃ hY₃) fun s₄ Po => ?_)
  obtain f₄ := frame_toMut Po.frame (inMut_polyR _)
  -- Its tag at `W + 240`.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 240) (by decide)) fun s₅ Tg => ?_)
  obtain f₅ := frame_toMut Tg.frame (inMut_tagWr _ (by decide))
  -- The comparison.
  obtain ⟨s₆, run₆, ax₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env (prmOf s) s₆ := Tg.env.keep (by rw [bp₆, Tg.env.ebp]) (by rw [sp₆, Tg.env.esp]) rd₆ wr₆ hm₆
  obtain ax₆' : s₆.gpr .eax = BitVec.ofNat 32 (if decide (bytesAt s₅.mem (w64 (prmOf s).W) 16 =
      bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 240) 16) then 1 else 0) := by
    rw [ax₆]; simp only [okVal, decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ ax₆') fun s₇ Mk => ?_)
  obtain fM : Frame (mutR (prmOf s)) s₆.mem s₇.mem := by
    rw [Mk.mem]
    exact frame_toMut (writeBytes_frame _ _ _ (by
      split <;> simp only [length_bytesAt, Spec.GcmSiv.zeros, List.length_replicate] <;>
        exact Region.contains_self _ _) : Frame [⟨w64 (prmOf s).D, (prmOf s).n⟩] _ _) fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact inMut_d _
  obtain f₂₇ : Frame (mutR (prmOf s)) s₁.mem s₇.mem := ((f₂.trans f₃).trans (f₄.trans f₅)).trans (hm₆ ▸ fM)
  -- The restore.
  refine WP.mono (exit_ok L Mk.env rfl (SavedAt.mut L f₂₇ sv₁) (by rw [ret_mut L f₂₇, ret₁]))
    fun s' ⟨ga, hm, hax⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  obtain n₃ : bytesAt s₃.mem (w64 (prmOf s).N) 12 = bytesAt s.mem (w64 (prmOf s).N) 12 := by
    rw [nonce_mut L (f₂.trans f₃), n₁]
  obtain a₃' : bytesAt s₃.mem (w64 (prmOf s).A) (prmOf s).al = bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al := by
    rw [aad_mut L (f₂.trans f₃), a₁]
  obtain dK : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).D, (prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  obtain d₂ : bytesAt s₂.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dK (by omega_using [hn]), d₁]
  obtain tK : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).W + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain tag₂ : bytesAt s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame tK (by decide), BitVec.add_zero, tag₁]
  obtain tag₅ : bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.d_w' (by decide)).symm
        · exact (L.bw' (by decide)).symm) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  obtain dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])]
  obtain ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    rw [dS (fun r hr => ?_) Po.frame, ciph_cryR L Cr.frame]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain d₅ : bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₃.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega_using [hn]),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact absorbR_buf L.d_w L.bd r hr) (by omega_using [hn])]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.mem
  rw [hm₆, tg, tag₅] at md
  obtain ax : s'.gpr .eax = s₆.gpr .eax := by rw [hax, Mk.eax]
  rw [ax₆', tg, tag₅] at ax
  show openPost (openResult s) s' (w64 (prmOf s).D) (prmOf s).n
  obtain hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
            (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) =
          bytesAt s.mem (w64 (prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  obtain hD₅ : bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n = Spec.GcmSiv.ctr
      (Spec.GcmSiv.aes (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)).2)
      (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16)) (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) := by
    rw [d₅, pt₃]
  obtain hl : ∀ c : Bool, (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n
      else Spec.GcmSiv.zeros (prmOf s).n).length = (prmOf s).n := fun c => by
    cases c <;> simp [length_bytesAt, Spec.GcmSiv.zeros]
  obtain mD : ∀ c : Bool, bytesAt (writeBytes s₅.mem (w64 (prmOf s).D) (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n
      else Spec.GcmSiv.zeros (prmOf s).n)) (w64 (prmOf s).D) (prmOf s).n =
      if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n else Spec.GcmSiv.zeros (prmOf s).n := fun c => by
    obtain e := Proof.AesGcm.X86.bytesAt_writeBytes_self s₅.mem (w64 (prmOf s).D)
      (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n else Spec.GcmSiv.zeros (prmOf s).n)
      (by rw [hl]; omega_using [hn])
    rwa [hl] at e
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12) = dk at ax hdec md hD₅
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
        (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) =
      bytesAt s.mem (w64 (prmOf s).T) 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax, ite_eq_left (decide_eq_true hc.symm)]; rfl
    · rw [hm, md, mD, hD₅, ite_eq_left (decide_eq_true hc.symm)]
  · have hc' : ¬bytesAt s.mem (w64 (prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (w64 (prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) :=
      Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax, ite_eq_right (fun h => hc' (of_decide_eq_true h))]; rfl
    · rw [hm, md, mD, ite_eq_right (fun h => hc' (of_decide_eq_true h))]

end VG.Proof.AesGcmSiv.X86
