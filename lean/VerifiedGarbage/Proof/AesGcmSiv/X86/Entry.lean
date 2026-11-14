module
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.GcmSiv
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Env
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

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
