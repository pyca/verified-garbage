import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Frame
import VerifiedGarbage.Proof.CmacAes.Arm.Verified
import VerifiedGarbage.Impl.AesSiv.Arm
import VerifiedGarbage.Proof.AesCcm.Arm.Frame
import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.AesGcm.Arm.Frame
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Call`. -/
section

/-!
# AES-SIV on ARMv7: the calls of `vg_cmac_aes_finalize`

Untrusted: everything here is checked by Lean. As streaming AES-CMAC's
(`Proof/CmacAes/Stream/Arm/Call.lean`, `fin_call`, `fin_rel`), but with the
two stack arguments pushed from `r12` (`last_len`) and `lr` (the working
space), which `encrypt` and `decrypt` do not keep across calls: what a call
needs (`FArgs`), what it leaves (`FPost`), and that two calls with the same
arguments leak the same (`fin_rel`). The calls of `vg_cmac_aes_update` are
AES-CCM's (`Proof.AesCcm.Arm.upd_call`, `upd_rel`), and those of
`vg_aes_ctr32` AES-GCM's (`Proof.AesGcm.Arm.ctr_call`, `ctr_rel`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm
open VG.Proof.CmacAes.Stream.Arm (view blw16 view_gpr view_sp view_arg0 view_arg1 view_argAddr view_blw spA
  slot_sub push_frame cov_push covW_push WP.frameCallF RelCT.frameCall stackUse_finalize fRd fWr)
open VG.Proof.CmacAes.Arm (toNat_rounds)

structure FArgs (s : State) (K St P S : BitVec 32) (L R : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = St
  r3 : s.gpr .r3 = P
  r12 : s.gpr .r12 = BitVec.ofNat 32 L
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  hsp : 16 ≤ s.sp.toNat
  kst : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ks : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  pst : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ps : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  sts : (⟨State.addr St, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bk : (blw16 s).Disjoint ⟨State.addr K, 272⟩
  bp : (blw16 s).Disjoint ⟨State.addr P, L⟩
  bst : (blw16 s).Disjoint ⟨State.addr St, 16⟩
  bs : (blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fK : K.toNat + 272 ≤ 2 ^ 32
  fSt : St.toNat + 16 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩, blw16 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr St) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 240) 16)
        (Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 256) 16) (Spec.Aes.bytesAt s.mem (State.addr P) L))
        (Spec.Aes.bytesAt s.mem (State.addr St) 16))

theorem FArgs.pre {s : State} {K St P S : BitVec 32} {L R : Nat} (h : VG.Proof.AesSiv.Arm.FArgs s K St P S L R) :
    Proof.CmacAes.Arm.finalizeArm.pre (view .r12 .lr s (fRd s K P L) (fWr St S)) := by
  have hR := VG.Proof.CmacAes.Arm.toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  have hb := view_blw (ra := .r12) (rb := .lr) (rd := fRd s K P L) (wr := fWr St S) h.hsp
  simp only [Proof.CmacAes.Arm.finalizeArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, hR, hL, State.withRegions_rd, State.withRegions_wr]
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, (h.bst.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm,
    (h.bs.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm, h.bk.sub_left hb, h.bp.sub_left hb, h.bst.sub_left hb, h.bs.sub_left hb,
    h.fK, h.fSt, h.fP, h.fS, ?_, ?_, h.rounds, h.len⟩
  · rw [VG.Proof.CmacAes.Stream.Arm.view_sp, hspv]; omega
  · rw [VG.Proof.CmacAes.Stream.Arm.view_sp, hspv]; have := s.sp.isLt; omega

theorem fin_call {s : State} {K St P S : BitVec 32} {L R : Nat} (h : VG.Proof.AesSiv.Arm.FArgs s K St P S L R) :
    WP isa Impl.AesSiv.Arm.finFrame s (VG.Proof.AesSiv.Arm.FPost s K St P S L R) := by
  have hR := VG.Proof.CmacAes.Arm.toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.finalizeRawArm) (fun _ hs => Proof.CmacAes.Arm.finalize_raw_wp hs)
    stackUse_finalize rfl h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bst
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := push_frame h.hsp .r12 .lr
  have keep : ∀ {p : Addr} {k : Nat}, (blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left VG.Proof.CmacAes.Stream.Arm.slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h' | h' | h' <;> omega
  simp only [Proof.CmacAes.Arm.finalizeRawArm, Proof.CmacAes.Arm.finalizeRaw, Proof.CmacAes.Arm.mn,
    Proof.CmacAes.Arm.ciph, Proof.CmacAes.Arm.ciphAt, Proof.CmacAes.Arm.W, Proof.CmacAes.Arm.R,
    Proof.CmacAes.Arm.St, Proof.CmacAes.Arm.Dp, Proof.CmacAes.Arm.N, view_arg0 h.hsp,
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, hR, hL, State.withRegions_mem, State.callEntry_mem] at hpost
  have eK := keep (h.bk.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK1 : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 240) 16 =
      Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 240) 16 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 256) 16 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := keep h.bst (by decide)
  have eP := keep h.bp (by have := h.len; omega)
  rw [eK, eK1, eK2, eSt, eP] at hpost
  rw [hm]
  exact hpost

theorem fin_rel {K St P S sp₀ : BitVec 32} {L R : Nat} {Pr : State → State → Prop}
    (h : ∀ s₁ s₂, Pr s₁ s₂ → VG.Proof.AesSiv.Arm.FArgs s₁ K St P S L R ∧ VG.Proof.AesSiv.Arm.FArgs s₂ K St P S L R ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa Pr Impl.AesSiv.Arm.finFrame fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.finalizeArm) (rd := [⟨State.addr K, 272⟩,
    ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := fWr St S)
    (fun _ hs => Proof.CmacAes.Arm.finalize_wp hs) Proof.CmacAes.Arm.finalize_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : fRd s₁ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [fRd, e₁]
  have r₂ : fRd s₂ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [fRd, e₂]
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
  simp only [Proof.CmacAes.Arm.finalizeArm, VG.Proof.CmacAes.Stream.Arm.view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, VG.Proof.CmacAes.Stream.Arm.view_gpr .r0 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r1 (by decide), VG.Proof.CmacAes.Stream.Arm.view_gpr .r2 (by decide),
    VG.Proof.CmacAes.Stream.Arm.view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12,
    h₂.lr, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Env`. -/
section

/-!
# AES-SIV on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The key context (512 bytes
at `c`), the working space (2576 bytes at `w`) and the 16 bytes of stack
below `sp` that the calls use (`Lay`), all 32-bit pointers; what a state may
access (`Perm`); and the registers holding the rounds, `c` and `w`, and the
stack pointer (`Env`). The strings S2V absorbs are buffers the code may read
(`Buf`), and the data one it may also write (`Dat`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (covers_off in_off in_left covers_left covers_of_mem covers_prefix)
open VG.Proof.AesCcm.Arm (blw)

theorem blw16_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) : Proof.CmacAes.Stream.Arm.blw16 s = blw sp := by
  subst h; rfl

/-- The working space of the functions called. -/
abbrev scrR (w : BitVec 32) : Region := ⟨State.addr w + BitVec.ofNat 64 256, 2176⟩

/-- The key context, `W` and the stack below `sp` used by the calls. -/
structure Lay (c w sp : BitVec 32) : Prop where
  cw : c.toNat + 512 ≤ 2 ^ 32
  ww : w.toNat + 2576 ≤ 2 ^ 32
  sp16 : 16 ≤ sp.toNat
  c_w : (⟨State.addr c, 512⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  stk_c : (blw sp).Disjoint ⟨State.addr c, 512⟩
  stk_w : (blw sp).Disjoint ⟨State.addr w, 2576⟩

/-- What a state may access. -/
structure Perm (c w : BitVec 32) (s : State) : Prop where
  c : Covers [⟨State.addr c, 512⟩] (s.rd ++ s.wr)
  w : Covers [⟨State.addr w, 2576⟩] s.wr

/-- The registers holding the rounds `R`, the key context and `W`, the stack
pointer, and what the state may access. -/
structure Env (c w sp : BitVec 32) (R : Nat) (s : State) : Prop where
  r9 : s.gpr .r9 = BitVec.ofNat 32 R
  r10 : s.gpr .r10 = c
  r11 : s.gpr .r11 = w
  sp : s.sp = sp
  perm : VG.Proof.AesSiv.Arm.Perm c w s

theorem Perm.of_eq {c w : BitVec 32} {s s' : State} (h : VG.Proof.AesSiv.Arm.Perm c w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.Perm c w s' := ⟨by rw [hrd, hwr]; exact h.c, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r9`–`r11`, `sp` and the permissions. -/
theorem Env.keep {c w sp : BitVec 32} {R : Nat} {s s' : State} (h : VG.Proof.AesSiv.Arm.Env c w sp R s)
    (hg : ∀ r ∈ [Reg.r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.Env c w sp R s' :=
  ⟨by rw [hg _ (by simp), h.r9], by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- After code that keeps the callee-saved registers (but `lr`). -/
theorem Env.of_saved {c w sp : BitVec 32} {R : Nat} {s s' : State} (h : VG.Proof.AesSiv.Arm.Env c w sp R s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.Env c w sp R s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2576) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2576⟩ :=
  Offset.sub_base _ h

theorem cSub {C : Addr} {d n : Nat} (h : d + n ≤ 512) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base _ h

variable {c w sp : BitVec 32} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 2576) : State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

/-- An offset into the context, as a 64-bit address. -/
theorem cA {d : Nat} (hd : d < 512) : State.addr (c + BitVec.ofNat 32 d) = State.addr c + BitVec.ofNat 64 d :=
  addr_add (by have := L.cw; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d m : Nat} (h : a + n ≤ d ∨ d + m ≤ a) (ha : a + n ≤ 2576) (hd : d + m ≤ 2576) :
    (⟨State.addr w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, m⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem wN {d : Nat} (hd : d < 2576) : (w + BitVec.ofNat 32 d).toNat = w.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem cN {d : Nat} (hd : d < 512) : (c + BitVec.ofNat 32 d).toNat = c.toNat + d := by
  have := L.cw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2576) : (blw sp).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (VG.Proof.AesSiv.Arm.Lay.wSub ha)

theorem stk_c' {a n : Nat} (ha : a + n ≤ 512) : (blw sp).Disjoint ⟨State.addr c + BitVec.ofNat 64 a, n⟩ :=
  L.stk_c.sub_right (VG.Proof.AesSiv.Arm.Lay.cSub ha)

theorem c_w' {a n b m : Nat} (ha : a + n ≤ 512) (hb : b + m ≤ 2576) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 b, m⟩ :=
  (L.c_w.sub_left (VG.Proof.AesSiv.Arm.Lay.cSub ha)).sub_right (VG.Proof.AesSiv.Arm.Lay.wSub hb)

theorem c0_w' {n b m : Nat} (ha : n ≤ 512) (hb : b + m ≤ 2576) :
    (⟨State.addr c, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 b, m⟩ :=
  (L.c_w.sub_left (Region.sub_prefix ha)).sub_right (VG.Proof.AesSiv.Arm.Lay.wSub hb)

end Lay

namespace Perm

variable {c w : BitVec 32} {s : State} (P : VG.Proof.AesSiv.Arm.Perm c w s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2576) : InRegions s.wr (State.addr w + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2576) : InRegions (s.rd ++ s.wr) (State.addr w + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2576) : Covers [⟨State.addr w + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem cR {d n : Nat} (h : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (State.addr c + BitVec.ofNat 64 d) n :=
  in_off P.c h (by decide)

theorem cC {d n : Nat} (h : d + n ≤ 512) : Covers [⟨State.addr c + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.c h (by decide)

theorem c0C {n : Nat} (h : n ≤ 512) : Covers [⟨State.addr c, n⟩] (s.rd ++ s.wr) := covers_prefix P.c h

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at the 32-bit pointer `D` that the code may read,
apart from `W` and the stack below `sp`. -/
structure Buf (w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr)
  fit : D.toNat + n ≤ 2 ^ 32
  w : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  stk : (blw sp).Disjoint ⟨State.addr D, n⟩

namespace Buf

variable {w sp : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesSiv.Arm.Buf w sp s D n)
include h

theorem lt32 : n ≤ 2 ^ 32 := by have := h.fit; omega

theorem lt : n < 2 ^ 64 := by have := h.fit; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.Buf w sp s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- Byte `j` of the buffer, for `j < n`, as a 64-bit address. -/
theorem addr {j : Nat} (hj : j < n) : State.addr (D + BitVec.ofNat 32 j) = State.addr D + BitVec.ofNat 64 j :=
  addr_add (by have := h.fit; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesSiv.Arm.Buf w sp s D k where
  rd := covers_prefix h.rd hk
  fit := by have := h.fit; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : VG.Proof.AesSiv.Arm.Buf w sp s (D + BitVec.ofNat 32 j) k := by
  have ha := h.addr (j := j) (by omega)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]; exact covers_off h.rd hjk h.lt
  · rw [h.toNat_add (by omega)]; have := h.fit; omega
  · rw [ha]; exact h.w.sub_left hs
  · rw [ha]; exact h.stk.sub_right hs

end Buf

/-- The data: `n` bytes at `D` that the code may write, apart from `W`, the
key context and the stack below `sp`. -/
structure Dat (c w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  buf : VG.Proof.AesSiv.Arm.Buf w sp s D n
  wr : Covers [⟨State.addr D, n⟩] s.wr
  c : (⟨State.addr c, 512⟩ : Region).Disjoint ⟨State.addr D, n⟩

theorem Dat.of_eq {c w sp : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesSiv.Arm.Dat c w sp s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.Dat c w sp s' D n :=
  ⟨h.buf.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.c⟩

/-! ## The context's functions outside a frame -/

/-- The PRF and the cipher of a key context outside a frame's regions. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega),
    Proof.Cmac.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.Cmac.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

theorem rounds_le {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : 16 * (R + 1) ≤ 240 := by
  rcases hR with rfl | rfl | rfl <;> decide

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.CmacOf`. -/
section

/-!
# AES-SIV on ARMv7: the CMAC of a string (`cmacOf`)

Untrusted: everything here is checked by Lean. `cmacOf` computes the CMAC
of the string with the context's PRF into the state at `W + 176`: the code
zeroes the state, computes `16 nb`, the bytes of the whole blocks before the
last 1 to 16 (`Spec.Cmac.chainedLen`), into `r4`, chains the `nb` blocks
with `vg_cmac_aes_update` and finalizes the rest with
`vg_cmac_aes_finalize`, from the subkeys in the context
(`Siv.cmacWith_chained`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.AesGcm.Arm (Keeps covers_cons covers_left shr4 toNat32 ofNat_sub32 z_cmp
  eval_eq' z_subFlags gpr_subFlags covers_off bytesAt_frame)
open VG.Proof.AesCcm.Arm (blw UArgs UPost upd_call)
open VG.Proof.CmacAes.Arm (zeroBlk zeroBlk_ok)
open VG.Proof.CmacAes.Stream.Arm (blw16)
open VG.Proof.MdStream.Arm (wp_mov op2_imm)

theorem zero16_eq (d : Nat) : zero16 d = .mov .r12 (imm 0) :: zeroBlk .r12 .r11 d := rfl

/-! ## Lengths -/

theorem chainedLen_le (n : Nat) : Spec.Cmac.chainedLen 16 n ≤ n := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_rest (n : Nat) : n - Spec.Cmac.chainedLen 16 n ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_div (n : Nat) : 16 * (Spec.Cmac.chainedLen 16 n / 16) = Spec.Cmac.chainedLen 16 n := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_zero : Spec.Cmac.chainedLen 16 0 = 0 := rfl

theorem chainedLen_pos {n : Nat} (_h : n ≠ 0) : Spec.Cmac.chainedLen 16 n = 16 * ((n - 1) / 16) := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_ne {n : Nat} (h : n ≠ 0) : 0 < n - Spec.Cmac.chainedLen 16 n := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem shl4 {n : Nat} (hn : 16 * n < 2 ^ 32) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- What the CMAC of a string writes: the state at `W + 176`, the working
space of the functions called and the stack below `sp`. -/
abbrev macR (w sp : BitVec 32) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 stOff, 16⟩, VG.Proof.AesSiv.Arm.scrR w, blw sp]

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-! ## The calls' arguments -/

/-- A call of `vg_cmac_aes_update` with the context's key schedule, the
state at `W + st`, `n` blocks at `D` and the working space at `W + 256`. -/
theorem uargs_of {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {st : Nat}
    (hst : st + 16 ≤ 256) {D : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) (fD : D.toNat + 16 * n ≤ 2 ^ 32)
    (dC : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 st, 16⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint (VG.Proof.AesSiv.Arm.scrR w))
    (dB : (blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (rD : Covers [⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr))
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 st)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 256) :
    UArgs s c (w + BitVec.ofNat 32 st) D (w + BitVec.ofNat 32 256) R n := by
  have eY := L.wA (d := st) (by omega)
  have eS := L.wA (d := 256) (by decide)
  have hb := VG.Proof.AesSiv.Arm.blw16_eq he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, hn, by rw [he.sp]; exact L.sp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by have := L.cw; omega, ?_, fD, ?_, covers_cons (he.perm.c0C (by decide)) rD, ?_⟩
  · rw [eY]; exact L.c0_w' (by decide) (by omega)
  · rw [eS]; exact L.c0_w' (by decide) (by decide)
  · rw [eY]; exact dC
  · rw [eS]; exact dS
  · rw [eY, eS]; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [hb]; exact L.stk_c.sub_right (Region.sub_prefix (by decide))
  · rw [hb]; exact dB
  · rw [hb, eY]; exact L.stk_w' (by omega)
  · rw [hb, eS]; exact L.stk_w' (by decide)
  · rw [L.wN (by omega)]; have := L.ww; omega
  · rw [L.wN (by decide)]; have := L.ww; omega
  · rw [eY, eS]; exact covers_cons (he.perm.wC (by omega)) (he.perm.wC (by decide))

/-- A call of `vg_cmac_aes_finalize` with the context as its key, the state
at `W + st`, the `n` last bytes at `D` and the working space at `W + 256`. -/
theorem fargs_of {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {st : Nat}
    (hst : st + 16 ≤ 256 ∨ (2432 ≤ st ∧ st + 16 ≤ 2576)) {D : BitVec 32} {n : Nat} (hn : n ≤ 16) (fD : D.toNat + n ≤ 2 ^ 32)
    (dC : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 st, 16⟩)
    (dS : (⟨State.addr D, n⟩ : Region).Disjoint (VG.Proof.AesSiv.Arm.scrR w))
    (dB : (blw sp).Disjoint ⟨State.addr D, n⟩) (rD : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr))
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 st)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 256) :
    VG.Proof.AesSiv.Arm.FArgs s c (w + BitVec.ofNat 32 st) D (w + BitVec.ofNat 32 256) n R := by
  have eY := L.wA (d := st) (by omega)
  have eS := L.wA (d := 256) (by decide)
  have hb := VG.Proof.AesSiv.Arm.blw16_eq he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, hn, by rw [he.sp]; exact L.sp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by have := L.cw; omega, ?_, fD, ?_, covers_cons (he.perm.c0C (by decide)) rD, ?_⟩
  · rw [eY]; exact L.c0_w' (by decide) (by omega)
  · rw [eS]; exact L.c0_w' (by decide) (by decide)
  · rw [eY]; exact dC
  · rw [eS]; exact dS
  · rw [eY, eS]; exact L.w_w (by omega) (by omega) (by decide)
  · rw [hb]; exact L.stk_c.sub_right (Region.sub_prefix (by decide))
  · rw [hb]; exact dB
  · rw [hb, eY]; exact L.stk_w' (by omega)
  · rw [hb, eS]; exact L.stk_w' (by decide)
  · rw [L.wN (by omega)]; have := L.ww; omega
  · rw [L.wN (by decide)]; have := L.ww; omega
  · rw [eY, eS]; exact covers_cons (he.perm.wC (by omega)) (he.perm.wC (by decide))

/-! ## Zeroing a block of `W` -/

theorem zero16_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) {d : Nat} (hd : d + 16 ≤ 2576) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 d) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (zero16 d ++ is)) s Q := by
  rw [VG.Proof.AesSiv.Arm.zero16_eq, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have h11 : s₁.gpr .r11 = w := by rw [u₁.other _ (by decide), he.r11]
  refine zeroBlk_ok (by rw [u₁.gpr]; rfl) (by omega) (by rw [h11]; have := L.ww; omega)
    (by rw [h11, u₁.wr]; exact he.perm.wC hd) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine k s₂ (fun r hr => by rw [g₂, u₁.other _ hr]) (by rw [m₂, h11, u₁.mem]) (by rw [rd₂, u₁.rd])
    (by rw [wr₂, u₁.wr]) (by rw [sp₂, u₁.sp])

/-! ## `cmacOf` -/

/-- `cmacPre`: the state zeroed, `16 nb` in `r4`, and the arguments of the
update. -/
theorem cmacPre_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32}
    {n : Nat} (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa (cmacPre stOff) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) ∧
      UArgs s' c (w + BitVec.ofNat 32 stOff) P (w + BitVec.ofNat 32 256) R (Spec.Cmac.chainedLen 16 n / 16) ∧
      s'.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 stOff) := by
  have hcl := VG.Proof.AesSiv.Arm.chainedLen_le n
  have hcd := VG.Proof.AesSiv.Arm.chainedLen_div n
  rw [cmacPre]
  refine WP.seq (VG.Proof.AesSiv.Arm.zero16_ok L he (d := stOff) (by decide) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_)
  -- `r4 := 0` and the comparison.
  obtain ⟨s₂, run₂, h4₂, hz₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.mov .r4 (imm 0), .cmp .r5 (imm 0)] s₁ = some s₂ ∧
      s₂.gpr .r4 = 0 ∧ s₂.z = decide (n = 0) ∧ (∀ r, r ≠ .r4 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide), h5]
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5₁]
      exact z_cmp hn (by decide)
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ : VG.Proof.AesSiv.Arm.Env c w sp R s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [g₂ _ (by decide), g₁ _ (by decide)])
    (by rw [k₂.sp, sp₁]) (by rw [k₂.rd, rd₁]) (by rw [k₂.wr, wr₁])
  have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n := by rw [g₂ _ (by decide), g₁ _ (by decide), h5]
  have h6₂ : s₂.gpr .r6 = P := by rw [g₂ _ (by decide), g₁ _ (by decide), h6]
  -- `r4 := 16 nb`, in both branches.
  have last : ∀ s₃ : State, VG.Proof.AesSiv.Arm.Env c w sp R s₃ → s₃.rd = s.rd → s₃.wr = s.wr →
      (∀ r, r ≠ .r4 → s₃.gpr r = s₂.gpr r) → s₃.mem = s₂.mem →
      s₃.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) →
      WP isa (.block (macArgs stOff ++ [mov .r3 .r6, .mov .r12 (.shifted .r4 .lsr 4)])) s₃ fun s' =>
        VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
        s'.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) ∧
        UArgs s' c (w + BitVec.ofNat 32 stOff) P (w + BitVec.ofNat 32 256) R (Spec.Cmac.chainedLen 16 n / 16) ∧
        s'.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 stOff) := by
    intro s₃ he₃ rd₃ wr₃ g₃ m₃ h4₃
    have h6₃ : s₃.gpr .r6 = P := by rw [g₃ _ (by decide), h6₂]
    refine WP.of_runBlock ⟨_, by simp only [macArgs, csOff, stOff, mov]; arun [he₃.r9, he₃.r10, he₃.r11], ?_⟩
    have hsh : BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) >>> 4 =
        BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n / 16) := VG.Proof.AesGcm.Arm.shr4 (by omega)
    have hq := hP.take hcl
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, rd₃, wr₃,
      fun r a b c' d e f g => by
        simp only [gpr_setReg, a, b, c', d, f, g, ite_false, reduceCtorEq, ne_eq, not_false_eq_true]
        rw [g₃ r e, g₂ r e, g₁ r f], by simp [gpr_setReg, h4₃], ?_, by simp [mem_setReg, m₃, k₂.mem, m₁]⟩
    refine VG.Proof.AesSiv.Arm.uargs_of L ?_ hR (st := stOff) (by decide)
      (n := Spec.Cmac.chainedLen 16 n / 16) (by omega) (by rw [hcd]; exact hq.fit) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [hcd]; exact hq.w.sub_right (Lay.wSub (by decide))
    · rw [hcd]; exact hq.w.sub_right (Lay.wSub (by decide))
    · rw [hcd]; exact hq.stk
    · rw [hcd]; simp only [rd_setReg, rd₃, wr_setReg, wr₃]; exact hq.rd
    · simp [gpr_setReg, he₃.r10]
    · simp [gpr_setReg, he₃.r9]
    · simp [gpr_setReg, he₃.r11]
    · simp [gpr_setReg, h6₃]
    · simp [gpr_setReg, h4₃, hsh]
    · simp [gpr_setReg, he₃.r11]
  by_cases h0 : n = 0
  · subst h0
    refine WP.seq (WP.ite true (eval_eq' (by rw [hz₂]; rfl)) (fun _ => WP.block_nil ?_) (fun h => by cases h))
    exact last s₂ he₂ (by rw [k₂.rd, rd₁]) (by rw [k₂.wr, wr₁]) (fun _ _ => rfl) rfl (by rw [h4₂]; rfl)
  · refine WP.seq (WP.ite false (eval_eq' (by rw [hz₂]; simp [h0])) (fun h => by cases h) fun _ => ?_)
    obtain ⟨s₃, run₃, h4₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.dp .sub .r4 .r5 (imm 1), .mov .r4 (.shifted .r4 .lsr 4),
        .mov .r4 (.shifted .r4 .lsl 4)] s₂ = some s₃ ∧
        s₃.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) ∧ (∀ r, r ≠ .r4 → s₃.gpr r = s₂.gpr r) ∧
        Keeps s₂ s₃ := by
      have e1 : BitVec.ofNat 32 n - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega) hn
      have e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := VG.Proof.AesGcm.Arm.shr4 (by omega)
      have e3 : BitVec.ofNat 32 ((n - 1) / 16) <<< 4 = BitVec.ofNat 32 (16 * ((n - 1) / 16)) := VG.Proof.AesSiv.Arm.shl4 (by omega)
      refine ⟨_, by arun [h5₂], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, h5₂]
        rw [show (BitVec.ofNat 32 1 : BitVec 32) = 1 from rfl] at e1
        rw [VG.Proof.AesSiv.Arm.chainedLen_pos h0, ← e3, ← e2, ← e1]
        rfl
      · intro r a; simp [gpr_setReg, a]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    exact last s₃ (he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr)
      (by rw [k₃.rd, k₂.rd, rd₁]) (by rw [k₃.wr, k₂.wr, wr₁]) g₃ k₃.mem h4₃

/-- `cmacMid`: the arguments of `vg_cmac_aes_finalize` for the last bytes. -/
theorem cmacMid_ok {s₂ : State} (he₂ : VG.Proof.AesSiv.Arm.Env c w sp R s₂) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hn : n < 2 ^ 32)
    (hq : VG.Proof.AesSiv.Arm.Buf w sp s₂ (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n))
    (h4₂ : s₂.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n)
    (h6₂ : s₂.gpr .r6 = P) :
    ∃ s₃, runBlock isa (cmacMid stOff) s₂ = some s₃ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₃ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ ∧
      VG.Proof.AesSiv.Arm.FArgs s₃ c (w + BitVec.ofNat 32 stOff) (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n))
        (w + BitVec.ofNat 32 256) (n - Spec.Cmac.chainedLen 16 n) R := by
  have hcl := VG.Proof.AesSiv.Arm.chainedLen_le n
  have hrest := VG.Proof.AesSiv.Arm.chainedLen_rest n
  refine ⟨_, by simp only [cmacMid, macArgs, csOff, stOff, mov]; arun [he₂.r9, he₂.r10, he₂.r11], ?_⟩
  have es : BitVec.ofNat 32 n - BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) =
      BitVec.ofNat 32 (n - Spec.Cmac.chainedLen 16 n) := ofNat_sub32 hcl hn
  refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine VG.Proof.AesSiv.Arm.fargs_of L ?_ hR (st := stOff) (by decide)
    (n := n - Spec.Cmac.chainedLen 16 n) hrest hq.fit ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · exact hq.w.sub_right (Lay.wSub (by decide))
  · exact hq.w.sub_right (Lay.wSub (by decide))
  · exact hq.stk
  · exact hq.rd
  · simp [gpr_setReg, he₂.r10]
  · simp [gpr_setReg, he₂.r9]
  · simp [gpr_setReg, he₂.r11]
  · simp [gpr_setReg, h6₂, h4₂]
  · simp [gpr_setReg, h5₂, h4₂, es]
  · simp [gpr_setReg, he₂.r11]

/-- `AES-CMAC(K1, S)` into the state at `W + 176`, for the string `S` (`n`
bytes at `P`, in `r6` and `r5`). -/
theorem cmacOf_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32}
    {n : Nat} (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa (cmacOf stOff) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (VG.Proof.AesSiv.Arm.macR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 stOff) 16 =
        Spec.Siv.ctxMac s.mem (State.addr c) R (bytesAt s.mem (State.addr P) n) := by
  have hcl := VG.Proof.AesSiv.Arm.chainedLen_le n
  have hcd := VG.Proof.AesSiv.Arm.chainedLen_div n
  have hrest := VG.Proof.AesSiv.Arm.chainedLen_rest n
  have eSt := L.wA (d := stOff) (by decide)
  have eS := L.wA (d := 256) (by decide)
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.cmacPre_ok L he hR hP hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, h4₁, U, m₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U) fun s₂ h₂ => ?_)
  have he₂ := he₁.of_saved h₂.saved h₂.sp h₂.rd h₂.wr
  have g₂ : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s₁.gpr r := h₂.saved
  have h4₂ : s₂.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) := by
    rw [g₂ _ (by decide) (by decide), h4₁]
  have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h5]
  have h6₂ : s₂.gpr .r6 = P := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h6]
  -- The arguments of the finalization.
  have hq : VG.Proof.AesSiv.Arm.Buf w sp s₂ (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
    by_cases h0 : n - Spec.Cmac.chainedLen 16 n = 0
    · have : n = 0 := by
        by_contra hne; have := VG.Proof.AesSiv.Arm.chainedLen_ne hne; omega
      subst this
      rw [VG.Proof.AesSiv.Arm.chainedLen_zero, show P + BitVec.ofNat 32 0 = P from BitVec.add_zero P]
      exact hP.of_eq (by rw [h₂.rd, rd₁]) (by rw [h₂.wr, wr₁])
    · exact (hP.sub (j := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega)
        (by omega)).of_eq (by rw [h₂.rd, rd₁]) (by rw [h₂.wr, wr₁])
  obtain ⟨s₃, run₃, he₃, g₃, k₃, F⟩ := VG.Proof.AesSiv.Arm.cmacMid_ok L he₂ hR hn hq h4₂ h5₂ h6₂
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.Arm.fin_call F) fun s₄ h₄ => ?_
  have he₄ := he₃.of_saved h₄.saved h₄.sp h₄.rd h₄.wr
  have hb₁ : blw16 s₁ = blw sp := VG.Proof.AesSiv.Arm.blw16_eq he₁.sp
  have hb₃ : blw16 s₃ = blw sp := VG.Proof.AesSiv.Arm.blw16_eq he₃.sp
  -- The memory: what each step writes.
  have f₁ : Frame (VG.Proof.AesSiv.Arm.macR w sp) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)
  have f₂ : Frame (VG.Proof.AesSiv.Arm.macR w sp) s₁.mem s₂.mem := by
    have := h₂.frame; rw [eSt, eS, hb₁] at this; exact this.mono (by simp)
  have f₄ : Frame (VG.Proof.AesSiv.Arm.macR w sp) s₃.mem s₄.mem := by
    have := h₄.frame; rw [eSt, eS, hb₃] at this; exact this.mono (by simp)
  have fT : Frame (VG.Proof.AesSiv.Arm.macR w sp) s.mem s₄.mem := f₁.trans (f₂.trans (by rw [← k₃.mem]; exact f₄))
  refine ⟨he₄, by rw [h₄.rd, k₃.rd, h₂.rd, rd₁], by rw [h₄.wr, k₃.wr, h₂.wr, wr₁], fun r hr h4 hlr => ?_, fT, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₄.saved r hr hlr, g₃ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr, h₂.saved r hr hlr,
      g₁ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 a.2.2.2.2 hlr]
  -- What the calls read is as on entry.
  have dc : ∀ r ∈ VG.Proof.AesSiv.Arm.macR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  have dp : ∀ r ∈ VG.Proof.AesSiv.Arm.macR w sp, (⟨State.addr P, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
  have f₁₂ := f₁.trans f₂
  have hlt := hP.lt
  have cK {d k : Nat} (hd : d + k ≤ 512) {m' : Mem} (hf : Frame (VG.Proof.AesSiv.Arm.macR w sp) s.mem m') :
      bytesAt m' (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (fun r hr => (dc r hr).sub_left (Lay.cSub hd)) (by omega)
  have cP {d k : Nat} (hd : d + k ≤ n) {m' : Mem} (hf : Frame (VG.Proof.AesSiv.Arm.macR w sp) s.mem m') :
      bytesAt m' (State.addr P + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr P + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (fun r hr => (dp r hr).sub_left (Offset.sub_base _ hd)) (by omega)
  have k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  have sch₁ := cK (d := 0) (k := 16 * (R + 1)) (by omega) f₁
  have sch₃ := cK (d := 0) (k := 16 * (R + 1)) (by omega) f₁₂
  have k1 := cK (d := 240) (k := 16) (by decide) f₁₂
  have k2 := cK (d := 256) (k := 16) (by decide) f₁₂
  have pre₁ := cP (d := 0) (k := Spec.Cmac.chainedLen 16 n) (by omega) f₁
  have rest₃ := cP (d := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega) f₁₂
  rw [k0] at sch₁ sch₃ pre₁
  have eP : State.addr (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) =
      State.addr P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) := by
    by_cases h0 : n = 0
    · subst h0; rw [VG.Proof.AesSiv.Arm.chainedLen_zero]; exact addr_add (by have := P.isLt; omega)
    · exact addr_add (by have := hP.fit; have := VG.Proof.AesSiv.Arm.chainedLen_ne h0; omega)
  have hz : bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 stOff) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero4_bytes]
  have hS : (bytesAt s.mem (State.addr P) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hsplit : n = Spec.Cmac.chainedLen 16 n + (n - Spec.Cmac.chainedLen 16 n) := by omega
  have tk : (bytesAt s.mem (State.addr P) n).take (Spec.Cmac.chainedLen 16 n) =
      bytesAt s.mem (State.addr P) (Spec.Cmac.chainedLen 16 n) := by
    have := take_bytesAt s.mem (State.addr P) (a := Spec.Cmac.chainedLen 16 n)
      (b := n - Spec.Cmac.chainedLen 16 n)
    rwa [← hsplit] at this
  have dr : (bytesAt s.mem (State.addr P) n).drop (Spec.Cmac.chainedLen 16 n) =
      bytesAt s.mem (State.addr P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
    have := drop_bytesAt s.mem (State.addr P) (a := Spec.Cmac.chainedLen 16 n)
      (b := n - Spec.Cmac.chainedLen 16 n)
    rwa [← hsplit] at this
  have out₂ := h₂.out
  rw [eSt] at out₂
  have out₄ := h₄.out
  rw [eSt, eP, k₃.mem, sch₃, k1, k2, rest₃, out₂, sch₁, hz, Proof.Cmac.Stream.blocksAt_eq, hcd, pre₁] at out₄
  rw [out₄, Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS, tk, dr, Proof.Cmac.xor_comm]
  rfl

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.S2vAd`. -/
section

/-!
# AES-SIV on ARMv7: a step of S2V over the associated data

Untrusted: everything here is checked by Lean. After the CMAC of a
component into the state at `W + 176` (`cmacOf_ok`), the code doubles `D`
(at `W + 2560`) in place and XORs the CMAC into it, so `D` is then
`dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (ofNat_sub32 z_cmp gpr_subFlags z_subFlags bytesAt_frame covers_left mem_subFlags rd_subFlags wr_subFlags sp_subFlags)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok dbl_wp dblMem dblMem_bytes dblMem_frame)
open VG.Proof.MdStream.Arm (wp_mov op2_reg)

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) : xor4 pb qb cb pd qd cd = xorBlk .r12 .lr pb qb cb pd qd cd :=
  rfl

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it, then the
descriptor pointer advanced by 8 and the count decremented, `Z` set when
none are left. -/
theorem adStep_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) {a : BitVec 32} {k : Nat} (hk : 0 < k) (hk32 : k < 2 ^ 32)
    (h8 : s.gpr .r8 = a) (h7 : s.gpr .r7 = BitVec.ofNat 32 k) :
    WP isa (.block adStep) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 →
        r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r8 = a + BitVec.ofNat 32 8 ∧ s'.gpr .r7 = BitVec.ofNat 32 (k - 1) ∧ s'.z = decide (k - 1 = 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
        Spec.Siv.xor (Spec.Siv.dbl (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16))
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 stOff) 16) := by
  have ww := L.ww
  rw [adStep, List.cons_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h6₁ : s₁.gpr .r6 = w := by rw [u₁.gpr, he.r11]
  simp only [List.append_eq, List.append_assoc]
  refine dbl_wp (K := w) h6₁ (src := dOff) (dst := dOff) (by decide) (by decide) (by omega) (by omega)
    (by rw [u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [u₁.wr]; exact he.perm.wC (by decide)) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have h11₂ : s₂.gpr .r11 = w := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide),
      he.r11]
  rw [VG.Proof.AesSiv.Arm.xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h11₂]; simp only [dOff]; omega)
    (by rw [h11₂]; simp only [stOff]; omega) (by rw [h11₂]; simp only [dOff]; omega)
    (by rw [h11₂, rd₂, wr₂, u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₂, rd₂, wr₂, u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₂, wr₂, u₁.wr]; exact he.perm.wC (by decide)) fun s₃ g₃ => ?_
  have h7₃ : s₃.gpr .r7 = BitVec.ofNat 32 k := by
    rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), u₁.other _ (by decide), h7]
  have h8₃ : s₃.gpr .r8 = a := by
    rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), u₁.other _ (by decide), h8]
  have e1 : BitVec.ofNat 32 k - BitVec.ofNat 32 1 = BitVec.ofNat 32 (k - 1) := ofNat_sub32 (by omega) hk32
  refine WP.of_runBlock ⟨_, by arun [h7₃, h8₃], ?_⟩
  have dD : (⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 stOff, 16⟩ := L.w_w (.inr (by decide)) (by decide) (by decide)
  refine ⟨he.keep (fun r hr => ?_) (by simp [sp_setReg, g₃.sp, sp₂, u₁.sp])
      (by simp [rd_setReg, g₃.rd, rd₂, u₁.rd]) (by simp [wr_setReg, g₃.wr, wr₂, u₁.wr]),
    by simp [rd_setReg, g₃.rd, rd₂, u₁.rd], by simp [wr_setReg, g₃.wr, wr₂, u₁.wr], fun r a0 a1 a2 a3 a4 a6 a7 a8 a12 alr => ?_,
    by simp [gpr_setReg, h8₃], by simp [gpr_setReg, h7₃, e1], ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp [gpr_setReg, g₃.gpr _ (by decide : Reg.r9 ≠ .r12) (by decide), g₃.gpr _ (by decide : Reg.r10 ≠ .r12) (by decide),
        g₃.gpr _ (by decide : Reg.r11 ≠ .r12) (by decide), g₂, u₁.other]
  · simp only [gpr_setReg, gpr_subFlags, a7, a8, ite_false, reduceCtorEq]
    rw [g₃.gpr r a12 alr, g₂ r a0 a1 a2 a3 a4 a12, u₁.other r a6]
  · simp only [z_setReg, z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h7₃]
    rw [z_cmp hk32 (by decide)]
    simp only [decide_eq_decide]; omega
  · simp only [mem_setReg, mem_subFlags, g₃.mem, m₂, u₁.mem, h11₂]
    exact (dblMem_frame _ _ _ _).trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
  · simp only [mem_setReg, mem_subFlags, g₃.mem, m₂, u₁.mem, h11₂]
    rw [Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dD), dblMem_bytes,
      bytesAt_frame (dblMem_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD.symm) (by decide)]
    rfl

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.S2vLoop`. -/
section

/-!
# AES-SIV on ARMv7: S2V over the components of associated data

Untrusted: everything here is checked by Lean. The `N` descriptors at `a`
(8 bytes each: a 32-bit address and a 32-bit length) list the components
in the memory on entry `m₀` (`Ads`). Each iteration of `s2vAds` loads the
next descriptor (`adNext`), computes the CMAC of its component into the
state at `W + 176` (`cmacOf_ok`) and folds it into `D` (`adStep_ok`), so
`D` is S2V's state of the components so far (`AInv`, `aStep_ok`), and of all
of them after the loop (`s2vAds_ok`). The code writes only within `W` but its
first 16 bytes (the synthetic IV) and our caller's saved registers, and the
stack below `sp` (`wR`); S2V's end also writes its result (`oR`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (ofNat_sub32 z_cmp gpr_subFlags z_subFlags bytesAt_frame covers_left covers_off
  add32_ofNat_assoc eval_eq' eval_ne' Keeps in_off)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.MdStream.Arm (wp_ldr)

/-- What the code writes: `W` but the synthetic IV (at `W`) and our caller's
saved registers (at `W + 128`), and the stack below `sp`. -/
abbrev wR (w sp : BitVec 32) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 16, 112⟩, ⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, blw sp]

/-- What S2V's end writes: `wR` and its result at `W + out`. -/
abbrev oR (w sp : BitVec 32) (out : Nat) : List Region :=
  ⟨State.addr w + BitVec.ofNat 64 out, 16⟩ :: VG.Proof.AesSiv.Arm.wR w sp

theorem frame_oR {w sp : BitVec 32} {m m' : Mem} (out : Nat) (h : Frame (VG.Proof.AesSiv.Arm.wR w sp) m m') :
    Frame (VG.Proof.AesSiv.Arm.oR w sp out) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

/-- With the result at `W + tOff`, S2V's end writes within `wR`. -/
theorem frame_oR_tOff {w sp : BitVec 32} {m m' : Mem} (h : Frame (VG.Proof.AesSiv.Arm.oR w sp tOff) m m') : Frame (VG.Proof.AesSiv.Arm.wR w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, fun _ h => h⟩
    · exact ⟨blw sp, by simp, fun _ h => h⟩

/-- Word `j` (0: the address, 1: the length) of descriptor `i` at `a`, in `m`. -/
abbrev descW (m : Mem) (a : BitVec 32) (i j : Nat) : BitVec 32 :=
  m.readW (State.addr a + BitVec.ofNat 64 (8 * i + 4 * j)) 32

/-- The `N` descriptors at `a`, readable apart from `W` and the stack, and
the components they list in `m₀`, each a buffer the code may read. -/
structure Ads (w sp a : BitVec 32) (N : Nat) (m₀ : Mem) (s : State) : Prop where
  desc : Covers [⟨State.addr a, 8 * N⟩] (s.rd ++ s.wr)
  fit : a.toNat + 8 * N ≤ 2 ^ 32
  dw : (⟨State.addr a, 8 * N⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  ds : (blw sp).Disjoint ⟨State.addr a, 8 * N⟩
  comp : ∀ i < N, VG.Proof.AesSiv.Arm.Buf w sp s (VG.Proof.AesSiv.Arm.descW m₀ a i 0) (VG.Proof.AesSiv.Arm.descW m₀ a i 1).toNat

theorem Ads.of_eq {w sp a : BitVec 32} {N : Nat} {m₀ : Mem} {s s' : State} (h : VG.Proof.AesSiv.Arm.Ads w sp a N m₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.Ads w sp a N m₀ s' :=
  { h with desc := by rw [hrd, hwr]; exact h.desc, comp := fun i hi => (h.comp i hi).of_eq hrd hwr }

/-- The `i`-th component, `i < N`. -/
theorem components_getElem (m : Mem) (a : BitVec 32) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 32 m (State.addr a) N)[i]'(by simp [Spec.Siv.components, Sig.listed, hi]) =
      bytesAt m (State.addr (VG.Proof.AesSiv.Arm.descW m a i 0)) (VG.Proof.AesSiv.Arm.descW m a i 1).toNat := by
  simp only [Spec.Siv.components, Sig.listed, List.getElem_map, List.getElem_range, Elem.size, Nat.mul_one,
    VG.Proof.AesSiv.Arm.descW, State.addr]
  rw [show i * (2 * (32 / 8)) = 8 * i + 4 * 0 by omega, show (32 / 8 : Nat) = 4 from rfl, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, show 8 * i + 4 * 0 + 4 = 8 * i + 4 by omega]

theorem length_components (m : Mem) (p : Addr) (N : Nat) : (Spec.Siv.components 32 m p N).length = N := by
  simp [Spec.Siv.components, Sig.listed]

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-- Before the `i`-th component (and, for `i = N`, after the last): `D` is
S2V's state of the first `i`, `r8` and `r7` the next descriptor's address
and how many are left. -/
structure AInv (c w sp a : BitVec 32) (R N : Nat) (m₀ : Mem) (σ : State) (i : Nat) (s : State) : Prop where
  env : VG.Proof.AesSiv.Arm.Env c w sp R s
  ads : VG.Proof.AesSiv.Arm.Ads w sp a N m₀ s
  r8 : s.gpr .r8 = a + BitVec.ofNat 32 (8 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (N - i)
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame (VG.Proof.AesSiv.Arm.wR w sp) m₀ s.mem
  acc : bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac m₀ (State.addr c) R) ((Spec.Siv.components 32 m₀ (State.addr a) N).take i)

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

omit L in
theorem macR_wR : ∀ r ∈ VG.Proof.AesSiv.Arm.macR w sp, ∃ r' ∈ VG.Proof.AesSiv.Arm.wR w sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨blw sp, by simp, fun _ h => h⟩

omit L in
theorem dD_wR : ∀ r ∈ [(⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region)], ∃ r' ∈ VG.Proof.AesSiv.Arm.wR w sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

omit L in
/-- A region apart from `W` and the stack below `sp` is apart from `wR`. -/
theorem dis_wR {r : Region} (hw : r.Disjoint ⟨State.addr w, 2576⟩) (hs : (blw sp).Disjoint r) :
    ∀ r' ∈ VG.Proof.AesSiv.Arm.wR w sp, r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm

omit L in
/-- `adNext`: the address and the length of descriptor `i`'s component in
`r6` and `r5`. -/
theorem adNext_ok {m₀ : Mem} {a : BitVec 32} {N i : Nat} {s : State} (hA : VG.Proof.AesSiv.Arm.Ads w sp a N m₀ s) (hi : i < N)
    (hf : Frame (VG.Proof.AesSiv.Arm.wR w sp) m₀ s.mem) (h8 : s.gpr .r8 = a + BitVec.ofNat 32 (8 * i)) :
    WP isa (.block adNext) s fun s' => s'.gpr .r6 = VG.Proof.AesSiv.Arm.descW m₀ a i 0 ∧ s'.gpr .r5 = VG.Proof.AesSiv.Arm.descW m₀ a i 1 ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have fit := hA.fit
  have word {j : Nat} (hj : j < 2) :
      State.addr (s.gpr .r8 + BitVec.ofNat 32 (4 * j)) = State.addr a + BitVec.ofNat 64 (8 * i + 4 * j) ∧
      InRegions (s.rd ++ s.wr) (State.addr a + BitVec.ofNat 64 (8 * i + 4 * j)) 4 ∧
      s.mem.readW (State.addr a + BitVec.ofNat 64 (8 * i + 4 * j)) 32 = VG.Proof.AesSiv.Arm.descW m₀ a i j := by
    refine ⟨by rw [h8, add32_ofNat_assoc]; exact addr_add (by omega),
      in_off hA.desc (by omega) (by omega), ?_⟩
    exact hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (VG.Proof.AesSiv.Arm.dis_wR (w := w) (sp := sp) (hA.dw.sub_left (Offset.sub_base _ (by omega)))
        (hA.ds.sub_right (Offset.sub_base _ (by omega)))) (by decide)
  obtain ⟨a₀, i₀, v₀⟩ := word (j := 0) (by decide)
  obtain ⟨a₁, i₁, v₁⟩ := word (j := 1) (by decide)
  simp only [Nat.mul_zero, Nat.mul_one] at a₀ i₀ v₀ a₁ i₁ v₁
  rw [show BitVec.ofNat 32 0 = (0 : BitVec 32) from rfl] at a₀
  simp only [adNext]
  refine wp_ldr (a := State.addr a + BitVec.ofNat 64 (8 * i + 0)) (by decide) a₀ i₀ fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr a + BitVec.ofNat 64 (8 * i + 4)) (by decide)
    (by rw [u₁.other _ (by decide)]; exact a₁) (by rw [u₁.rd, u₁.wr]; exact i₁) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨by rw [u₂.other _ (by decide), u₁.gpr, v₀], by rw [u₂.gpr, u₁.mem, v₁],
    fun r h5 h6 => by rw [u₂.other _ h5, u₁.other _ h6], ⟨by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩⟩

/-- One iteration of the loop, for the component `i < N`. -/
theorem aStep_ok (hR : R = 10 ∨ R = 12 ∨ R = 14) {a : BitVec 32} {N : Nat} {m₀ : Mem} {σ : State} {i : Nat}
    {s : State} (h : VG.Proof.AesSiv.Arm.AInv c w sp a R N m₀ σ i s) (hi : i < N) :
    WP isa (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) s fun s' =>
      VG.Proof.AesSiv.Arm.AInv c w sp a R N m₀ σ (i + 1) s' ∧ s'.z = decide (N - (i + 1) = 0) := by
  have fit := h.ads.fit
  have hN32 : N - i < 2 ^ 32 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.adNext_ok h.ads hi h.frame h.r8) fun s₁ ⟨h6₁, h5₁, g₁, k₁⟩ => ?_)
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := h.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hP : VG.Proof.AesSiv.Arm.Buf w sp s₁ (VG.Proof.AesSiv.Arm.descW m₀ a i 0) (VG.Proof.AesSiv.Arm.descW m₀ a i 1).toNat := (h.ads.comp i hi).of_eq k₁.rd k₁.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.cmacOf_ok L he₁ hR hP (BitVec.isLt _) h6₁ (by rw [h5₁, BitVec.ofNat_toNat,
                        BitVec.setWidth_eq])) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, out₂⟩ => ?_)
  have h8₂ : s₂.gpr .r8 = a + BitVec.ofNat 32 (8 * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), h.r8]
  have h7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (N - i) := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), h.r7]
  refine WP.mono (VG.Proof.AesSiv.Arm.adStep_ok L he₂ (k := N - i) (by omega) hN32 h8₂ h7₂)
    fun s₃ ⟨he₃, rd₃, wr₃, g₃, h8₃, h7₃, hz₃, f₃, out₃⟩ => ?_
  -- The memory.
  have fs := h.frame
  have f₀₂ : Frame (VG.Proof.AesSiv.Arm.wR w sp) m₀ s₂.mem := fs.trans (by rw [← k₁.mem]; exact f₂.sub VG.Proof.AesSiv.Arm.macR_wR)
  have f₀₃ : Frame (VG.Proof.AesSiv.Arm.wR w sp) m₀ s₃.mem := f₀₂.trans (f₃.sub VG.Proof.AesSiv.Arm.dD_wR)
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  have dc : ∀ r ∈ VG.Proof.AesSiv.Arm.wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := VG.Proof.AesSiv.Arm.dis_wR L.c_w L.stk_c
  have mac₁ : Spec.Siv.ctxMac s₁.mem (State.addr c) R = Spec.Siv.ctxMac m₀ (State.addr c) R := by
    rw [k₁.mem]; exact VG.Proof.AesSiv.Arm.ctxMac_frame fs dc hRb
  have comp₁ : bytesAt s₁.mem (State.addr (VG.Proof.AesSiv.Arm.descW m₀ a i 0)) (VG.Proof.AesSiv.Arm.descW m₀ a i 1).toNat =
      bytesAt m₀ (State.addr (VG.Proof.AesSiv.Arm.descW m₀ a i 0)) (VG.Proof.AesSiv.Arm.descW m₀ a i 1).toNat := by
    rw [k₁.mem]; exact bytesAt_frame fs (VG.Proof.AesSiv.Arm.dis_wR (h.ads.comp i hi).w (h.ads.comp i hi).stk) (by omega)
  have dD₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
      bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 dOff) 16 := by
    refine bytesAt_frame f₂ (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have hl := VG.Proof.AesSiv.Arm.length_components m₀ (State.addr a) N
  refine ⟨⟨he₃, (h.ads.of_eq (by rw [rd₃, rd₂, k₁.rd]) (by rw [wr₃, wr₂, k₁.wr])), ?_, ?_,
    by rw [rd₃, rd₂, k₁.rd, h.rd], by rw [wr₃, wr₂, k₁.wr, h.wr], f₀₃, ?_⟩, ?_⟩
  · rw [h8₃, add32_ofNat_assoc]; congr 2
  · rw [h7₃]; congr 1
  · rw [out₃, out₂, dD₂, mac₁, comp₁, k₁.mem, h.acc, List.take_succ_eq_append_getElem (by omega), VG.Proof.AesSiv.Arm.s2vAcc_snoc,
      VG.Proof.AesSiv.Arm.components_getElem m₀ a hi]
    rfl
  · rw [hz₃]; congr 1

/-- S2V over all the components, from S2V's first state in `D`. -/
theorem s2vAds_ok (hR : R = 10 ∨ R = 12 ∨ R = 14) {a : BitVec 32} {N : Nat} {m₀ : Mem} {σ : State}
    {s : State} (h : VG.Proof.AesSiv.Arm.AInv c w sp a R N m₀ σ 0 s) (hN : N < 2 ^ 32) :
    WP isa s2vAds s (VG.Proof.AesSiv.Arm.AInv c w sp a R N m₀ σ N) := by
  obtain ⟨s₁, run₁, hz₁, k₁⟩ : ∃ s₁, runBlock isa [.cmp .r7 (imm 0)] s = some s₁ ∧ s₁.z = decide (N = 0) ∧
      s₁.gpr = s.gpr ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [z_subFlags, h.r7, Nat.sub_zero]; exact z_cmp hN (by decide)
    · rfl
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨g₁, k₁⟩ := k₁
  have h₁ : VG.Proof.AesSiv.Arm.AInv c w sp a R N m₀ σ 0 s₁ :=
    ⟨h.env.keep (fun r _ => by rw [g₁]) k₁.sp k₁.rd k₁.wr, h.ads.of_eq k₁.rd k₁.wr, by rw [g₁, h.r8],
      by rw [g₁, h.r7], by rw [k₁.rd, h.rd], by rw [k₁.wr, h.wr], by rw [k₁.mem]; exact h.frame,
      by rw [k₁.mem]; exact h.acc⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : N = 0
  · subst h0
    exact WP.ite true (eval_eq' (by rw [hz₁]; rfl)) (fun _ => WP.block_nil h₁) (fun h => by cases h)
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ j, n = N - j ∧ j < N ∧ VG.Proof.AesSiv.Arm.AInv c w sp a R N m₀ σ j t)
      ?_ (N - 0) s₁ ⟨0, rfl, by omega, h₁⟩
    rintro n t ⟨j, rfl, hj, hI⟩
    refine WP.mono (VG.Proof.AesSiv.Arm.aStep_ok L hR hI hj) fun t' ⟨hI', hz⟩ => ?_
    have ev : isa.eval .ne t' = some !decide (N - (j + 1) = 0) := eval_ne' hz
    by_cases hz' : N - (j + 1) = 0
    · left
      refine ⟨by rw [ev]; simp [hz'], ?_⟩
      have e : j + 1 = N := by omega
      rw [e] at hI'; exact hI'
    · right
      exact ⟨by rw [ev]; simp [hz'], N - (j + 1), by omega, j + 1, rfl, by omega, hI'⟩

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.FinishShort`. -/
section

/-!
# AES-SIV on ARMv7: finishing S2V with a string shorter than a block

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, `shortTail` copies `P` onto the zeroed tail at `W + 32` and
puts `0x80` after it, so the tail is `pad(P)`, doubles `D` into `W + 192`
and XORs it into the tail (`shortTail_ok`); `shortMac out` finalizes the
tail, one complete block, from a zero state at `W + out`
(`shortMac_ok`), which is S2V's end (`Siv.s2vFinish_short`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (z_cmp gpr_subFlags z_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags
  bytesAt_frame covers_left covers_off eval_eq' Keeps LoopPre LoopOut copyLoop_ok in_off)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok dbl_wp dblMem dblMem_bytes dblMem_frame b80)
open VG.Proof.MdStream.Arm (wp_mov wp_add wp_strb op2_imm op2_reg)
open VG.Proof.AesSiv (chain_blocks_nil)
open VG.Proof.AesCcm.Arm (blw)

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-- The tail after `shortTail`: `pad(P) ⊕ dbl(D)`. -/
theorem shortTail_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) {P : BitVec 32} {n : Nat} (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n)
    (hn : n < 16) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa shortTail s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (VG.Proof.AesSiv.Arm.wR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 =
        Spec.Cmac.xor (Spec.Siv.pad (bytesAt s.mem (State.addr P) n))
          (Spec.Siv.dbl (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16)) := by
  have ww := L.ww
  have eT := L.wA (d := tailOff) (by decide)
  have hlen : (bytesAt s.mem (State.addr P) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  -- The tail zeroed, and the arguments of the copy.
  rw [shortTail]
  refine WP.seq (VG.Proof.AesSiv.Arm.zero16_ok L he (d := tailOff) (by decide) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_)
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, hz₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [mov .r1 .r6, addI .r2 .r11 tailOff,
      mov .r3 .r5, .cmp .r5 (imm 0)] s₁ = some s₂ ∧ s₂.gpr .r1 = P ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 tailOff ∧
      s₂.gpr .r3 = BitVec.ofNat 32 n ∧ s₂.z = decide (n = 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
    have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide), h5]
    have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
    refine ⟨_, by simp only [mov, tailOff]; arun [h11₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h6₁]
    · simp [gpr_setReg, h11₁]
    · simp [gpr_setReg, h5₁]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5₁]
      exact z_cmp (by omega) (by decide)
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  -- The copy, if any: the tail is `P` followed by zeros.
  have pmem : bytesAt s₁.mem (State.addr P) n = bytesAt s.mem (State.addr P) n := by
    rw [m₁]
    exact bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.fit; omega)
  have copied : WP isa (.ite .eq (.block []) copyLoop) s₂ fun s₃ =>
      s₃.mem = VG.WriteBytes.writeBytes s₁.mem (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₃.gpr r = s₂.gpr r) ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.sp = s₂.sp := by
    by_cases h0 : n = 0
    · subst h0
      refine WP.ite true (eval_eq' (by rw [hz₂]; rfl)) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨?_, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
      rw [k₂.mem]; simp [bytesAt, VG.WriteBytes.writeBytes_nil]
    · refine WP.ite false (eval_eq' (by rw [hz₂]; simp [h0])) (fun h => by cases h) fun _ => ?_
      have lp : LoopPre s₂ P (w + BitVec.ofNat 32 tailOff) n :=
        ⟨h1₂, h2₂, h3₂, by omega, by omega, hP.fit, by rw [L.wN (by decide)]; simp only [tailOff]; omega,
          by rw [k₂.rd, k₂.wr, rd₁, wr₁]; exact hP.rd,
          by rw [eT, k₂.wr, wr₁]; exact he.perm.wC (by simp only [tailOff]; omega),
          by rw [eT]; exact hP.w.sub_right (Lay.wSub (by simp only [tailOff]; omega))⟩
      refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨m₃, lo⟩ => ?_
      refine ⟨by rw [m₃, k₂.mem, eT, pmem], lo.other, lo.rd, lo.wr, lo.sp⟩
  refine WP.seq (WP.mono copied fun s₃ ⟨m₃, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  -- `0x80` after `P`, and `r6 := W`.
  have h11₃ : s₃.gpr .r11 = w := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide), he.r11]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide), h5]
  refine wp_add (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  have a80 : State.addr (s₅.gpr .r2 + BitVec.ofNat 32 tailOff) =
      State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 n := by
    rw [u₅.other _ (by decide), u₄.gpr, h11₃, h5₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      L.wA (by simp only [tailOff]; omega),
      Offset.add_add, Nat.add_comm]
  refine wp_strb (by decide) a80 (by
      rw [u₅.wr, u₄.wr, wr₃, k₂.wr, wr₁, Offset.add_add]
      exact in_off he.perm.w (by simp only [tailOff]; omega) (by decide)) fun s₆ v₆ => ?_
  refine wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
  have h6₇ : s₇.gpr .r6 = w := by rw [u₇.gpr, v₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  have h11₇ : s₇.gpr .r11 = w := by
    rw [u₇.other _ (by decide), v₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  have hrw : s₇.rd ++ s₇.wr = s.rd ++ s.wr := by
    rw [u₇.rd, u₇.wr, v₆.rd, v₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rd₃, wr₃, k₂.rd, k₂.wr, rd₁, wr₁]
  have hw₇ : s₇.wr = s.wr := by rw [u₇.wr, v₆.wr, u₅.wr, u₄.wr, wr₃, k₂.wr, wr₁]
  have m₇ : s₇.mem = (VG.WriteBytes.writeBytes (Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 tailOff))
      (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n)).writeW
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 n) (0x80 : Byte) := by
    have b : (BitVec.setWidth 8 (BitVec.ofNat 32 128) : Byte) = 0x80 := by decide
    rw [u₇.mem, v₆.mem, u₅.gpr, u₅.mem, u₄.mem, m₃, m₁, b]
  refine dbl_wp (K := w) h6₇ (src := dOff) (dst := dbOff) (by decide) (by decide) (by simp only [dOff]; omega)
    (by simp only [dbOff]; omega) (by rw [hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [hw₇]; exact he.perm.wC (by decide)) fun s₈ g₈ m₈ rd₈ wr₈ sp₈ => ?_
  have h11₈ : s₈.gpr .r11 = w := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h11₇]
  rw [VG.Proof.AesSiv.Arm.xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h11₈]; simp only [tailOff]; omega)
    (by rw [h11₈]; simp only [dbOff]; omega) (by rw [h11₈]; simp only [tailOff]; omega)
    (by rw [h11₈, rd₈, wr₈, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₈, rd₈, wr₈, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₈, wr₈, hw₇]; exact he.perm.wC (by decide)) fun s₉ g₉ => WP.block_nil ?_
  -- The registers.
  have gT : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r12 → r ≠ .lr →
      s₉.gpr r = s.gpr r := fun r a0 a1 a2 a3 a4 a6 a12 alr => by
    rw [g₉.gpr r a12 alr, g₈ r a0 a1 a2 a3 a4 a12, u₇.other r a6, v₆.gpr, u₅.other r a12, u₄.other r a2,
      g₃ r a0 a1 a2 a3 a12, g₂ r a1 a2 a3, g₁ r a12]
  have rd₉ : s₉.rd = s.rd := by rw [g₉.rd, rd₈, u₇.rd, v₆.rd, u₅.rd, u₄.rd, rd₃, k₂.rd, rd₁]
  have wr₉ : s₉.wr = s.wr := by rw [g₉.wr, wr₈, hw₇]
  have sp₉ : s₉.sp = s.sp := by rw [g₉.sp, sp₈, u₇.sp, v₆.sp, u₅.sp, u₄.sp, sp₃, k₂.sp, sp₁]
  -- The memory.
  have dTB : (⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 dbOff, 16⟩ := L.w_w (.inl (by decide)) (by decide) (by decide)
  have m₉ : s₉.mem = Proof.Cmac.xor4Mem (dblMem s₇.mem (State.addr w) dOff dbOff)
      (State.addr w + BitVec.ofNat 64 tailOff) (State.addr w + BitVec.ofNat 64 tailOff)
      (State.addr w + BitVec.ofNat 64 dbOff) := by rw [g₉.mem, m₈, h11₈]
  have f₇ : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩] s.mem s₇.mem := by
    rw [m₇]
    refine ((Proof.Cmac.frame_store4 _ _ _ _ _).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    rw [hlen]
    simpa using Offset.contains_base (State.addr w + BitVec.ofNat 64 tailOff) (d := 0) (n := n) (k := 16)
      (by omega) (by decide)
  have f₉ : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩, ⟨State.addr w + BitVec.ofNat 64 dbOff, 16⟩]
      s.mem s₉.mem := by
    rw [m₉]
    exact ((f₇.mono (by simp)).trans ((dblMem_frame _ _ _ _).mono (by simp))).trans
      ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact gT _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) sp₉ rd₉ wr₉, rd₉, wr₉, fun r hr h4 h6 hlr => ?_,
    f₉.sub fun r hr => ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact gT r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 h6 a.2.2.2.2 hlr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · have dD : (⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint
        ⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩ := L.w_w (.inr (by decide)) (by decide) (by decide)
    have pad := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 tailOff))
      (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n) (by rw [hlen]; exact hn)
      (Proof.Cmac.zero4_bytes _ _)
    rw [hlen] at pad
    rw [m₉, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dTB),
      dblMem_bytes, bytesAt_frame (dblMem_frame _ _ _ _) (p := State.addr w + BitVec.ofNat 64 tailOff) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dTB) (by omega),
      bytesAt_frame f₇ (p := State.addr w + BitVec.ofNat 64 dOff) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by omega),
      m₇, pad, Spec.Siv.pad, hlen, Spec.Siv.dbl, show 16 - n - 1 = 15 - n by omega]
    rfl

omit L in
/-- The CMAC of one block. -/
theorem cmacWith_one (ciph : Spec.Cmac.Cipher) (k1 k2 T : List Byte) (hT : T.length = 16) :
    Spec.Siv.cmacWith ciph k1 k2 T = ciph (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 k1 k2 T) (Spec.Cmac.zeros 16)) := by
  rw [Siv.cmacWith_chained, hT, show Spec.Cmac.chainedLen 16 16 = 0 from rfl, List.take_zero, List.drop_zero,
    chain_blocks_nil, Proof.Cmac.xor_comm]

/-- `shortArgs out`: the state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_finalize` of the tail, one complete block. -/
theorem shortArgs_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (.block (shortArgs out)) s fun s₂ => VG.Proof.AesSiv.Arm.Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 out) ∧
      VG.Proof.AesSiv.Arm.FArgs s₂ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  rw [shortArgs, List.append_assoc]
  refine VG.Proof.AesSiv.Arm.zero16_ok L he (d := out) (by omega) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  obtain ⟨s₂, run₂, he₂, g₂, k₂, F⟩ : ∃ s₂, runBlock isa (macArgs out ++ [addI .r3 .r11 tailOff, .mov .r12 (imm 16)])
      s₁ = some s₂ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ ∧
      VG.Proof.AesSiv.Arm.FArgs s₂ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R := by
    refine ⟨_, by simp only [macArgs, csOff, tailOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11, eo], ?_⟩
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine VG.Proof.AesSiv.Arm.fargs_of L ?_ hR (st := out) (by omega) (n := 16) (by decide)
      (by rw [L.wN (by decide)]; simp only [tailOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [eT]; exact L.w_w (by omega) (by decide) (by omega)
    · rw [eT]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eT]; exact L.stk_w' (by decide)
    · rw [eT]; exact covers_left (he₁.perm.wC (by decide))
    · simp [gpr_setReg, he₁.r10]
    · simp [gpr_setReg, he₁.r9]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₁.r11]
  exact WP.of_runBlock ⟨s₂, run₂, he₂, fun r a b c' d e f => by rw [g₂ r a b c' d e f, g₁ r e],
    by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁], by rw [k₂.mem, m₁], F⟩

/-- `shortMac out`: the CMAC of the tail, one block, at `W + out`. -/
theorem shortMac_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (shortMac out) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (VG.Proof.AesSiv.Arm.oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.ctxMac s.mem (State.addr c) R (bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) 16) := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  have eO := L.wA (d := out) (by omega)
  rw [shortMac]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.shortArgs_ok L he hR hout) fun s₂ ⟨he₂, g₂, rd₂, wr₂, m₂, F⟩ => ?_)
  refine WP.mono (VG.Proof.AesSiv.Arm.fin_call F) fun s₃ h₃ => ?_
  have hb := VG.Proof.AesSiv.Arm.blw16_eq (s := s₂) he₂.sp
  have f₃ := h₃.frame
  rw [eO, L.wA (d := 256) (by decide), hb] at f₃
  have f₁ : Frame (VG.Proof.AesSiv.Arm.oR w sp out) s.mem s₂.mem := by
    rw [m₂]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  have f₃' : Frame (VG.Proof.AesSiv.Arm.oR w sp out) s₂.mem s₃.mem := by
    exact f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨blw sp, by simp, fun _ h => h⟩
  have fT := f₁.trans f₃'
  refine ⟨he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr, by rw [h₃.rd, rd₂], by rw [h₃.wr, wr₂],
    fun r hr hlr => ?_, fT, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · -- What the call reads is as on entry.
    have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 out, 16⟩] s.mem s₂.mem := by
      rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₂.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' hd (by omega)) (by omega)
    have sch := cK (d := 0) (k := 16 * (R + 1)) (by omega)
    rw [BitVec.add_zero] at sch
    have tl : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by decide) (by omega)) (by decide)
    have z : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
      rw [m₂, Proof.Cmac.zero4_bytes]
    have out₃ := h₃.out
    rw [eO, eT, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide), tl, z] at out₃
    rw [out₃, Spec.Siv.ctxMac, Spec.Siv.schedCiph, VG.Proof.AesSiv.Arm.cmacWith_one _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _)]
    rfl

/-- S2V's end for a string `P` shorter than a block, into `W + out`. -/
theorem short_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) (hn : n < 16) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (.seq shortTail (shortMac out)) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (VG.Proof.AesSiv.Arm.oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.shortTail_ok L he hP hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, f₁, t₁⟩ => ?_)
  refine WP.mono (VG.Proof.AesSiv.Arm.shortMac_ok L he₁ hR hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
  refine ⟨he₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h4 h6 hlr => by rw [g₂ r hr hlr, g₁ r hr h4 h6 hlr],
    (VG.Proof.AesSiv.Arm.frame_oR out f₁).trans f₂, ?_⟩
  rw [o₂, t₁, VG.Proof.AesSiv.Arm.ctxMac_frame f₁ (VG.Proof.AesSiv.Arm.dis_wR L.c_w L.stk_c) (VG.Proof.AesSiv.Arm.rounds_le hR),
    Siv.s2vFinish_short _ _ (by rw [Proof.Cmac.bytesAt_length]; exact hn), Siv.xor_eq, Proof.Cmac.xor_comm]

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.FinishLong`. -/
section

/-!
# AES-SIV on ARMv7: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, `longTail` computes `16 k` (`kBlock_ok`, `kOf`), copies the
last `T = L − 16 k` bytes of `P` to the tail at `W + 32` and XORs `D` into
its last 16 (`tailCopy_ok`, `xorend_mem4`); `longMac out` chains the `k`
blocks of `P`, then the first `j` blocks of the tail, and finalizes the rest
(`longMac_ok`), which is S2V's end (`long_spec`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (z_cmp gpr_subFlags z_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags
  bytesAt_frame covers_left covers_off eval_eq' Keeps LoopPre LoopOut copyLoop_ok in_off ofNat_sub32 shr4 addr_toNat
  add32_ofNat_assoc)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok)
open VG.Proof.MdStream.Arm (wp_sub wp_add op2_reg)
open VG.Proof.AesCcm.Arm (blw UArgs UPost upd_call)
open VG.Proof.CmacAes.Stream.Arm (blw16)
open VG.Proof.AesSiv (kOf jOf kOf_lt kOf_ge kOf_tail jOf_rest jOf_le take_bytesAt drop_bytesAt long_spec)

/-- XORing `D` into the last 16 of `T` bytes, a word at a time. -/
theorem xorend_mem4 (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    bytesAt (Proof.Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16)) (B + BitVec.ofNat 64 (T - 16)) Q) B T =
      Spec.Siv.xorend (bytesAt m B T) (bytesAt m Q 16) := by
  have hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega)
  have e : T = (T - 16) + 16 := by omega
  have hs := Proof.Cmac.Stream.bytesAt_append (Proof.Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16))
    (B + BitVec.ofNat 64 (T - 16)) Q) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := take_bytesAt m B (a := T - 16) (b := 16)
  have dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (hd.sub_left hc)),
    Siv.xor_eq]

theorem shl4' {n : Nat} (hn : 16 * n < 2 ^ 32) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16 * n) := VG.Proof.AesSiv.Arm.shl4 hn

/-- `kBlock`: `16 k` in `r4`. -/
theorem kBlock_ok {s : State} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa kBlock s fun s' => s'.gpr .r4 = BitVec.ofNat 32 (16 * kOf n) ∧
      (∀ r, r ≠ .r4 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have e1 : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega) hn
  have e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := VG.Proof.AesGcm.Arm.shr4 (by omega)
  obtain ⟨s₁, run₁, h12₁, h4₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.dp .sub .r12 .r5 (imm 1),
      .mov .r12 (.shifted .r12 .lsr 4), .mov .r4 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 32 ((n - 1) / 16) ∧ s₁.gpr .r4 = 0 ∧ s₁.z = decide ((n - 1) / 16 = 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [h5], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h5, e1, e2]
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, e1, e2]
      exact z_cmp (by omega) (by decide)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : (n - 1) / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨by rw [h4₁, kOf_lt (by omega)]; rfl, g₁, k₁⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    have e3 : BitVec.ofNat 32 ((n - 1) / 16) - 1#32 = BitVec.ofNat 32 ((n - 1) / 16 - 1) :=
      ofNat_sub32 (by omega) (by omega)
    have e4 : BitVec.ofNat 32 ((n - 1) / 16 - 1) <<< 4 = BitVec.ofNat 32 (16 * ((n - 1) / 16 - 1)) :=
      VG.Proof.AesSiv.Arm.shl4 (by omega)
    refine WP.of_runBlock ⟨_, by arun [h12₁], ?_, ?_, ?_⟩
    · simp [gpr_setReg, h12₁, e3, e4, kOf_ge (show ¬ n < 17 by omega)]
    · intro r a b; simp [gpr_setReg, a, b, g₁ r a b]
    · exact ⟨k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p xs.length = xs := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base m p xs (Nat.le_refl _) hn,
    List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil]

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-- `longTail`: `16 k` in `r4`, and the tail `P[16k..] xorend D` at `W + 32`. -/
theorem longTail_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) {P : BitVec 32} {n : Nat} (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n)
    (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa longTail s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (16 * kOf n) ∧ Frame (VG.Proof.AesSiv.Arm.wR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tailOff) (n - 16 * kOf n) =
        Spec.Siv.xorend ((bytesAt s.mem (State.addr P) n).drop (16 * kOf n))
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) := by
  have ww := L.ww
  have hT := kOf_tail h16
  generalize hK : 16 * kOf n = K at hT ⊢
  have eT := L.wA (d := tailOff) (by decide)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.kBlock_ok h16 hn h5) fun s₁ ⟨h4₁, g₁, k₁⟩ => ?_)
  rw [hK] at h4₁
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide) (by decide), h6]
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide) (by decide), h5]
  have hq : VG.Proof.AesSiv.Arm.Buf w sp s₁ (P + BitVec.ofNat 32 K) (n - K) :=
    (hP.sub (j := K) (k := n - K) (by omega) (by omega)).of_eq k₁.rd k₁.wr
  have eK : BitVec.ofNat 32 n - BitVec.ofNat 32 K = BitVec.ofNat 32 (n - K) := ofNat_sub32 (by omega) hn
  rw [tailCopy]
  refine WP.seq (WP.of_runBlock ⟨_, by simp only [tailOff]; arun [h6₁, h5₁, h4₁, he₁.r11], ?_⟩)
  -- The copy of the last `T` bytes.
  refine WP.seq (WP.mono (copyLoop_ok (S := P + BitVec.ofNat 32 K) (D := w + BitVec.ofNat 32 tailOff)
      (n := n - K) _ ⟨by simp [gpr_setReg, h6₁, h4₁], by simp [gpr_setReg, he₁.r11],
      by simp [gpr_setReg, h5₁, h4₁, eK], by omega, by omega, hq.fit,
      by rw [L.wN (by decide)]; simp only [tailOff]; omega, hq.rd,
      by rw [eT]; exact he₁.perm.wC (by simp only [tailOff]; omega),
      by rw [eT]; exact hq.w.sub_right (Lay.wSub (by simp only [tailOff]; omega))⟩) fun s₃ ⟨m₃, lo⟩ => ?_)
  have h11₃ : s₃.gpr .r11 = w := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, he₁.r11]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, h5₁]
  have h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 K := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, h4₁]
  refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_add (op2_reg _ _) fun s₅ u₅ => ?_
  have h0₅ : s₅.gpr .r0 = w + BitVec.ofNat 32 (n - K) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, h11₃, h5₃, h4₃, eK]
  have h11₅ : s₅.gpr .r11 = w := by rw [u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  have eA : State.addr (w + BitVec.ofNat 32 (n - K)) + BitVec.ofNat 64 16 =
      State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16) := by
    rw [L.wA (by omega), Offset.add_add, Offset.add_add]; congr 2; simp only [tailOff]; omega
  have hrw : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by
    rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, lo.rd, lo.wr]; simp only [rd_setReg, wr_setReg, k₁.rd, k₁.wr]
  have hw₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, lo.wr]; simp only [wr_setReg, k₁.wr]
  rw [VG.Proof.AesSiv.Arm.xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h0₅, L.wN (by omega)]; omega)
    (by rw [h11₅]; simp only [dOff]; omega) (by rw [h0₅, L.wN (by omega)]; omega)
    (by rw [h0₅, eA, hrw, Offset.add_add]; exact covers_left (he.perm.wC (by simp only [tailOff]; omega)))
    (by rw [h11₅, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h0₅, eA, hw₅, Offset.add_add]; exact he.perm.wC (by simp only [tailOff]; omega)) fun s₆ g₆ => WP.block_nil ?_
  have gT : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr →
      s₆.gpr r = s.gpr r := fun r a0 a1 a2 a3 a4 a12 alr => by
    rw [g₆.gpr r a12 alr, u₅.other r a0, u₄.other r a0, lo.other r a0 a1 a2 a3 a12]
    simp only [gpr_setReg, a1, a2, a3, ite_false, reduceCtorEq]
    rw [g₁ r a4 a12]
  have rd₆ : s₆.rd = s.rd := by
    rw [g₆.rd, u₅.rd, u₄.rd, lo.rd]; simp only [rd_setReg, k₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [g₆.wr, hw₅]
  have sp₆ : s₆.sp = s.sp := by
    rw [g₆.sp, u₅.sp, u₄.sp, lo.sp]; simp only [sp_setReg, k₁.sp]
  have aP : State.addr (P + BitVec.ofNat 32 K) = State.addr P + BitVec.ofNat 64 K := hP.addr (by omega)
  have m₅ : s₅.mem = VG.WriteBytes.writeBytes s.mem (State.addr w + BitVec.ofNat 64 tailOff)
      (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)) := by
    rw [u₅.mem, u₄.mem, m₃, eT, aP]; simp only [mem_setReg, k₁.mem]
  have hlx : (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)).length = n - K :=
    Proof.Cmac.bytesAt_length _ _ _
  have fW : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩] s.mem s₅.mem := by
    rw [m₅]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hlx]; exact Region.contains_self _ _)
  have m₆ : s₆.mem = Proof.Cmac.xor4Mem s₅.mem
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16))
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16))
      (State.addr w + BitVec.ofNat 64 dOff) := by rw [g₆.mem, h0₅, h11₅, eA]
  have dTD : (⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ := L.w_w (.inl (by simp only [tailOff, dOff]; omega))
        (by simp only [tailOff]; omega) (by decide)
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact gT _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) sp₆ rd₆ wr₆, rd₆, wr₆, fun r hr h4 hlr => ?_, ?_, ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact gT r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 a.2.2.2.2 hlr
  · rw [g₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), u₄.other _ (by decide), h4₃]
  · rw [m₆]
    refine (fW.sub fun r hr => ?_).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp,
        Offset.sub _ (by simp only [tailOff]; omega) (by simp only [tailOff]; omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, ?_⟩
      rw [Offset.add_add]; exact Offset.sub _ (by simp only [tailOff]; omega) (by simp only [tailOff]; omega)
  · have hBw : (State.addr w + BitVec.ofNat 64 tailOff).toNat + (n - K) ≤ 2 ^ 64 := by
      rw [← eT, addr_toNat, L.wN (by decide)]; simp only [tailOff]; omega
    rw [m₆, VG.Proof.AesSiv.Arm.xorend_mem4 _ (by omega) hBw dTD,
      m₅, bytesAt_frame (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩)
        (by rw [hlx]; exact Region.contains_self _ _)) (p := State.addr w + BitVec.ofNat 64 dOff)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTD.symm) (by decide)]
    have ws := VG.Proof.AesSiv.Arm.bytesAt_writeBytes_self s.mem (State.addr w + BitVec.ofNat 64 tailOff)
      (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)) (by omega)
    rw [hlx] at ws
    rw [ws]
    have dr := drop_bytesAt s.mem (State.addr P) (a := K) (b := n - K)
    rw [show K + (n - K) = n by omega] at dr
    rw [dr]

omit L in
/-- `jBlock`: `j` in `r7`. -/
theorem jBlock_ok {s : State} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa jBlock s fun s' => s'.gpr .r7 = BitVec.ofNat 32 (jOf n) ∧
      (∀ r, r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have e1 : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega) hn
  have e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := VG.Proof.AesGcm.Arm.shr4 (by omega)
  obtain ⟨s₁, run₁, h7₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.dp .sub .r12 .r5 (imm 1),
      .mov .r12 (.shifted .r12 .lsr 4), .mov .r7 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r7 = 0 ∧ s₁.z = decide ((n - 1) / 16 = 0) ∧
      (∀ r, r ≠ .r7 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [h5], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, e1, e2]
      exact z_cmp (by omega) (by decide)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : (n - 1) / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨by rw [h7₁]; simp [jOf, show n < 17 by omega], g₁, k₁⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, jOf, show ¬ n < 17 by omega]
    · intro r a b; simp [gpr_setReg, a, g₁ r a b]
    · exact ⟨k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩

/-- What `longMac out` computes, from the memory `m` before it: the CMAC of
the `k` blocks of `P`, the first `j` blocks of the tail, and the rest of the
tail. -/
def longVal (m : Mem) (C W P : Addr) (R n : Nat) : List Byte :=
  Spec.Siv.schedCiph m C R (Spec.Cmac.xor
    (Spec.Cmac.lastBlock 16 (bytesAt m (C + BitVec.ofNat 64 240) 16) (bytesAt m (C + BitVec.ofNat 64 256) 16)
      ((bytesAt m (W + BitVec.ofNat 64 tailOff) (n - 16 * kOf n)).drop (16 * jOf n)))
    (Spec.Cmac.chain (Spec.Siv.schedCiph m C R)
      (Spec.Cmac.chain (Spec.Siv.schedCiph m C R) (Spec.Cmac.zeros 16)
        (Spec.Cmac.blocks 16 ((bytesAt m P n).take (16 * kOf n))))
      (Spec.Cmac.blocks 16 ((bytesAt m (W + BitVec.ofNat 64 tailOff) (n - 16 * kOf n)).take (16 * jOf n)))))

/-- What the calls of `longMac out` write. -/
abbrev outR (w sp : BitVec 32) (out : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 out, 16⟩, VG.Proof.AesSiv.Arm.scrR w, blw sp]

/-- `longArgs₁ out`: the state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_update` over the `K / 16` blocks of the string. -/
theorem longArgs₁_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32}
    {n K : Nat} (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) (hKn : K ≤ n) (hK16 : 16 * (K / 16) = K) (hn : n < 2 ^ 32)
    (h6 : s.gpr .r6 = P) (h4 : s.gpr .r4 = BitVec.ofNat 32 K) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (.block (longArgs₁ out)) s fun s₂ => VG.Proof.AesSiv.Arm.Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 out) ∧
      UArgs s₂ c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16) := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  rw [longArgs₁, List.append_assoc]
  refine VG.Proof.AesSiv.Arm.zero16_ok L he (d := out) (by omega) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  have hq := (hP.take (k := K) hKn).of_eq rd₁ wr₁
  have hsh : BitVec.ofNat 32 K >>> 4 = BitVec.ofNat 32 (K / 16) := VG.Proof.AesGcm.Arm.shr4 (by omega)
  obtain ⟨s₂, run₂, he₂, g₂, k₂, U₁⟩ : ∃ s₂, runBlock isa (macArgs out ++ [mov .r3 .r6, .mov .r12 (.shifted .r4 .lsr 4)])
      s₁ = some s₂ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ ∧
      UArgs s₂ c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16) := by
    have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
    have h4₁ : s₁.gpr .r4 = BitVec.ofNat 32 K := by rw [g₁ _ (by decide), h4]
    refine ⟨_, by simp only [macArgs, csOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11, eo], ?_⟩
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine VG.Proof.AesSiv.Arm.uargs_of L ?_ hR (st := out) (by omega) (n := K / 16) (by omega)
      (by rw [show 16 * (K / 16) = K by omega]; exact hq.fit) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [show 16 * (K / 16) = K by omega]; exact hq.w.sub_right (Lay.wSub (by omega))
    · rw [show 16 * (K / 16) = K by omega]; exact hq.w.sub_right (Lay.wSub (by decide))
    · rw [show 16 * (K / 16) = K by omega]; exact hq.stk
    · rw [show 16 * (K / 16) = K by omega]; exact hq.rd
    · simp [gpr_setReg, he₁.r10]
    · simp [gpr_setReg, he₁.r9]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg, h6₁]
    · simp [gpr_setReg, h4₁, hsh]
    · simp [gpr_setReg, he₁.r11]
  exact WP.of_runBlock ⟨s₂, run₂, he₂, fun r a b c' d e f => by rw [g₂ r a b c' d e f, g₁ r e],
    by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁], by rw [k₂.mem, m₁], U₁⟩

/-- `longArgs₂ out`: the arguments of `vg_cmac_aes_update` over the first `j`
blocks of the tail. -/
theorem longArgs₂_ok {s₄ : State} (he₄ : VG.Proof.AesSiv.Arm.Env c w sp R s₄) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) {j : Nat} (hj1 : j ≤ 1) (h7₄ : s₄.gpr .r7 = BitVec.ofNat 32 j) :
    ∃ s₅, runBlock isa (longArgs₂ out) s₄ = some s₅ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₅ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ ∧
      UArgs s₅ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) R j := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  refine ⟨_, by simp only [longArgs₂, macArgs, csOff, tailOff, mov]; arun [he₄.r9, he₄.r10, he₄.r11, eo], ?_⟩
  refine ⟨he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine VG.Proof.AesSiv.Arm.uargs_of L ?_ hR (st := out) (by omega) (n := j) (by omega)
    (by rw [L.wN (by decide)]; simp only [tailOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · rw [eT]; exact L.w_w (by simp only [tailOff] at hoT ⊢; omega) (by simp only [tailOff]; omega) (by omega)
  · rw [eT]; exact L.w_w (.inl (by simp only [tailOff]; omega)) (by simp only [tailOff]; omega) (by decide)
  · rw [eT]; exact L.stk_w' (by simp only [tailOff]; omega)
  · rw [eT]; exact covers_left (he₄.perm.wC (by simp only [tailOff]; omega))
  · simp [gpr_setReg, he₄.r10]
  · simp [gpr_setReg, he₄.r9]
  · simp [gpr_setReg, he₄.r11]
  · simp [gpr_setReg, he₄.r11]
  · simp [gpr_setReg, h7₄]
  · simp [gpr_setReg, he₄.r11]

/-- `longArgs₃ out`: the arguments of `vg_cmac_aes_finalize` over the rest of
the tail. -/
theorem longArgs₃_ok {s₆ : State} (he₆ : VG.Proof.AesSiv.Arm.Env c w sp R s₆) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) {n K j : Nat} (hn : n < 2 ^ 32) (hT : 16 ≤ n - K ∧ n - K ≤ 32)
    (hJ : 16 * j ≤ n - K ∧ 0 < n - K - 16 * j ∧ n - K - 16 * j ≤ 16) (hj1 : j ≤ 1)
    (h7₆ : s₆.gpr .r7 = BitVec.ofNat 32 j) (h5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n)
    (h4₆ : s₆.gpr .r4 = BitVec.ofNat 32 K) :
    ∃ s₇, runBlock isa (longArgs₃ out) s₆ = some s₇ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₇ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₇.gpr r = s₆.gpr r) ∧ Keeps s₆ s₇ ∧
      VG.Proof.AesSiv.Arm.FArgs s₇ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 (tailOff + 16 * j)) (w + BitVec.ofNat 32 256)
        (n - K - 16 * j) R := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have e7 : BitVec.ofNat 32 j <<< 4 = BitVec.ofNat 32 (16 * j) := VG.Proof.AesSiv.Arm.shl4 (by omega)
  have eR : BitVec.ofNat 32 n - BitVec.ofNat 32 K - BitVec.ofNat 32 (16 * j) =
      BitVec.ofNat 32 (n - K - 16 * j) := by
    rw [ofNat_sub32 (by omega) hn, ofNat_sub32 (by omega) (by omega)]
  have eA : w + BitVec.ofNat 32 tailOff + BitVec.ofNat 32 (16 * j) = w + BitVec.ofNat 32 (tailOff + 16 * j) :=
    add32_ofNat_assoc _ _ _
  refine ⟨_, by simp only [longArgs₃, macArgs, csOff, mov]; arun [he₆.r9, he₆.r10, he₆.r11, eo], ?_⟩
  refine ⟨he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine VG.Proof.AesSiv.Arm.fargs_of L ?_ hR (st := out) (by omega) (n := n - K - 16 * j) (by omega)
    (by rw [L.wN (by simp only [tailOff]; omega)]; simp only [tailOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · rw [L.wA (by simp only [tailOff]; omega)]
    exact L.w_w (by simp only [tailOff] at hoT ⊢; omega) (by simp only [tailOff]; omega) (by omega)
  · rw [L.wA (by simp only [tailOff]; omega)]
    exact L.w_w (.inl (by simp only [tailOff]; omega)) (by simp only [tailOff]; omega) (by decide)
  · rw [L.wA (by simp only [tailOff]; omega)]; exact L.stk_w' (by simp only [tailOff]; omega)
  · rw [L.wA (by simp only [tailOff]; omega)]; exact covers_left (he₆.perm.wC (by simp only [tailOff]; omega))
  · simp [gpr_setReg, he₆.r10]
  · simp [gpr_setReg, he₆.r9]
  · simp [gpr_setReg, he₆.r11]
  · simp [gpr_setReg, he₆.r11, h7₆, e7, eA]
  · simp [gpr_setReg, h5₆, h4₆, h7₆, e7, eR]
  · simp [gpr_setReg, he₆.r11]

/-- `longMac out`: S2V's end for a long string, from its tail, at `W + out`. -/
theorem longMac_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (h4 : s.gpr .r4 = BitVec.ofNat 32 (16 * kOf n)) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (longMac out) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        VG.Proof.AesSiv.Arm.longVal s.mem (State.addr c) (State.addr w) (State.addr P) R n := by
  have ww := L.ww
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le n
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  have eO := L.wA (d := out) (by omega)
  have eS := L.wA (d := 256) (by decide)
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  generalize hK : 16 * kOf n = K at hT hJ h4 ⊢
  have hKk : K / 16 = kOf n := by omega
  generalize hj : jOf n = j at hJ hj1 ⊢
  -- The first call's arguments.
  rw [longMac]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.longArgs₁_ok L he hR hP (by omega) (by omega) hn h6 h4 hout)
    fun s₂ ⟨he₂, g₂, rd₂, wr₂, m₂, U₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U₁) fun s₃ h₃ => ?_)
  have he₃ := he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr
  have g₃ : ∀ r ∈ preserved, r ≠ .lr → s₃.gpr r = s.gpr r := fun r hr hlr => by
    have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by rw [g₃ _ (by decide) (by decide), h5]
  have h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 K := by rw [g₃ _ (by decide) (by decide), h4]
  -- `j`.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.jBlock_ok h16 hn h5₃) fun s₄ ⟨h7₄, g₄, k₄⟩ => ?_)
  rw [hj] at h7₄
  have he₄ : VG.Proof.AesSiv.Arm.Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) k₄.sp k₄.rd k₄.wr
  have h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [g₄ _ (by decide) (by decide), h5₃]
  have h4₄ : s₄.gpr .r4 = BitVec.ofNat 32 K := by rw [g₄ _ (by decide) (by decide), h4₃]
  -- The second call's arguments: the first `j` blocks of the tail.
  obtain ⟨s₅, run₅, he₅, g₅, k₅, U₂⟩ := VG.Proof.AesSiv.Arm.longArgs₂_ok L he₄ hR hout hj1 h7₄
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.seq (WP.mono (upd_call U₂) fun s₆ h₆ => ?_)
  have he₆ := he₅.of_saved h₆.saved h₆.sp h₆.rd h₆.wr
  have g₆ : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → s₆.gpr r = s₄.gpr r := fun r hr h7 hlr => by
    have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₆.saved r hr hlr, g₅ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  have h7₆ : s₆.gpr .r7 = BitVec.ofNat 32 j := by
    rw [h₆.saved _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h7₄]
  have h5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n := by rw [g₆ _ (by decide) (by decide) (by decide), h5₄]
  have h4₆ : s₆.gpr .r4 = BitVec.ofNat 32 K := by rw [g₆ _ (by decide) (by decide) (by decide), h4₄]
  -- The third call's arguments: the rest of the tail.
  obtain ⟨s₇, run₇, he₇, g₇, k₇, F⟩ := VG.Proof.AesSiv.Arm.longArgs₃_ok L he₆ hR hout hn hT hJ hj1 h7₆ h5₆ h4₆
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.Arm.fin_call F) fun s₈ h₈ => ?_
  have hb₂ := VG.Proof.AesSiv.Arm.blw16_eq (s := s₂) he₂.sp
  have hb₅ := VG.Proof.AesSiv.Arm.blw16_eq (s := s₅) he₅.sp
  have hb₇ := VG.Proof.AesSiv.Arm.blw16_eq (s := s₇) he₇.sp
  -- What each step writes.
  have F₃ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s₂.mem s₃.mem := by
    have := h₃.frame; rw [eO, eS, hb₂] at this; exact this
  have F₆ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s₅.mem s₆.mem := by
    have := h₆.frame; rw [eO, eS, hb₅] at this; exact this
  have F₈ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s₇.mem s₈.mem := by
    have := h₈.frame; rw [eO, eS, hb₇] at this; exact this
  have F₀₂ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem s₂.mem := by
    rw [m₂]; exact (Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)
  have F₀₃ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem s₃.mem := F₀₂.trans F₃
  have F₀₅ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem s₅.mem := by rw [k₅.mem, k₄.mem]; exact F₀₃
  have F₀₆ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem s₆.mem := F₀₅.trans F₆
  have F₀₇ : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem s₇.mem := by rw [k₇.mem]; exact F₀₆
  refine ⟨he₇.of_saved h₈.saved h₈.sp h₈.rd h₈.wr, by rw [h₈.rd, k₇.rd, h₆.rd, k₅.rd, k₄.rd, h₃.rd, rd₂],
    by rw [h₈.wr, k₇.wr, h₆.wr, k₅.wr, k₄.wr, h₃.wr, wr₂], fun r hr h7 hlr => ?_, F₀₇.trans F₈, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₈.saved r hr hlr, g₇ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr, g₆ r hr h7 hlr, g₄ r h7 a.2.2.2.2,
      g₃ r hr hlr]
  -- What the calls read is as on entry, but the state.
  have dc : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ VG.Proof.AesSiv.Arm.outR w sp out, (⟨State.addr c + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.c_w' hd (by omega)
    · exact L.c_w' hd (by decide)
    · exact (L.stk_c' hd).symm
  have dt : ∀ {d k : Nat}, tailOff + d + k ≤ 64 → ∀ r ∈ VG.Proof.AesSiv.Arm.outR w sp out,
      (⟨State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    rw [Offset.add_add]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (by simp only [tailOff] at hoT hd ⊢; omega) (by omega) (by omega)
    · exact L.w_w (.inl (by simp only [tailOff] at hd ⊢; omega)) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm
  have dp : ∀ r ∈ VG.Proof.AesSiv.Arm.outR w sp out, (⟨State.addr P, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by omega))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
  have cK {m' : Mem} (hf : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem m') {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt m' (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (dc hd) (by omega)
  have cT {m' : Mem} (hf : Frame (VG.Proof.AesSiv.Arm.outR w sp out) s.mem m') {d k : Nat} (hd : tailOff + d + k ≤ 64) :
      bytesAt m' (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d) k =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (dt hd) (by omega)
  have k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  have sch₂ := cK F₀₂ (d := 0) (k := 16 * (R + 1)) (by omega)
  have sch₅ := cK F₀₅ (d := 0) (k := 16 * (R + 1)) (by omega)
  have sch₇ := cK F₀₇ (d := 0) (k := 16 * (R + 1)) (by omega)
  rw [k0] at sch₂ sch₅ sch₇
  have k1 := cK F₀₇ (d := 240) (k := 16) (by decide)
  have k2 := cK F₀₇ (d := 256) (k := 16) (by decide)
  have pK : bytesAt s₂.mem (State.addr P) K = bytesAt s.mem (State.addr P) K :=
    bytesAt_frame F₀₂ (fun r hr => (dp r hr).sub_left (Region.sub_prefix (by omega))) (by omega)
  have tJ := cT F₀₅ (d := 0) (k := 16 * j) (by simp only [tailOff]; omega)
  have tR := cT F₀₇ (d := 16 * j) (k := n - K - 16 * j) (by simp only [tailOff]; omega)
  rw [k0] at tJ
  have z₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂, Proof.Cmac.zero4_bytes]
  have o₃ := h₃.out
  have o₆ := h₆.out
  have o₈ := h₈.out
  rw [eO, sch₂, z₂, Proof.Cmac.Stream.blocksAt_eq, show 16 * (K / 16) = K by omega, pK] at o₃
  rw [eO, eT, sch₅, k₅.mem, k₄.mem, o₃, Proof.Cmac.Stream.blocksAt_eq, ← k₄.mem, ← k₅.mem, tJ] at o₆
  rw [eO, L.wA (by simp only [tailOff]; omega), ← Offset.add_add, sch₇, k1, k2, tR, k₇.mem, o₆] at o₈
  rw [o₈, VG.Proof.AesSiv.Arm.longVal, Spec.Siv.schedCiph, hK, hj]
  -- The pieces of `P` and of the tail.
  have tk := take_bytesAt s.mem (State.addr P) (a := K) (b := n - K)
  rw [show K + (n - K) = n by omega] at tk
  have tk' := take_bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) (a := 16 * j) (b := n - K - 16 * j)
  rw [show 16 * j + (n - K - 16 * j) = n - K by omega] at tk'
  have dr' := drop_bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) (a := 16 * j) (b := n - K - 16 * j)
  rw [show 16 * j + (n - K - 16 * j) = n - K by omega] at dr'
  rw [tk, tk', dr']

omit L in
theorem outR_oR {out : Nat} : ∀ r ∈ VG.Proof.AesSiv.Arm.outR w sp out, ∃ r' ∈ VG.Proof.AesSiv.Arm.oR w sp out, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨blw sp, by simp, fun _ h => h⟩

/-- S2V's end for a string `P` of a block or more, into `W + out`. -/
theorem long_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (.seq longTail (longMac out)) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (VG.Proof.AesSiv.Arm.oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.longTail_ok L he hP h16 hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, h4₁, f₁, t₁⟩ => ?_)
  have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide) (by decide) (by decide), h6]
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide) (by decide) (by decide), h5]
  refine WP.mono (VG.Proof.AesSiv.Arm.longMac_ok L he₁ hR (hP.of_eq rd₁ wr₁) h16 hn h6₁ h5₁ h4₁ hout)
    fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
  refine ⟨he₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h4 h7 hlr => by rw [g₂ r hr h7 hlr, g₁ r hr h4 hlr],
    (VG.Proof.AesSiv.Arm.frame_oR out f₁).trans (f₂.sub VG.Proof.AesSiv.Arm.outR_oR), ?_⟩
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  have dc : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ VG.Proof.AesSiv.Arm.wR w sp, (⟨State.addr c + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd => VG.Proof.AesSiv.Arm.dis_wR (L.c_w.sub_left (Lay.cSub hd)) (L.stk_c' hd)
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame f₁ (dc hd) (by omega)
  have sch := cK (d := 0) (k := 16 * (R + 1)) (by omega)
  rw [BitVec.add_zero] at sch
  have pP : bytesAt s₁.mem (State.addr P) n = bytesAt s.mem (State.addr P) n :=
    bytesAt_frame f₁ (VG.Proof.AesSiv.Arm.dis_wR hP.w hP.stk) (by omega)
  rw [o₂, VG.Proof.AesSiv.Arm.longVal, Spec.Siv.schedCiph, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide),
    t₁, pP, Spec.Siv.ctxMac, Spec.Siv.schedCiph, show (240 : Addr) = BitVec.ofNat 64 240 from rfl,
    show (256 : Addr) = BitVec.ofNat 64 256 from rfl]
  have hl : 16 ≤ (bytesAt s.mem (State.addr P) n).length := by rw [Proof.Cmac.bytesAt_length]; exact h16
  have ls := long_spec (Spec.Cmac.aesWith R (bytesAt s.mem (State.addr c) (16 * (R + 1))))
    (bytesAt s.mem (State.addr c + BitVec.ofNat 64 240) 16) (bytesAt s.mem (State.addr c + BitVec.ofNat 64 256) 16)
    (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n)
    (Proof.Cmac.bytesAt_length _ _ _) hl
  rw [Proof.Cmac.bytesAt_length s.mem (State.addr P) n] at ls
  exact ls

omit L in
/-- `finish`'s first block: `Z` set iff the string is shorter than a block. -/
theorem finishPre_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s =
      some s₁ ∧ s₁.z = decide (n / 16 = 0) ∧ (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨_, by arun [h5], ?_, ?_, ?_⟩
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, VG.Proof.AesGcm.Arm.shr4 hn]
    exact z_cmp (by omega) (by decide)
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- `finish out`: S2V's end with the string `P` (`n` bytes, in `r6` and
`r5`) from `D`, into `W + out`. -/
theorem finish_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (finish out) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (VG.Proof.AesSiv.Arm.oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  obtain ⟨s₁, run₁, hz₁, g₁, k₁⟩ := VG.Proof.AesSiv.Arm.finishPre_ok hn h5
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  have hP₁ := hP.of_eq k₁.rd k₁.wr
  have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide), h5]
  have gP : ∀ r ∈ preserved, s₁.gpr r = s.gpr r := fun r hr => g₁ r (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [finish]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (VG.Proof.AesSiv.Arm.short_ok L he₁ hR hP₁ (by omega) h6₁ h5₁ hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
    refine ⟨he₂, by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], fun r hr h4 h6 _ hlr => by rw [g₂ r hr h4 h6 hlr, gP r hr],
      by rw [← k₁.mem]; exact f₂, by rw [o₂, k₁.mem]⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.mono (VG.Proof.AesSiv.Arm.long_ok L he₁ hR hP₁ (by omega) hn h6₁ h5₁ hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
    refine ⟨he₂, by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], fun r hr h4 _ h7 hlr => by rw [g₂ r hr h4 h7 hlr, gP r hr],
      by rw [← k₁.mem]; exact f₂, by rw [o₂, k₁.mem]⟩

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Ctr`. -/
section

/-!
# AES-SIV on ARMv7: CTR (`ctr`)

Untrusted: everything here is checked by Lean. `counter 0` sets the counter
block at `W + 96` to `Q`, the IV at `W` with bit 7 of its bytes 8 and 12
cleared (`counter_ok`, `Proof.AesSiv.counter_words4`). `ctrWhole` encrypts
the whole blocks of the data by one call of `vg_aes_ctr32` from `Q`, whose
counters do not wrap around (`Proof.AesSiv.counter_low`,
`Proof.AesSiv.repeat_inc32`), and which leaves `Q + nb` in the counter block
(`ctrWhole_ok`); `ctrTail` XORs the last bytes with the first bytes of the
keystream block of that counter, which `vg_aes_ctr32` computes on a zero
block at `W + 80` (`ctrTail_ok`). Together, CTR's output on the data
(`ctr_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI ctrFrame xorLoop)
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (mem_store store32_eq gpr_store rd_store wr_store sp_store encodable_of_decide sepW
  bytes_words store4_eq add_ofNat_assoc)
open VG.Proof.AesSiv (qm4 orr_eor_80 counter_words4)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame)
open VG.Proof.MdStream.Arm (wp_ldrSp)
open VG.Proof.AesSiv (counter_low)

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-- `counter 0`: `Q` at `W + 96`, from the IV at `W`. -/
theorem counter_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s.mem (State.addr w) 16) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  have w₀ := he.perm.wW (show 96 + 4 ≤ 2576 by decide)
  have w₁ := he.perm.wW (show 100 + 4 ≤ 2576 by decide)
  have w₂ := he.perm.wW (show 104 + 4 ≤ 2576 by decide)
  have w₃ := he.perm.wW (show 108 + 4 ≤ 2576 by decide)
  have q : ∀ a d, a + 4 ≤ d → d + 4 ≤ 2576 →
      (⟨State.addr w + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ => L.w_w (.inl h₁) (by omega) h₂
  have p₁ := fun m v => sepW (m := m) (v := v) (q 4 96 (by decide) (by decide))
  have p₂ := fun m v => sepW (m := m) (v := v) (q 8 96 (by decide) (by decide))
  have p₃ := fun m v => sepW (m := m) (v := v) (q 8 100 (by decide) (by decide))
  have p₄ := fun m v => sepW (m := m) (v := v) (q 12 96 (by decide) (by decide))
  have p₅ := fun m v => sepW (m := m) (v := v) (q 12 100 (by decide) (by decide))
  have p₆ := fun m v => sepW (m := m) (v := v) (q 12 104 (by decide) (by decide))
  have e := fun d (hd : d < 2576) => L.wA (d := d) hd
  let m := s.mem
  let W := State.addr w
  have hm : ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = store4 m (W + BitVec.ofNat 64 96) (m.readW (W + BitVec.ofNat 64 0) 32)
        (m.readW (W + BitVec.ofNat 64 4) 32) ((m.readW (W + BitVec.ofNat 64 8) 32 ||| 0x80#32) ^^^ 0x80#32)
        ((m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80#32) ^^^ 0x80#32) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [counter, cbOff]; arun [h11, e, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃,
      p₄, p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc, m, W]
    · intro r a; simp [gpr_setReg, a]
    all_goals exact ⟨rfl, rfl, rfl⟩
  obtain ⟨s', run, hm', g, rd, wr, sp⟩ := hm
  refine ⟨s', run, ?_, by rw [hm']; exact Proof.Cmac.frame_store4 _ _ _ _ _, g, rd, wr, sp⟩
  rw [hm', Proof.Cmac.bytesAt_store4, orr_eor_80, orr_eor_80, counter_words4, bytes_words]
  simp only [add_ofNat_assoc, BitVec.add_zero, m, W]

omit L in
theorem below_blw (sp : BitVec 32) : Region.Sub (Proof.AesGcm.Arm.below sp) (blw sp) :=
  Offset.sub_below (State.addr sp) (a := 8) (b := 16) (by decide) (by decide)

/-- A call of `vg_aes_ctr32` with `K2`'s schedule, the counter block at
`W + 96`, `n` blocks at `D` and the working space at `W + 256`. -/
theorem ctrCall_of {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32}
    {n : Nat} (h0 : s.gpr .r0 = c + BitVec.ofNat 32 272) (h1 : s.gpr .r1 = BitVec.ofNat 32 R)
    (h2 : s.gpr .r2 = w + BitVec.ofNat 32 cbOff) (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n)
    (hlr : s.gpr .lr = w + BitVec.ofNat 32 256)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (dK : (⟨State.addr c + BitVec.ofNat 64 272, 240⟩ : Region).Disjoint
      ⟨State.addr D, 16 * n⟩)
    (dC : (⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 2048⟩)
    (dB : (blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (wD : Covers [⟨State.addr D, 16 * n⟩] s.wr) :
    Proof.AesGcm.Arm.CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) D (w + BitVec.ofNat 32 256) R n := by
  have eC := L.wA (d := cbOff) (by decide)
  have eS := L.wA (d := 256) (by decide)
  have eK := L.cA (d := 272) (by decide)
  have hsp := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hsp]; have := L.sp16; omega,
    by rw [L.cN (by decide)]; have := L.cw; omega, by rw [L.wN (by decide)]; have := L.ww; simp only [cbOff]; omega, fD,
    by rw [L.wN (by decide)]; have := L.ww; omega, ?_, by rw [eK]; exact dK, ?_, by rw [eC]; exact dC, ?_,
    by rw [eS]; exact dS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eK, eC]; exact L.c_w' (by decide) (by decide)
  · rw [eK, eS]; exact L.c_w' (by decide) (by decide)
  · rw [eC, eS]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [hsp, eK]; exact (L.stk_c' (by decide)).sub_left (VG.Proof.AesSiv.Arm.below_blw sp)
  · rw [hsp, eC]; exact (L.stk_w' (by decide)).sub_left (VG.Proof.AesSiv.Arm.below_blw sp)
  · rw [hsp]; exact dB.sub_left (VG.Proof.AesSiv.Arm.below_blw sp)
  · rw [hsp, eS]; exact (L.stk_w' (by decide)).sub_left (VG.Proof.AesSiv.Arm.below_blw sp)
  · rw [eK]; exact he.perm.cC (by decide)
  · rw [eC, eS]
    exact Proof.AesGcm.Arm.covers_cons (he.perm.wC (by decide))
      (Proof.AesGcm.Arm.covers_cons wD (he.perm.wC (by decide)))

/-- The data: `n` bytes at `D` that the code may write. -/
abbrev ctrR (w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩, VG.Proof.AesSiv.Arm.scrR w, blw sp, ⟨State.addr D, n⟩]

omit L in
theorem split16_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 32 (n / 16) ∧ s₁.z = decide (n / 16 = 0) ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Proof.AesGcm.Arm.Keeps s s₁ := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, Proof.AesGcm.Arm.shr4 hn]
  · simp only [Proof.AesGcm.Arm.z_subFlags, gpr_setReg, Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false,
      reduceCtorEq, h5, Proof.AesGcm.Arm.shr4 hn]
    exact Proof.AesGcm.Arm.z_cmp (by omega) (by decide)
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩


/-- The arguments of the call in `ctrWhole`. -/
theorem ctrWholeArgs_ok {s₀ s₁ : State} (he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32}
    {n : Nat} (hD : VG.Proof.AesSiv.Arm.Dat c w sp s₀ D n) (h6₁ : s₁.gpr .r6 = D) (hwr : s₁.wr = s₀.wr)
    (h12₁ : s₁.gpr .r12 = BitVec.ofNat 32 (n / 16)) :
    ∃ s₂, runBlock isa (ctrArgs ++ [mov .r3 .r6]) s₁ = some s₂ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧
      Proof.AesGcm.Arm.Keeps s₁ s₂ ∧
      Proof.AesGcm.Arm.CtrCall s₂ (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) D
        (w + BitVec.ofNat 32 256) R (n / 16) := by
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hdb := hD.buf.take hb
  refine ⟨_, by simp only [ctrArgs, cbOff, csOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11], ?_⟩
  refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e => by simp [gpr_setReg, a, b, c', d, e], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine VG.Proof.AesSiv.Arm.ctrCall_of L ?_ hR ?_ ?_ ?_ ?_ ?_ ?_ hdb.fit ?_ ?_ ?_ hdb.stk ?_
  · exact he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · simp [gpr_setReg, he₁.r10]
  · simp [gpr_setReg, he₁.r9]
  · simp [gpr_setReg, he₁.r11]
  · simp [gpr_setReg, h6₁]
  · simp [gpr_setReg, h12₁]
  · simp [gpr_setReg, he₁.r11]
  · exact (hD.c.sub_left (Lay.cSub (by decide))).sub_right (Region.sub_prefix hb)
  · exact (hdb.w.sub_right (Lay.wSub (by decide))).symm
  · exact hdb.w.sub_right (Lay.wSub (by decide))
  · simp only [wr_setReg]; rw [hwr]; exact Proof.AesGcm.Arm.covers_prefix hD.wr hb

/-- The whole blocks of the data, from the counter `q` at `W + 96`, whose last
32 bits do not wrap around. -/
theorem ctrWhole_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.Arm.Dat c w sp s D n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    {q : List Byte} (hq : bytesAt s.mem (State.addr w + BitVec.ofNat 64 cbOff) 16 = q)
    (hlow : Spec.Siv.beNat q % 2 ^ 32 + n / 16 + 1 ≤ 2 ^ 32) :
    WP isa ctrWhole s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (VG.Proof.AesSiv.Arm.ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n =
        ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q (bytesAt s.mem (State.addr D) n) (16 * (n / 16)) ∧
      Spec.Gcm.blockAt s'.mem (State.addr w + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
  have hql : q.length = 16 := by rw [← hq, Proof.Cmac.bytesAt_length]
  have hinc := repeat_inc32 hql (k := n / 16 + 1) (by omega)
  have eC := L.wA (d := cbOff) (by decide)
  have hcb : Spec.Gcm.blockAt s.mem (State.addr w + BitVec.ofNat 64 cbOff) = Spec.Gcm.ofBytes q := by
    rw [Spec.Gcm.blockAt, hq]
  obtain ⟨s₁, run₁, h12₁, hz, g₁, k₁⟩ := VG.Proof.AesSiv.Arm.split16_ok hn h5
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hlen := Proof.Cmac.bytesAt_length s.mem (State.addr D) n
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun _ => WP.block_nil ?_)
      (fun h => by cases h)
    refine ⟨he₁, k₁.rd, k₁.wr, fun r _ _ => g₁ r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at *
        rintro rfl; simp_all), by rw [k₁.mem]; exact Frame.refl _ _, ?_, ?_⟩
    · rw [k₁.mem, h0, Nat.mul_zero, ctrPart_zero]
    · rw [k₁.mem, hcb, h0, Nat.add_zero]
      have := hinc 0 (by omega)
      rw [Nat.add_zero] at this
      exact this
  · refine WP.ite false (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun h => by cases h) fun _ => ?_
    have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
    have hdb := hD.buf.take hb
    obtain ⟨s₂, run₂, he₂, g₂, k₂, C⟩ := VG.Proof.AesSiv.Arm.ctrWholeArgs_ok L he₁ hR hD (by rw [g₁ _ (by decide), h6])
      (by rw [k₁.wr]) h12₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.mono (Proof.AesGcm.Arm.ctr_call C) fun s₃ h₃ => ?_
    have hsp₂ : s₂.sp = sp := he₂.sp
    have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
    have eK := L.cA (d := 272) (by decide)
    have eS := L.wA (d := 256) (by decide)
    have f₃ := h₃.frame
    rw [eC, eS, hsp₂] at f₃
    have mem₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
    have fT : Frame (VG.Proof.AesSiv.Arm.ctrR w sp D n) s.mem s₃.mem := by
      rw [← mem₂]
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨⟨State.addr D, n⟩, by simp, Region.sub_prefix hb⟩
        · exact ⟨VG.Proof.AesSiv.Arm.scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨blw sp, by simp, VG.Proof.AesSiv.Arm.below_blw sp⟩
    refine ⟨he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr, by rw [h₃.rd, k₂.rd, k₁.rd],
      by rw [h₃.wr, k₂.wr, k₁.wr], fun r hr hlr => ?_, fT, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 hlr, g₁ r a.2.2.2.2]
    · -- The whole blocks, then the rest as it was.
      have hc := ctr32_ctrPart (m := s₂.mem) (m' := s₃.mem) (K := State.addr (c + BitVec.ofNat 32 272))
        (C := State.addr (w + BitVec.ofNat 32 cbOff)) (D := State.addr D) (R := R) (q := q) (k := n / 16)
        (fun i hi => by rw [eC, mem₂, hcb]; exact hinc i (by omega)) h₃.out
      have e := Proof.Cmac.Stream.bytesAt_append s₃.mem (State.addr D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e
      have e₀ := Proof.Cmac.Stream.bytesAt_append s.mem (State.addr D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e₀
      have rest : bytesAt s₃.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
          bytesAt s.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
        rw [← mem₂]
        refine bytesAt_frame f₃ (fun r hr => ?_) (by have := hD.buf.lt; omega)
        have hsub : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩
            ⟨State.addr D, n⟩ := Offset.sub_base _ (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ((hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide)))
        · exact (Offset.base_disjoint (State.addr D) (e := 16 * (n / 16)) (n := n - 16 * (n / 16))
            (k := 16 * (n / 16)) (by omega) (by have := hD.buf.lt; omega)).symm
        · exact ((hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide)))
        · exact (hD.buf.stk.sub_right hsub).symm.sub_right (VG.Proof.AesSiv.Arm.below_blw sp)
      have hpa := ctrPart_append (Spec.Siv.ctxCiph s.mem (State.addr c) R) q
        (bytesAt s.mem (State.addr D) (16 * (n / 16)))
        (bytesAt s.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)))
      rw [Proof.Cmac.bytesAt_length] at hpa
      rw [e, hc, rest, e₀, hpa, eK, mem₂]
      rfl
    · have := h₃.ctr
      rw [eC, mem₂, hcb] at this
      rw [this]
      exact hinc (n / 16) (by omega)

/-- The keystream block zeroed, and the arguments of the call in `ctrTail`. -/
theorem ctrTailArgs_ok {s₁ : State} (he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.block (zero16 ksOff ++ ctrArgs ++ [addI .r3 .r11 ksOff, .mov .r12 (imm 1)])) s₁ fun s₂ =>
      VG.Proof.AesSiv.Arm.Env c w sp R s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp ∧
      s₂.mem = Proof.Cmac.zero4 s₁.mem (State.addr w + BitVec.ofNat 64 ksOff) ∧
      Proof.AesGcm.Arm.CtrCall s₂ (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) (w + BitVec.ofNat 32 ksOff)
        (w + BitVec.ofNat 32 256) R 1 := by
  rw [List.append_assoc]
  refine VG.Proof.AesSiv.Arm.zero16_ok L he₁ (d := ksOff) (by decide) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have he₂ : VG.Proof.AesSiv.Arm.Env c w sp R s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₂ _ (by decide)) sp₂ rd₂ wr₂
  have eK := L.wA (d := ksOff) (by decide)
  refine WP.of_runBlock ⟨_, by simp only [ctrArgs, cbOff, csOff, ksOff, mov]; arun [he₂.r9, he₂.r10, he₂.r11], ?_⟩
  refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp only [gpr_setReg, a, b, c', d, e, f, ite_false, reduceCtorEq]; rw [g₂ r e],
    by simp [rd_setReg, rd₂], by simp [wr_setReg, wr₂], by simp [sp_setReg, sp₂], by simp [mem_setReg, m₂], ?_⟩
  refine VG.Proof.AesSiv.Arm.ctrCall_of L ?_ hR ?_ ?_ ?_ ?_ ?_ ?_ (by rw [L.wN (by decide)]; have := L.ww; simp only [ksOff]; omega)
    ?_ ?_ ?_ ?_ ?_
  · exact he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · simp [gpr_setReg, he₂.r10]
  · simp [gpr_setReg, he₂.r9]
  · simp [gpr_setReg, he₂.r11]
  · simp [gpr_setReg, he₂.r11]
  · simp [gpr_setReg]
  · simp [gpr_setReg, he₂.r11]
  · rw [eK]; exact L.c_w' (by decide) (by decide)
  · rw [eK]; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · rw [eK]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eK]; exact L.stk_w' (by decide)
  · rw [eK]; simp only [wr_setReg]; exact he₂.perm.wC (by decide)

omit L in
/-- `ctrTail`'s first block: the number of last bytes in `r4`, and `Z` set
iff there are none. -/
theorem tailPre_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.dp .and .r4 .r5 (imm 15), .cmp .r4 (imm 0)] s =
      some s₁ ∧ s₁.gpr .r4 = BitVec.ofNat 32 (n % 16) ∧ s₁.z = decide (n % 16 = 0) ∧
      (∀ r, r ≠ .r4 → s₁.gpr r = s.gpr r) ∧ Proof.AesGcm.Arm.Keeps s s₁ := by
  have hand := Proof.AesGcm.Arm.and15 (BitVec.ofNat 32 n)
  rw [Proof.AesGcm.Arm.toNat32 hn] at hand
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, imm, hand]
  · simp only [Proof.AesGcm.Arm.z_subFlags, gpr_setReg, Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false,
      reduceCtorEq, h5, imm, hand]
    exact Proof.AesGcm.Arm.z_cmp (by omega) (by decide)
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The last bytes of the data, XORed with the keystream block of the counter
`Q + nb` that `ctrWhole` left. -/
theorem ctrTail_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.Arm.Dat c w sp s D n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    {q x : List Byte} (hx : x.length = n)
    (hcb : Spec.Gcm.blockAt s.mem (State.addr w + BitVec.ofNat 64 cbOff) =
      Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)))
    (hd : bytesAt s.mem (State.addr D) n = ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q x (16 * (n / 16))) :
    WP isa ctrTail s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (VG.Proof.AesSiv.Arm.ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n = ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q x n := by
  obtain ⟨s₁, run₁, h4₁, hz, g₁, k₁⟩ := VG.Proof.AesSiv.Arm.tailPre_ok hn h5
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n % 16 = 0
  · refine WP.ite true (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun _ => WP.block_nil ?_)
      (fun h => by cases h)
    refine ⟨he₁, k₁.rd, k₁.wr, fun r _ h4 _ => g₁ r h4, by rw [k₁.mem]; exact Frame.refl _ _, ?_⟩
    rw [k₁.mem, hd, show 16 * (n / 16) = n by omega]
  · refine WP.ite false (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.ctrTailArgs_ok L he₁ hR) fun s₂ ⟨he₂, g₂, rd₂, wr₂, sp₂, m₂, C⟩ => ?_)
    refine WP.seq (WP.mono (Proof.AesGcm.Arm.ctr_call C) fun s₃ h₃ => ?_)
    have he₃ := he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr
    have hsp₂ : s₂.sp = sp := he₂.sp
    have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
    have hb : 16 * (n / 16) < n := by omega
    have eC := L.wA (d := cbOff) (by decide)
    have eK := L.wA (d := ksOff) (by decide)
    have eS := L.wA (d := 256) (by decide)
    have eCK := L.cA (d := 272) (by decide)
    have g₃ : ∀ r ∈ preserved, r ≠ .lr → s₃.gpr r = s₁.gpr r := fun r hr hlr => by
      have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
    have h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 (n % 16) := by rw [g₃ _ (by decide) (by decide), h4₁]
    have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), h5]
    have h6₃ : s₃.gpr .r6 = D := by rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), h6]
    -- The keystream block.
    have hdata : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩ :=
      hD.buf.w.sub_right (Lay.wSub (by decide))
    have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 ksOff, 16⟩] s.mem s₂.mem := by
      rw [m₂, k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have cb₂ : Spec.Gcm.blockAt s₂.mem (State.addr w + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
      rw [Spec.Gcm.blockAt, bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), ← Spec.Gcm.blockAt, hcb]
    have sch₂ : bytesAt s₂.mem (State.addr c + BitVec.ofNat 64 272) (16 * (R + 1)) =
        bytesAt s.mem (State.addr c + BitVec.ofNat 64 272) (16 * (R + 1)) :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' (by omega) (by decide)) (by omega)
    have hks : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 ksOff) 16 =
        Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (State.addr c) R) q (n / 16) := by
      have hx₃ := Proof.AesCcm.ctr32_bytes (m := s₂.mem) (m' := s₃.mem) (C := State.addr (w + BitVec.ofNat 32 cbOff))
        (D := State.addr (w + BitVec.ofNat 32 ksOff)) (nb := 1) h₃.out
      rw [Nat.mul_one, eK, eC, m₂, Proof.Cmac.zero4_bytes, ← m₂, cb₂, xorKs_zeros, eCK, sch₂,
        Proof.Cmac.aesWith_bytes _ _ (length_be128 _)] at hx₃
      rw [hx₃]; rfl
    -- The arguments of the XOR.
    have eD := hD.buf.addr (j := 16 * (n / 16)) hb
    obtain ⟨s₄, run₄, a1₄, a2₄, a3₄, g₄, k₄⟩ : ∃ s₄, runBlock isa [addI .r1 .r11 ksOff, .dp .sub .r2 .r5 (.reg .r4),
        .dp .add .r2 .r2 (.reg .r6), mov .r3 .r4] s₃ = some s₄ ∧
        s₄.gpr .r1 = w + BitVec.ofNat 32 ksOff ∧ s₄.gpr .r2 = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
        s₄.gpr .r3 = BitVec.ofNat 32 (n % 16) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₄.gpr r = s₃.gpr r) ∧ Proof.AesGcm.Arm.Keeps s₃ s₄ := by
      have hsub : BitVec.ofNat 32 n - BitVec.ofNat 32 (n % 16) = BitVec.ofNat 32 (16 * (n / 16)) := by
        rw [Proof.AesGcm.Arm.ofNat_sub32 (Nat.mod_le _ _) hn]; congr 1; omega
      refine ⟨_, by simp only [ksOff, mov]; arun [he₃.r11], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, he₃.r11]
      · simp [gpr_setReg, h4₃, h5₃, h6₃, hsub, BitVec.add_comm]
      · simp [gpr_setReg, h4₃]
      · intro r a b c'; simp [gpr_setReg, a, b, c']
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    have hT := hD.buf.sub (j := 16 * (n / 16)) (k := n % 16) (by omega) (by omega)
    have wr₄ : s₄.wr = s.wr := by rw [k₄.wr, h₃.wr, wr₂, k₁.wr]
    have rd₄ : s₄.rd = s.rd := by rw [k₄.rd, h₃.rd, rd₂, k₁.rd]
    have lp : Proof.AesGcm.Arm.LoopPre s₄ (w + BitVec.ofNat 32 ksOff) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨a1₄, a2₄, a3₄, by omega, by omega, by rw [L.wN (by decide)]; have := L.ww; simp only [ksOff]; omega,
        hT.fit, ?_, ?_, ?_⟩
      · rw [eK, rd₄, wr₄]; exact Proof.AesGcm.Arm.covers_left (he.perm.wC (by simp only [ksOff]; omega))
      · rw [wr₄, eD]; exact Proof.AesGcm.Arm.covers_off hD.wr (by omega) hD.buf.lt
      · rw [eK]; exact (hT.w.sub_right (Lay.wSub (by simp only [ksOff]; omega))).symm
    refine WP.mono (Proof.AesGcm.Arm.xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
    rw [eK, eD] at hm₅
    have hxl : (Proof.AesGcm.Arm.xorBytes s₄.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16)))
        (State.addr w + BitVec.ofNat 64 ksOff) (n % 16)).length = n % 16 := Proof.AesGcm.Arm.length_xorBytes _ _ _ _
    -- What was written before the XOR.
    have f₂₃ : Frame [⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩, VG.Proof.AesSiv.Arm.scrR w, blw sp] s₂.mem s₃.mem := by
      have fc := h₃.frame
      rw [hsp₂, eC, eK, eS] at fc
      exact fc.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨VG.Proof.AesSiv.Arm.scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨blw sp, by simp, VG.Proof.AesSiv.Arm.below_blw sp⟩
    have f₀₄ : Frame [⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩, VG.Proof.AesSiv.Arm.scrR w, blw sp] s.mem s₄.mem := by
      rw [k₄.mem]
      exact (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans f₂₃
    have fw : Frame [⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] s₄.mem s₅.mem := by
      rw [hm₅]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;>
          rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
            g₄ _ (by decide) (by decide) (by decide)]) (lo.sp.trans k₄.sp) (lo.rd.trans k₄.rd) (lo.wr.trans k₄.wr),
      by rw [lo.rd, rd₄], by rw [lo.wr, wr₄], fun r hr h4 hlr => ?_, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [lo.other r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2, g₄ r a.2.1 a.2.2.1 a.2.2.2.1, g₃ r hr hlr, g₁ r h4]
    · refine (f₀₄.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr D, n⟩, by simp, Offset.sub_base _ (by omega)⟩
    · have hc : ∀ y, (Spec.Siv.ctxCiph s.mem (State.addr c) R y).length = 16 :=
        fun y => Proof.Cmac.aesWith_length _ _ y
      have d₄ : bytesAt s₄.mem (State.addr D) x.length = ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q x
          (16 * (n / 16)) := by
        rw [hx, bytesAt_frame f₀₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hdata
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.stk.symm) (by have := hD.buf.lt; omega), hd]
      have st := ctrPart_step (Spec.Siv.ctxCiph s.mem (State.addr c) R) hc q x s₄.mem (State.addr D)
        (i := n / 16) (n := n % 16) (by have := hD.buf.lt; omega) (by omega) (by omega) d₄
      have xb : Proof.AesGcm.Arm.xorBytes s₄.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16)))
          (State.addr w + BitVec.ofNat 64 ksOff) (n % 16) =
          Spec.Cmac.xor (bytesAt s₄.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
            ((Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (State.addr c) R) q (n / 16)).take (n % 16)) := by
        rw [Proof.AesGcm.Arm.xorBytes, Proof.AesCcm.bytesAt_prefix s₄.mem (State.addr w + BitVec.ofNat 64 ksOff)
          (show n % 16 ≤ 16 by omega), k₄.mem, hks]
        rfl
      rw [hx] at st
      rw [hm₅, xb, st, show 16 * (n / 16) + n % 16 = n by omega]

/-- CTR's first block: the counter `Q` at `W + 96`, and the data's address
and length in `r6` and `r5`. -/
theorem ctrPre_ok {s : State} (he : Env c w sp R s) {D : BitVec 32} {n : Nat}
    (hD : Dat c w sp s D n) (hfit : sp.toNat + 16 ≤ 2 ^ 32)
    (hA : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)) (hAw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩)
    (hm0 : s.mem.readW (State.addr sp) 32 = D)
    (hm1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n) :
    WP isa (.block (counter 0 ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) s fun s₃ => VG.Proof.AesSiv.Arm.Env c w sp R s₃ ∧ VG.Proof.AesSiv.Arm.Dat c w sp s₃ D n ∧
      s₃.gpr .r6 = D ∧ s₃.gpr .r5 = BitVec.ofNat 32 n ∧
      (∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s.mem (State.addr w) 16) := by
  obtain ⟨s₁, run₁, hq₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := VG.Proof.AesSiv.Arm.counter_ok L he
  have he₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  have hsp₁ : s₁.sp = sp := he₁.sp
  have dA : ∀ {d : Nat}, d + 4 ≤ 16 → ∀ r ∈ [(⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩ : Region)],
      (⟨State.addr sp + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hAw.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub (by decide))
  have a0 : State.addr (s₁.sp + BitVec.ofNat 32 0) = State.addr sp + BitVec.ofNat 64 0 := by
    rw [hsp₁]; exact addr_add (by omega)
  have a4 : State.addr (sp + BitVec.ofNat 32 4) = State.addr sp + BitVec.ofNat 64 4 := addr_add (by omega)
  have v0 : s₁.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [f₁.readW (Region.contains_self _ _) (dA (d := 0) (by decide)) (by decide), BitVec.add_zero, hm0]
  have v4 : s₁.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₁.readW (Region.contains_self _ _) (dA (d := 4) (by decide)) (by decide), hm1]
  have i0 : InRegions (s₁.rd ++ s₁.wr) (State.addr sp + BitVec.ofNat 64 0) 4 := by
    rw [rd₁, wr₁]; exact Proof.AesGcm.Arm.in_off hA (by decide) (by decide)
  have i4 : InRegions (s₁.rd ++ s₁.wr) (State.addr sp + BitVec.ofNat 64 4) 4 := by
    rw [rd₁, wr₁]; exact Proof.AesGcm.Arm.in_off hA (by decide) (by decide)
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine wp_ldrSp (by decide) a0 i0 fun s₂ u₂ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide) (by rw [u₂.sp, hsp₁]; exact a4)
    (by rw [u₂.rd, u₂.wr]; exact i4) fun s₃ u₃ =>
    WP.block_nil ?_
  have he₃ : VG.Proof.AesSiv.Arm.Env c w sp R s₃ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [u₃.other _ (by decide), u₂.other _ (by decide)])
    (by rw [u₃.sp, u₂.sp]) (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr])
  have h6₃ : s₃.gpr .r6 = D := by rw [u₃.other _ (by decide), u₂.gpr, v0]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by rw [u₃.gpr, u₂.mem, v4]
  have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
  have hD₃ : VG.Proof.AesSiv.Arm.Dat c w sp s₃ D n := hD.of_eq (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁])
  exact ⟨he₃, hD₃, h6₃, h5₃, fun r h0 h5 h6 => by rw [u₃.other r h5, u₂.other r h6, g₁ r h0],
    by rw [u₃.rd, u₂.rd, rd₁], by rw [u₃.wr, u₂.wr, wr₁], by rw [m₃]; exact f₁, by rw [m₃]; exact hq₁⟩

/-- `ctr 0`: the data (`n` bytes at `D`, its address and length at `sp` and
`sp + 4`) XORed with CTR's keystream from the IV at `W` with two bits cleared. -/
theorem ctr_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat}
    (hD : Dat c w sp s D n) (hn : n < 2 ^ 32) (hfit : sp.toNat + 16 ≤ 2 ^ 32)
    (hA : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)) (hAw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩)
    (hm0 : s.mem.readW (State.addr sp) 32 = D)
    (hm1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n) :
    WP isa (VG.Impl.AesSiv.Arm.ctr 0) s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n ∧
      Frame (VG.Proof.AesSiv.Arm.ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n =
        Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R) (Spec.Siv.counter (bytesAt s.mem (State.addr w) 16))
          (bytesAt s.mem (State.addr D) n) := by
  rw [VG.Impl.AesSiv.Arm.ctr]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.ctrPre_ok L he hD hfit hA hAw hm0 hm1)
    fun s₃ ⟨he₃, hD₃, h6₃, h5₃, g₃, rd₃, wr₃, f₁, hq₃⟩ => ?_)
  -- The bounds of the counter.
  have hlow := counter_low (bytesAt s.mem (State.addr w) 16)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.ctrWhole_ok L he₃ hR hD₃ hn h6₃ h5₃
    (q := Spec.Siv.counter (bytesAt s.mem (State.addr w) 16)) hq₃ (by omega))
    fun s₄ ⟨he₄, rd₄, wr₄, g₄, f₄, d₄, cb₄⟩ => ?_)
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  have dcR : ∀ r ∈ VG.Proof.AesSiv.Arm.ctrR w sp D n, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
    · exact hD.c
  have k₄ : Spec.Siv.ctxCiph s₄.mem (State.addr c) R = Spec.Siv.ctxCiph s₃.mem (State.addr c) R :=
    VG.Proof.AesSiv.Arm.ctxCiph_frame f₄ dcR hRb
  have h6₄ : s₄.gpr .r6 = D := by rw [g₄ _ (by decide) (by decide), h6₃]
  have h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [g₄ _ (by decide) (by decide), h5₃]
  refine WP.mono (VG.Proof.AesSiv.Arm.ctrTail_ok L he₄ hR (hD₃.of_eq rd₄ wr₄) hn h6₄ h5₄ (x := bytesAt s₃.mem (State.addr D) n)
    (Proof.Cmac.bytesAt_length _ _ _) cb₄ (by rw [k₄]; exact d₄)) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, d₅⟩ => ?_
  have f₀₁ : Frame (VG.Proof.AesSiv.Arm.ctrR w sp D n) s.mem s₃.mem := by
    exact f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
  refine ⟨he₅, by rw [rd₅, rd₄, rd₃], by rw [wr₅, wr₄, wr₃],
    fun r hr h4 h5 h6 hlr => ?_, by rw [g₅ _ (by decide) (by decide) (by decide), h6₄],
    by rw [g₅ _ (by decide) (by decide) (by decide), h5₄], f₀₁.trans (f₄.trans f₅), ?_⟩
  · have h0 : r ≠ .r0 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₅ r hr h4 hlr, g₄ r hr hlr, g₃ r h0 h5 h6]
  · have c₃ : Spec.Siv.ctxCiph s₃.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
      VG.Proof.AesSiv.Arm.ctxCiph_frame f₀₁ dcR hRb
    have b₃ : bytesAt s₃.mem (State.addr D) n = bytesAt s.mem (State.addr D) n := by
      exact bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hD.buf.w.sub_right (Lay.wSub (by decide)))
        (by have := hD.buf.lt; omega)
    rw [d₅, k₄, c₃, b₃]
    exact ctrPart_all (Spec.Siv.ctxCiph s.mem (State.addr c) R) (fun y => Proof.Cmac.aesWith_length _ _ y) _ _
      (by rw [Proof.Cmac.bytesAt_length])

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Start`. -/
section

/-!
# AES-SIV on ARMv7: the entry, and S2V's first state

Untrusted: everything here is checked by Lean. `encrypt` and `decrypt` take
the key context in `r0`, the rounds in `r1`, the descriptors in `r2` and
their number in `r3`, and the data, its length, `siv` and `W` on the stack
(`EPre`). They save our caller's registers in `W` where AES-GCM does
(`Proof.AesGcm.Arm.save_ok`), keep their arguments in registers, zero the
block at `W + 16` and `D`, and finalize the zero block into `D`:
`D = AES-CMAC(K1, <zero>)` (`start_ok`), S2V's first state.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI save)
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR save_ok covers_left covers_prefix in_off)
open VG.Proof.MdStream.Arm (wp_ldrSp)

/-- What `encrypt` and `decrypt` need of their arguments: the key context
`c`, the rounds `R`, the `N` descriptors at `a`, the data (`n` bytes at `D`),
`siv` (16 bytes at `T`, which they may at least read) and `W`, the last four
on the stack at `sp`. -/
structure EPre (c w sp a D T : BitVec 32) (R N n : Nat) (s : State) : Prop where
  lay : Lay c w sp
  perm : Perm c w s
  r0 : s.gpr .r0 = c
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = a
  r3 : s.gpr .r3 = BitVec.ofNat 32 N
  hsp : s.sp = sp
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  afit : sp.toNat + 16 ≤ 2 ^ 32
  args : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)
  args_w : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  args_d : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩
  a0 : s.mem.readW (State.addr sp) 32 = D
  a1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  a2 : s.mem.readW (State.addr sp + BitVec.ofNat 64 8) 32 = T
  a3 : s.mem.readW (State.addr sp + BitVec.ofNat 64 12) 32 = w
  ads : Ads w sp a N s.mem s
  data : Dat c w sp s D n
  n32 : n < 2 ^ 32
  tfit : T.toNat + 16 ≤ 2 ^ 32
  t_rd : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  t_stk : (blw sp).Disjoint ⟨State.addr T, 16⟩

/-- The descriptors as they were, after writes apart from them. -/
theorem Ads.of_frame {w sp a : BitVec 32} {N : Nat} {m m' : Mem} {s : State} (h : VG.Proof.AesSiv.Arm.Ads w sp a N m s)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r) :
    VG.Proof.AesSiv.Arm.Ads w sp a N m' s := by
  have e : ∀ i < N, ∀ j < 2, VG.Proof.AesSiv.Arm.descW m' a i j = VG.Proof.AesSiv.Arm.descW m a i j := fun i hi j hj =>
    hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)
  exact { h with comp := fun i hi => by rw [e i hi 0 (by decide), e i hi 1 (by decide)]; exact h.comp i hi }

/-- The components as they were, after writes apart from them. -/
theorem components_frame {a : BitVec 32} {N : Nat} {m m' : Mem}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r)
    (hc : ∀ i < N, ∀ r ∈ rs, (⟨State.addr (VG.Proof.AesSiv.Arm.descW m a i 0), (VG.Proof.AesSiv.Arm.descW m a i 1).toNat⟩ : Region).Disjoint r) :
    Spec.Siv.components 32 m' (State.addr a) N = Spec.Siv.components 32 m (State.addr a) N := by
  have e : ∀ i < N, ∀ j < 2, VG.Proof.AesSiv.Arm.descW m' a i j = VG.Proof.AesSiv.Arm.descW m a i j := fun i hi j hj =>
    hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)
  apply List.ext_getElem (by rw [VG.Proof.AesSiv.Arm.length_components, VG.Proof.AesSiv.Arm.length_components])
  intro i h₁ h₂
  rw [VG.Proof.AesSiv.Arm.length_components] at h₂
  rw [VG.Proof.AesSiv.Arm.components_getElem m' a h₂, VG.Proof.AesSiv.Arm.components_getElem m a h₂, e i h₂ 0 (by decide), e i h₂ 1 (by decide)]
  exact bytesAt_frame hf (hc i h₂) (by have := (VG.Proof.AesSiv.Arm.descW m a i 1).isLt; omega)

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

theorem saved_wR : ∀ r ∈ VG.Proof.AesSiv.Arm.wR w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (a := 128) (n := 36) (d := 16) (m := 112) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

omit L in
/-- What the entry leaves, before the call of `vg_cmac_aes_finalize` that
computes S2V's first state: the registers saved in the memory `mₛ`, the
zero block at `W + 16` and `D` zeroed, and the arguments of the call. -/
structure Started (c w sp a : BitVec 32) (R N : Nat) (s : State) (mₛ : Mem) (s' : State) : Prop where
  fs : Frame [savedR w] s.mem mₛ
  sv : SavedAt mₛ w s
  env : VG.Proof.AesSiv.Arm.Env c w sp R s'
  r8 : s'.gpr .r8 = a
  r7 : s'.gpr .r7 = BitVec.ofNat 32 N
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (VG.Proof.AesSiv.Arm.wR w sp) mₛ s'.mem
  zD : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 = Spec.Cmac.zeros 16
  zZ : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 zOff) 16 = Spec.Cmac.zeros 16
  args : VG.Proof.AesSiv.Arm.FArgs s' c (w + BitVec.ofNat 32 dOff) (w + BitVec.ofNat 32 zOff) (w + BitVec.ofNat 32 256) 16 R

/-- The entry, up to the call. -/
theorem startBlock_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa (.block (encPre ++ startPre)) s fun s' => ∃ mₛ, Started c w sp a R N s mₛ s' := by
  have ww := L.ww
  have hR := h.rounds
  rw [encPre, List.cons_append]
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 12) (by decide)
    (by rw [h.hsp]; exact addr_add (by have := h.afit; omega)) (in_off h.args (by decide) (by decide))
    fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = w := by rw [u₁.gpr, h.a3]
  simp only [List.append_eq, List.append_assoc]
  refine save_ok h12 (by omega) (by rw [u₁.wr]; exact covers_prefix h.perm.w (by decide))
    fun s₂ g₂ rd₂ wr₂ sp₂ sv₂ f₂ => ?_
  have hrd₂ : s₂.rd = s.rd := by rw [rd₂, u₁.rd]
  have hwr₂ : s₂.wr = s.wr := by rw [wr₂, u₁.wr]
  have hsp₂ : s₂.sp = sp := by rw [sp₂, u₁.sp, h.hsp]
  have gg : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  obtain ⟨s₃, run₃, he₃, h8₃, h7₃, k₃⟩ : ∃ s₃, runBlock isa [mov .r11 .r12, mov .r10 .r0, mov .r9 .r1,
      mov .r8 .r2, mov .r7 .r3] s₂ = some s₃ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₃ ∧ s₃.gpr .r8 = a ∧ s₃.gpr .r7 = BitVec.ofNat 32 N ∧
      Proof.AesGcm.Arm.Keeps s₂ s₃ := by
    have e0 : s₂.gpr .r0 = c := by rw [gg _ (by decide), h.r0]
    have e1 : s₂.gpr .r1 = BitVec.ofNat 32 R := by rw [gg _ (by decide), h.r1]
    have e2 : s₂.gpr .r2 = a := by rw [gg _ (by decide), h.r2]
    have e3 : s₂.gpr .r3 = BitVec.ofNat 32 N := by rw [gg _ (by decide), h.r3]
    have e12 : s₂.gpr .r12 = w := by rw [g₂, h12]
    refine ⟨_, by simp only [mov]; arun [], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e1]
    · simp [gpr_setReg, e0]
    · simp [gpr_setReg, e12]
    · simp [sp_setReg, hsp₂]
    · exact h.perm.of_eq (by simp [rd_setReg, hrd₂]) (by simp [wr_setReg, hwr₂])
    · simp [gpr_setReg, e2]
    · simp [gpr_setReg, e3]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  simp only [startPre, List.append_assoc]
  refine VG.Proof.AesSiv.Arm.zero16_ok L he₃ (d := zOff) (by decide) fun s₄ g₄ m₄ rd₄ wr₄ sp₄ => ?_
  have he₄ : VG.Proof.AesSiv.Arm.Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide)) sp₄ rd₄ wr₄
  refine VG.Proof.AesSiv.Arm.zero16_ok L he₄ (d := dOff) (by decide) fun s₅ g₅ m₅ rd₅ wr₅ sp₅ => ?_
  have he₅ : VG.Proof.AesSiv.Arm.Env c w sp R s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide)) sp₅ rd₅ wr₅
  have eZ := L.wA (d := zOff) (by decide)
  have eD := L.wA (d := dOff) (by decide)
  obtain ⟨s₆, run₆, he₆, g₆, k₆, F⟩ : ∃ s₆, runBlock isa (macArgs dOff ++ [addI .r3 .r11 zOff, .mov .r12 (imm 16)])
      s₅ = some s₆ ∧ VG.Proof.AesSiv.Arm.Env c w sp R s₆ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s₅.gpr r) ∧
      Proof.AesGcm.Arm.Keeps s₅ s₆ ∧
      VG.Proof.AesSiv.Arm.FArgs s₆ c (w + BitVec.ofNat 32 dOff) (w + BitVec.ofNat 32 zOff) (w + BitVec.ofNat 32 256) 16 R := by
    refine ⟨_, by simp only [macArgs, csOff, zOff, dOff]; arun [he₅.r9, he₅.r10, he₅.r11], ?_⟩
    refine ⟨he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine VG.Proof.AesSiv.Arm.fargs_of L ?_ hR (st := dOff) (.inr ⟨by decide, by decide⟩) (n := 16) (by decide)
      (by rw [L.wN (by decide)]; simp only [zOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [eZ]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eZ]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eZ]; exact L.stk_w' (by decide)
    · rw [eZ]; exact covers_left (he₅.perm.wC (by decide))
    · simp [gpr_setReg, he₅.r10]
    · simp [gpr_setReg, he₅.r9]
    · simp [gpr_setReg, he₅.r11]
    · simp [gpr_setReg, he₅.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₅.r11]
  -- What was written after the save.
  have fZ : Frame (VG.Proof.AesSiv.Arm.wR w sp) s₂.mem s₆.mem := by
    rw [k₆.mem, m₅, m₄, k₃.mem]
    refine ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have hgg : ∀ r ∈ [Reg.r7, .r8], s₆.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide),
        g₄ _ (by decide)]
  have f₂' : Frame [savedR w] s.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  refine WP.of_runBlock ⟨s₆, run₆, s₂.mem, f₂', fun p hp => ?_, he₆, by rw [hgg _ (by simp), h8₃],
    by rw [hgg _ (by simp), h7₃], by rw [k₆.rd, rd₅, rd₄, k₃.rd, hrd₂], by rw [k₆.wr, wr₅, wr₄, k₃.wr, hwr₂], fZ,
    ?_, ?_, F⟩
  · have hp' : p.1 ≠ .r12 := by
      simp only [Impl.AesGcm.Arm.saved, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [sv₂ p hp, u₁.other _ hp']
  · rw [k₆.mem, m₅, Proof.Cmac.zero4_bytes]
  · rw [k₆.mem, m₅, Proof.Cmac.zero4, bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (p := State.addr w + BitVec.ofNat 64 zOff)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), m₄, Proof.Cmac.zero4_bytes]

/-- The entry and S2V's first state: from the memory `mₛ` after the save,
`D = AES-CMAC(K1, <zero>)`, before the first component. -/
theorem start_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa (.seq (.block (encPre ++ startPre)) finFrame) s fun s' =>
      ∃ mₛ : Mem, Frame [savedR w] s.mem mₛ ∧ SavedAt mₛ w s ∧ VG.Proof.AesSiv.Arm.AInv c w sp a R N mₛ s 0 s' := by
  have hR := h.rounds
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.startBlock_ok L h) fun s₆ ⟨mₛ, St⟩ => ?_)
  have he₆ := St.env
  have eD := L.wA (d := dOff) (by decide)
  have eZ := L.wA (d := zOff) (by decide)
  refine WP.mono (VG.Proof.AesSiv.Arm.fin_call St.args) fun s₇ h₇ => ?_
  have hb₆ := VG.Proof.AesSiv.Arm.blw16_eq (s := s₆) he₆.sp
  have f₇ := h₇.frame
  rw [eD, L.wA (d := 256) (by decide), hb₆] at f₇
  have f₆₇ : Frame (VG.Proof.AesSiv.Arm.wR w sp) s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨blw sp, by simp, fun _ h => h⟩
  have rd₇ : s₇.rd = s.rd := by rw [h₇.rd, St.rd]
  have wr₇ : s₇.wr = s.wr := by rw [h₇.wr, St.wr]
  refine ⟨mₛ, St.fs, St.sv, ⟨he₆.of_saved h₇.saved h₇.sp h₇.rd h₇.wr, ?_, ?_, ?_, rd₇, wr₇,
    St.frame.trans f₆₇, ?_⟩⟩
  · refine (h.ads.of_frame St.fs (fun r hr => ?_)).of_eq (by rw [rd₇]) (by rw [wr₇])
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.ads.dw.sub_right (Lay.wSub (by decide)))
  · rw [h₇.saved _ (by decide) (by decide), St.r8]; simp
  · rw [h₇.saved _ (by decide) (by decide), St.r7, Nat.sub_zero]
  · have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
    have dcw : ∀ r ∈ VG.Proof.AesSiv.Arm.wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := VG.Proof.AesSiv.Arm.dis_wR L.c_w L.stk_c
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₆.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt mₛ (State.addr c + BitVec.ofNat 64 d) k :=
      bytesAt_frame St.frame (fun r hr => (dcw r hr).sub_left (Lay.cSub hd)) (by omega)
    have sch := cK (d := 0) (k := 16 * (R + 1)) (by omega)
    rw [BitVec.add_zero] at sch
    have o₇ := h₇.out
    rw [eD, eZ, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide), St.zZ, St.zD] at o₇
    rw [o₇, List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil, Spec.Siv.s2vStart, Spec.Siv.ctxMac,
      Spec.Siv.schedCiph, VG.Proof.AesSiv.Arm.cmacWith_one _ _ _ _ (by rfl)]
    rfl

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Seal`. -/
section

/-!
# AES-SIV on ARMv7: `vg_aes_siv_encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves the
registers, sets S2V's first state (`start_ok`), absorbs the components of
associated data (`s2vAds_ok`) and loads the data's address and length
(`s2v_ok`); `encrypt` then finishes S2V with the plaintext into the IV at
`W` (`finish_ok`), encrypts the plaintext with CTR from it (`ctr_ok`), copies
the IV to `siv` (`sivOut_ok`) and restores the registers (`encrypt_wp`):
`encryptWith` of the context's PRF and cipher (`Spec.Siv.encryptWith_eq`).
`decrypt` copies the received IV from `siv` to `W` the same way
(`sivIn_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR restore_ok covers_left covers_prefix in_off sepW
  bytesAt_copy4 store4_eq mem_store add_ofNat_assoc add_ofNat_zero)
open VG.Proof.Cmac (store4)
open VG.Proof.MdStream.Arm (wp_ldrSp)

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-- What `encS2v` leaves: `D` is S2V's state of the components, from the
memory `mₛ` after the save, and the data's address and length in `r6` and
`r5`. -/
structure S2vOut (c w sp a D : BitVec 32) (R N n : Nat) (s : State) (mₛ : Mem) (s' : State) : Prop where
  fs : Frame [savedR w] s.mem mₛ
  sv : SavedAt mₛ w s
  env : VG.Proof.AesSiv.Arm.Env c w sp R s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  r6 : s'.gpr .r6 = D
  r5 : s'.gpr .r5 = BitVec.ofNat 32 n
  frame : Frame (VG.Proof.AesSiv.Arm.wR w sp) mₛ s'.mem
  acc : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N)

theorem s2v_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa encS2v s fun s' => ∃ mₛ, S2vOut c w sp a D R N n s mₛ s' := by
  have hR := h.rounds
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  have hN : N < 2 ^ 32 := by have := h.ads.fit; omega
  have st := WP.seq_iff.mp (VG.Proof.AesSiv.Arm.start_ok L h)
  refine WP.seq (WP.mono st fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono h₁ fun s₂ ⟨mₛ, fs, sv, I₀⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.s2vAds_ok L hR I₀ hN) fun s₃ I => ?_)
  -- The data's address and length.
  have dA : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  have fT : Frame (savedR w :: wR w sp) s.mem s₃.mem :=
    (fs.mono (by simp)).trans (I.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
  have v0 : s₃.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [fT.readW (r := ⟨State.addr sp + BitVec.ofNat 64 0, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), BitVec.add_zero, h.a0]
  have v4 : s₃.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [fT.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  have hsp₃ : s₃.sp = sp := I.env.sp
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp₃]; exact addr_add (by have := h.afit; omega))
    (by rw [I.rd, I.wr]; exact in_off h.args (by decide) (by decide)) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₄.sp, hsp₃]; exact addr_add (by have := h.afit; omega))
    (by rw [u₄.rd, u₄.wr, I.rd, I.wr]; exact in_off h.args (by decide) (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have dc : ∀ r ∈ [savedR w], (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.c0_w' (by decide) (by decide)
  refine ⟨mₛ, fs, sv, I.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₅.other _ (by decide), u₄.other _ (by decide)])
      (by rw [u₅.sp, u₄.sp]) (by rw [u₅.rd, u₄.rd]) (by rw [u₅.wr, u₄.wr]),
    by rw [u₅.rd, u₄.rd, I.rd], by rw [u₅.wr, u₄.wr, I.wr], by rw [u₅.other _ (by decide), u₄.gpr, v0],
    by rw [u₅.gpr, u₄.mem, v4], by rw [u₅.mem, u₄.mem]; exact I.frame, ?_⟩
  rw [u₅.mem, u₄.mem, I.acc, List.take_of_length_le (by rw [VG.Proof.AesSiv.Arm.length_components]), VG.Proof.AesSiv.Arm.ctxMac_frame fs dc hRb,
    VG.Proof.AesSiv.Arm.components_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ads.dw.sub_right (Lay.wSub (by decide)))
      (fun i hi r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.ads.comp i hi).w.sub_right (Lay.wSub (by decide)))]

/-- `sivOut`: the IV at `W` copied to `T`, the stack argument at `[sp + 8]`. -/
theorem sivOut_ok {s : State} (he : Env c w sp R s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 = T)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa sivOut s = some s' ∧ bytesAt s'.mem (State.addr T) 16 = bytesAt s.mem (State.addr w) 16 ∧
      Frame [⟨State.addr T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 2576 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  have w₀ := in_off hTw (show 0 + 4 ≤ 16 by decide) (by decide)
  have w₁ := in_off hTw (show 4 + 4 ≤ 16 by decide) (by decide)
  have w₂ := in_off hTw (show 8 + 4 ≤ 16 by decide) (by decide)
  have w₃ := in_off hTw (show 12 + 4 ≤ 16 by decide) (by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr T + BitVec.ofNat 64 b) v).readW (State.addr w + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr w + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.symm.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa sivOut s = some s' ∧
      s'.mem = store4 s.mem (State.addr T + BitVec.ofNat 64 0) (s.mem.readW (State.addr w + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr w + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [sivOut]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Proof.Cmac.frame_store4 _ _ _ _ _, hg,
    hk.1, hk.2.1, hk.2.2⟩

/-- `sivIn`: the IV at `T`, the stack argument at `[sp + 8]`, copied to `W`. -/
theorem sivIn_ok {s : State} (he : Env c w sp R s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 = T)
    (hTr : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa sivIn s = some s' ∧ bytesAt s'.mem (State.addr w) 16 = bytesAt s.mem (State.addr T) 16 ∧
      Frame [⟨State.addr w, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 2576 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₀ := in_off hTr (show 0 + 4 ≤ 16 by decide) (by decide)
  have r₁ := in_off hTr (show 4 + 4 ≤ 16 by decide) (by decide)
  have r₂ := in_off hTr (show 8 + 4 ≤ 16 by decide) (by decide)
  have r₃ := in_off hTr (show 12 + 4 ≤ 16 by decide) (by decide)
  have w₀ := he.perm.wW (show 0 + 4 ≤ 2576 by decide)
  have w₁ := he.perm.wW (show 4 + 4 ≤ 2576 by decide)
  have w₂ := he.perm.wW (show 8 + 4 ≤ 2576 by decide)
  have w₃ := he.perm.wW (show 12 + 4 ≤ 2576 by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr w + BitVec.ofNat 64 b) v).readW (State.addr T + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr T + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa sivIn s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 0) (s.mem.readW (State.addr T + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr T + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr T + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr T + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [sivIn]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Proof.Cmac.frame_store4 _ _ _ _ _, hg,
    hk.1, hk.2.1, hk.2.2⟩

/-- `vg_aes_siv_encrypt`: the synthetic IV at `T` and the ciphertext in place. -/
theorem encrypt_wp {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩) :
    WP isa encrypt s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.ctxCiph s.mem (State.addr c) R)
          (Spec.Siv.components 32 s.mem (State.addr a) N) (bytesAt s.mem (State.addr D) n) =
        (bytesAt s'.mem (State.addr T) 16, bytesAt s'.mem (State.addr D) n) := by
  have hR := h.rounds
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  have ww := L.ww
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.s2v_ok L h) fun s₁ ⟨mₛ, O⟩ => ?_)
  have hD₁ : VG.Proof.AesSiv.Arm.Dat c w sp s₁ D n := h.data.of_eq O.rd O.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.finish_ok L O.env hR hD₁.buf h.n32 O.r6 O.r5 (out := 0) (.inl rfl))
    fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_)
  -- The memory before CTR.
  have f₀₁ : Frame (savedR w :: oR w sp 0) s.mem s₁.mem :=
    (O.fs.mono (by simp)).trans ((frame_oR 0 O.frame).mono fun r hr => List.mem_cons_of_mem _ hr)
  have f₀₂ : Frame (savedR w :: oR w sp 0) s.mem s₂.mem :=
    (O.fs.mono (by simp)).trans (((frame_oR 0 O.frame).trans f₂).mono fun r hr => List.mem_cons_of_mem _ hr)
  have dA : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  have dD : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.stk.symm
  have dc : ∀ r ∈ savedR w :: VG.Proof.AesSiv.Arm.oR w sp 0, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  have hm0 : s₂.mem.readW (State.addr sp) 32 = D := by
    rw [f₀₂.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.a0]
  have hm1 : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₀₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  have hD₂ : VG.Proof.AesSiv.Arm.Dat c w sp s₂ D n := hD₁.of_eq rd₂ wr₂
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.ctr_ok L he₂ hR hD₂ h.n32 h.afit (by rw [rd₂, wr₂, O.rd, O.wr]; exact h.args) h.args_w
    hm0 hm1) fun s₃ ⟨he₃, rd₃, wr₃, g₃, h6₃, h5₃, f₃, d₃⟩ => ?_)
  -- The saved registers are where the save put them.
  have dS : ∀ r ∈ VG.Proof.AesSiv.Arm.ctrR w sp D n, (savedR w).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  have sv₃ : SavedAt s₃.mem w s := (O.sv.frame ((VG.Proof.AesSiv.Arm.frame_oR 0 O.frame).trans f₂) fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact saved_wR L r hr).frame f₃ dS
  -- The IV copied to `siv`.
  have eA : ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
    · exact h.args_d
  have a8 : State.addr (s₃.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [he₃.sp]; exact addr_add (by have := h.afit; omega)
  have v8 : s₃.mem.readW (State.addr (s₃.sp + BitVec.ofNat 32 8)) 32 = T := by
    rw [a8, f₃.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide),
      f₀₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a2]
  have i8 : InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.sp + BitVec.ofNat 32 8)) 4 := by
    rw [a8, rd₃, wr₃, rd₂, wr₂, O.rd, O.wr]
    exact in_off h.args (by decide) (by decide)
  obtain ⟨s₄, run₄, iv₄, fo₄, g₄, rd₄, wr₄, sp₄⟩ := sivOut_ok L he₃ i8 v8
    (by rw [wr₃, wr₂, O.wr]; exact hTw) h.tfit (h.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) sp₄ rd₄ wr₄
  have sv₄ : SavedAt s₄.mem w s := sv₃.frame fo₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (restore_ok (s₀ := s) he₄.r11 (by omega)
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, O.rd, O.wr]; exact covers_left (covers_prefix h.perm.w (by decide)))
    sv₄ (by rw [he₄.sp, h.hsp])) fun s₅ ⟨ab, m₅, _, _, _⟩ => ⟨ab, ?_⟩
  have pD : bytesAt s₄.mem (State.addr D) n = bytesAt s₃.mem (State.addr D) n :=
    bytesAt_frame fo₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd.symm)
      (by have := h.data.buf.lt; omega)
  -- The values.
  have dW : ∀ r ∈ VG.Proof.AesSiv.Arm.ctrR w sp D n, (⟨State.addr w, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
    · exact (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  have iv : bytesAt s₃.mem (State.addr w) 16 = bytesAt s₂.mem (State.addr w) 16 :=
    bytesAt_frame f₃ dW (by decide)
  have mac₁ : Spec.Siv.ctxMac s₁.mem (State.addr c) R = Spec.Siv.ctxMac s.mem (State.addr c) R :=
    VG.Proof.AesSiv.Arm.ctxMac_frame f₀₁ dc hRb
  have ciph₂ : Spec.Siv.ctxCiph s₂.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
    VG.Proof.AesSiv.Arm.ctxCiph_frame f₀₂ dc hRb
  have p₁ : bytesAt s₁.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₁ dD
      (by have := h.data.buf.lt; omega)
  have p₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₂ dD (by have := h.data.buf.lt; omega)
  rw [BitVec.add_zero] at o₂
  rw [m₅, iv₄, pD, Spec.Siv.encryptWith_eq, Spec.Siv.sealWith, d₃, iv, o₂, mac₁, O.acc, p₁, ciph₂, p₂]

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Open`. -/
section

/-!
# AES-SIV on ARMv7: `vg_aes_siv_decrypt`

Untrusted: everything here is checked by Lean. `decrypt` runs S2V over the
associated data (`s2v_ok`), copies the received IV from `siv` to `W`
(`sivIn_ok`), decrypts the data with CTR from it (`ctr_ok`), finishes S2V with the plaintext into `W + 112`
(`finish_ok`), sets `r0` to 1 if the two IVs are equal and 0 if not,
without a branch (`compare_ok`), ANDs every byte of the plaintext with
`0 − r0` (`maskData_ok`) and restores the registers (`decrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesCcm.Arm (blw mask_byte length_mask mask_succ)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR restore_ok covers_left covers_prefix in_off)
open VG.Proof.MdStream.Arm (wp_ldrSp)
open VG.Proof.AesGcm.Arm (Keeps z_subFlags gpr_subFlags z_cmp eval_eq' eval_ne' addr_i dec32 z_dec in_of_covers
  bytesAt_succ mem_store gpr_store add32_ofNat_assoc in_left add_ofNat_zero mem_subFlags bytes_words cmp_value
  words_eq_iff runBlock_app_of add_ofNat_assoc)

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp)
include L

/-- `compare`: `r0` is 1 iff the 16 bytes at `W` and `W + 112` are equal. -/
theorem compare_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 0) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tOff) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  have q₀ := he.perm.wR (show 112 + 4 ≤ 2576 by decide)
  have q₁ := he.perm.wR (show 116 + 4 ≤ 2576 by decide)
  have q₂ := he.perm.wR (show 120 + 4 ≤ 2576 by decide)
  have q₃ := he.perm.wR (show 124 + 4 ≤ 2576 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (112 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, tOff]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, tOff]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
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
  · rw [show compare = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m, tOff, Nat.mul_zero, Nat.add_zero]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

omit L in
theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {ok : Bool} (h6 : s.gpr .r6 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if ok then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa [.ldrb .r12 .r6 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r6 0, addI .r6 .r6 1,
        .subs .r5 .r5 (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if ok then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r6 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [h6, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      mask_byte]
  · simp [gpr_setReg, h6, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

omit L in
/-- `maskData`: every byte of the data (`n` bytes at `D`, in `r6` and `r5`)
ANDed with `0 − ok`, for `ok ∈ {0, 1}` in `r0`: kept if `ok = 1`, zeroed if
`ok = 0`. -/
theorem maskData_ok {s : State} (he : VG.Proof.AesSiv.Arm.Env c w sp R s) {D : BitVec 32} {n : Nat} (hD : VG.Proof.AesSiv.Arm.Dat c w sp s D n)
    (hn32 : n < 2 ^ 32) (h6 : s.gpr .r6 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {ok : Bool}
    (h0 : s.gpr .r0 = if ok then 1 else 0) :
    WP isa maskData s fun s' => VG.Proof.AesSiv.Arm.Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r1 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (if ok then bytesAt s.mem (State.addr D) n else Spec.Ccm.zeros n) := by
  have hn := hD.buf.fit
  obtain ⟨s₁, run₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .cmp .r5 (imm 0)] s = some s₁ ∧ s₁.gpr .r1 = 0 - (if ok then 1 else 0) ∧
      s₁.z = decide (n = 0) ∧ (∀ r, r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h0, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, imm]
      rw [z_cmp hn32 (by decide)]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := by simpa using hb
    subst hn0
    refine ⟨he₁, k₁.rd, k₁.wr, fun r a _ _ _ => g₁ r a, ?_⟩
    rw [k₁.mem]; cases ok <;> simp [bytesAt, Spec.Ccm.zeros, VG.WriteBytes.writeBytes_nil]
  have hn0 : 0 < n := by have : n ≠ 0 := by simpa using hb
                         omega
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r6 = D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - j) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (if ok then bytesAt s.mem (State.addr D) j else Spec.Ccm.zeros j) ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (n - 0) _
    ⟨0, rfl, hn0, by rw [g₁ _ (by decide), h6, add_ofNat_zero], by rw [g₁ _ (by decide), h5]; rfl,
      by rw [k₁.mem]; cases ok <;> simp [bytesAt, Spec.Ccm.zeros, VG.WriteBytes.writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr,
      k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r6, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r6', r5', z', g', rd', wr', sp'⟩ := VG.Proof.AesSiv.Arm.maskStep_ok t (ok := ok) r6 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers hD.buf.rd hj (by omega))
    (by rw [wr, aD]; exact in_of_covers hD.wr hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr D, j⟩] s.mem t.mem := by
    rw [mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr D + BitVec.ofNat 64 j) = s.mem (State.addr D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D)
      (if ok then bytesAt s.mem (State.addr D) (j + 1) else Spec.Ccm.zeros (j + 1)) := by
    rw [mem', aD, hq, mem, mask_succ, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.z = decide (j + 1 = n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = n) := eval_ne' hz
  by_cases hjn : j + 1 = n
  · left
    refine ⟨by rw [ev]; simp [hjn], he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], fun r a b d e => by rw [gg r b d e, g₁ r a], by rw [hmem, hjn]⟩
  · right
    refine ⟨by rw [ev]; simp [hjn], n - (j + 1), by omega, j + 1, rfl, by omega, r6',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-- Decryption before the comparison: the received IV at `W`, from `T`, the
plaintext `p` at `D` and S2V's result for it at `W + 112`, the saved
registers and the data's address and length where they were. -/
structure OMid (c w sp a D T : BitVec 32) (R N n : Nat) (s s' : State) : Prop where
  env : Env c w sp R s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sv : SavedAt s'.mem w s
  a0 : s'.mem.readW (State.addr sp) 32 = D
  a1 : s'.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  iv : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 0) 16 = bytesAt s.mem (State.addr T) 16
  pt : bytesAt s'.mem (State.addr D) n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R)
    (Spec.Siv.counter (bytesAt s.mem (State.addr T) 16)) (bytesAt s.mem (State.addr D) n)
  tag : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tOff) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N))
      (bytesAt s'.mem (State.addr D) n)

/-- S2V of the associated data, the received IV copied from `siv`, CTR from it
and S2V's end with the plaintext. -/
theorem front_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) {rest : Prog isa}
    {Q : State → Prop} (k : ∀ s', OMid c w sp a D T R N n s s' → WP isa rest s' Q) :
    WP isa (.seq encS2v (.seq (.block sivIn) (.seq (ctr 0) (.seq (.block [.ldrSp .r6 0, .ldrSp .r5 4])
      (.seq (finish tOff) rest))))) s Q := by
  have hR := h.rounds
  have hRb := VG.Proof.AesSiv.Arm.rounds_le hR
  have ww := L.ww
  refine WP.seq (WP.mono (s2v_ok L h) fun s₀ ⟨mₛ, O⟩ => ?_)
  have f₀₀ : Frame (savedR w :: wR w sp) s.mem s₀.mem :=
    (O.fs.mono (by simp)).trans (O.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
  have dA₀ : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  have dT₀ : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr T, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.t_w.sub_right (Lay.wSub (by decide))
    · exact h.t_w.sub_right (Lay.wSub (by decide))
    · exact h.t_w.sub_right (Lay.wSub (by decide))
    · exact h.t_stk.symm
  -- The received IV copied from `siv`.
  have a8 : State.addr (s₀.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [O.env.sp]; exact addr_add (by have := h.afit; omega)
  have v8 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 8)) 32 = T := by
    rw [a8, f₀₀.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA₀ r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a2]
  have i8 : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 8)) 4 := by
    rw [a8, O.rd, O.wr]; exact in_off h.args (by decide) (by decide)
  obtain ⟨s₁, run₁, iv₀₁, fi, gi, rdi, wri, spi⟩ := sivIn_ok L O.env i8 v8 (by rw [O.rd, O.wr]; exact h.t_rd)
    h.tfit (h.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c w sp R s₁ := O.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact gi _ (by decide) (by decide)) spi rdi wri
  have rd₁ : s₁.rd = s.rd := by rw [rdi, O.rd]
  have wr₁ : s₁.wr = s.wr := by rw [wri, O.wr]
  have hD₁ : Dat c w sp s₁ D n := h.data.of_eq rd₁ wr₁
  have w0 : ∀ {a k : Nat}, 16 ≤ a → a + k ≤ 2576 →
      (⟨State.addr w + BitVec.ofNat 64 a, k⟩ : Region).Disjoint ⟨State.addr w, 16⟩ := fun ha hk => by
    have := L.w_w (a := _) (n := _) (d := 0) (m := 16) (.inr ha) hk (by decide)
    rwa [add_ofNat_zero] at this
  have f₀₁ : Frame (⟨State.addr w, 16⟩ :: savedR w :: wR w sp) s.mem s₁.mem :=
    (f₀₀.mono fun r hr => List.mem_cons_of_mem _ hr).trans (fi.mono (by simp))
  have dA : ∀ r ∈ ⟨State.addr w, 16⟩ :: savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.args_w.sub_right (Region.sub_prefix (by decide))
    · exact dA₀ r hr
  have dD : ∀ r ∈ ⟨State.addr w, 16⟩ :: savedR w :: wR w sp, (⟨State.addr D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.data.buf.w.sub_right (Region.sub_prefix (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.stk.symm
  have dc : ∀ r ∈ ⟨State.addr w, 16⟩ :: savedR w :: wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.c_w.sub_right (Region.sub_prefix (by decide))
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  have hm0 : s₁.mem.readW (State.addr sp) 32 = D := by
    rw [f₀₁.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.a0]
  have hm1 : s₁.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₀₁.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  refine WP.seq (WP.mono (ctr_ok L he₁ hR hD₁ h.n32 h.afit (by rw [rd₁, wr₁]; exact h.args) h.args_w
    hm0 hm1) fun s₂ ⟨he₂, rd₂, wr₂, g₂, h6₂, h5₂, f₂, d₂⟩ => ?_)
  -- What CTR writes.
  have eA : ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
    · exact h.args_d
  have eS : ∀ r ∈ VG.Proof.AesSiv.Arm.ctrR w sp D n, (savedR w).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  have eW : ∀ {d : Nat}, d + 16 ≤ 80 ∨ 2432 ≤ d → d + 16 ≤ 2576 →
      ∀ r ∈ VG.Proof.AesSiv.Arm.ctrR w sp D n, (⟨State.addr w + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro d hd hd' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by simp only [ksOff]; omega) hd' (by decide)
    · exact L.w_w (by omega) hd' (by decide)
    · exact (L.stk_w' hd').symm
    · exact (h.data.buf.w.sub_right (Lay.wSub hd')).symm
  have ec : ∀ r ∈ VG.Proof.AesSiv.Arm.ctrR w sp D n, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
    · exact h.data.c
  have hm0₂ : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [BitVec.add_zero, f₂.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), hm0]
  have hm1₂ : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), hm1]
  have hsp₂ : s₂.sp = sp := he₂.sp
  refine WP.seq ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp₂]; exact addr_add (by have := h.afit; omega))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact in_off h.args (by decide) (by decide)) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.sp, hsp₂]; exact addr_add (by have := h.afit; omega))
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, rd₁, wr₁]; exact in_off h.args (by decide) (by decide))
    fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have he₄ : VG.Proof.AesSiv.Arm.Env c w sp R s₄ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.sp, u₃.sp]) (by rw [u₄.rd, u₃.rd]) (by rw [u₄.wr, u₃.wr])
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, rd₂, rd₁]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, wr₂, wr₁]
  have hD₄ : Dat c w sp s₄ D n := h.data.of_eq rd₄ wr₄
  have h6₄ : s₄.gpr .r6 = D := by rw [u₄.other _ (by decide), u₃.gpr, hm0₂]
  have h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [u₄.gpr, u₃.mem, hm1₂]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.finish_ok L he₄ hR hD₄.buf h.n32 h6₄ h5₄ (out := tOff) (.inr rfl))
    fun s₅ ⟨he₅, rd₅, wr₅, _, f₅, o₅⟩ => k s₅ ?_)
  have f₅' : Frame (VG.Proof.AesSiv.Arm.wR w sp) s₄.mem s₅.mem := VG.Proof.AesSiv.Arm.frame_oR_tOff f₅
  rw [m₄] at f₅' o₅
  -- The values.
  have ciph₁ : Spec.Siv.ctxCiph s₁.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
    VG.Proof.AesSiv.Arm.ctxCiph_frame f₀₁ dc hRb
  have mac₂ : Spec.Siv.ctxMac s₂.mem (State.addr c) R = Spec.Siv.ctxMac s.mem (State.addr c) R := by
    rw [ctxMac_frame f₂ ec hRb, ctxMac_frame f₀₁ dc hRb]
  have iv₁ : bytesAt s₁.mem (State.addr w) 16 = bytesAt s.mem (State.addr T) 16 := by
    rw [iv₀₁, bytesAt_frame f₀₀ dT₀ (by decide)]
  have p₁ : bytesAt s₁.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₁ dD (by have := h.data.buf.lt; omega)
  have p₅ : bytesAt s₅.mem (State.addr D) n = bytesAt s₂.mem (State.addr D) n :=
    bytesAt_frame f₅' (dis_wR h.data.buf.w h.data.buf.stk) (by have := h.data.buf.lt; omega)
  have acc₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
      bytesAt s₀.mem (State.addr w + BitVec.ofNat 64 dOff) 16 := by
    rw [bytesAt_frame f₂ (eW (.inr (by decide)) (by decide)) (by decide),
      bytesAt_frame fi (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact w0 (by decide) (by decide)) (by decide)]
  have dWw : ∀ r ∈ wR w sp, (⟨State.addr w + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have dAw : ∀ r ∈ wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r :=
    fun r hr => dA₀ r (List.mem_cons_of_mem _ hr)
  refine ⟨he₅, by rw [rd₅, rd₄], by rw [wr₅, wr₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((O.sv.frame O.frame (saved_wR L)).frame fi fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w0 (by decide) (by decide)).frame f₂ eS).frame f₅'
      (saved_wR L)
  · rw [f₅'.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dAw r hr).sub_left (Region.sub_prefix (by decide))) (by decide), ← hm0₂, BitVec.add_zero]
  · rw [f₅'.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dAw r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), hm1₂]
  · rw [bytesAt_frame f₅' dWw (by decide), bytesAt_frame f₂ (eW (.inl (by decide)) (by decide)) (by decide),
      BitVec.add_zero, iv₁]
  · rw [p₅, d₂, ciph₁, iv₁, p₁]
  · rw [o₅, mac₂, acc₂, O.acc, p₅]

/-- `vg_aes_siv_decrypt`: 1 and the plaintext in place if the received IV at
`T` is S2V's for it, and 0 and zeros if not. -/
theorem decrypt_wp {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa decrypt s fun s' => abiPreserved s s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.ctxCiph s.mem (State.addr c) R)
          (Spec.Siv.components 32 s.mem (State.addr a) N) (bytesAt s.mem (State.addr T) 16)
          (bytesAt s.mem (State.addr D) n) with
      | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr D) n = pt
      | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr D) n = Spec.Siv.zeros n := by
  have ww := L.ww
  refine VG.Proof.AesSiv.Arm.front_ok L h fun s₅ M => ?_
  obtain ⟨s₆, run₆, h0₆, g₆, k₆⟩ := VG.Proof.AesSiv.Arm.compare_ok L M.env
  have hsp₅ : s₅.sp = sp := M.env.sp
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩))
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [k₆.sp, hsp₅]; exact addr_add (by have := h.afit; omega))
    (by rw [k₆.rd, k₆.wr, M.rd, M.wr]; exact in_off h.args (by decide) (by decide)) fun s₇ u₇ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₇.sp, k₆.sp, hsp₅]; exact addr_add (by have := h.afit; omega))
    (by rw [u₇.rd, u₇.wr, k₆.rd, k₆.wr, M.rd, M.wr]; exact in_off h.args (by decide) (by decide))
    fun s₈ u₈ => WP.block_nil ?_
  have m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, k₆.mem]
  have he₈ : VG.Proof.AesSiv.Arm.Env c w sp R s₈ := M.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        rw [u₈.other _ (by decide), u₇.other _ (by decide), g₆ _ (by decide) (by decide) (by decide)])
    (by rw [u₈.sp, u₇.sp, k₆.sp]) (by rw [u₈.rd, u₇.rd, k₆.rd]) (by rw [u₈.wr, u₇.wr, k₆.wr])
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, k₆.rd, M.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, k₆.wr, M.wr]
  have hD₈ : VG.Proof.AesSiv.Arm.Dat c w sp s₈ D n := h.data.of_eq rd₈ wr₈
  have h6₈ : s₈.gpr .r6 = D := by
    rw [u₈.other _ (by decide), u₇.gpr, k₆.mem, BitVec.add_zero, M.a0]
  have h5₈ : s₈.gpr .r5 = BitVec.ofNat 32 n := by rw [u₈.gpr, u₇.mem, k₆.mem, M.a1]
  have h0₈ : s₈.gpr .r0 = if (decide (bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 0) 16 =
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 tOff) 16)) then 1 else 0 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), h0₆]; simp only [decide_eq_true_eq]
  obtain ⟨ok, hok⟩ : ∃ ok, ok = decide (bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 0) 16 =
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 tOff) 16) := ⟨_, rfl⟩
  rw [← hok] at h0₈
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.maskData_ok he₈ hD₈ h.n32 h6₈ h5₈ h0₈) fun s₉ ⟨he₉, rd₉, wr₉, g₉, m₉⟩ => ?_)
  have hlen := length_mask s₈.mem (State.addr D) ok n
  have sv₉ : SavedAt s₉.mem w s := by
    rw [m₉]
    refine (m₈ ▸ M.sv).frame (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨State.addr D, n⟩)
      (by rw [hlen]; exact Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (restore_ok (s₀ := s) he₉.r11 (by omega)
    (by rw [rd₉, wr₉, rd₈, wr₈]; exact covers_left (covers_prefix h.perm.w (by decide))) sv₉
    (by rw [he₉.sp, h.hsp])) fun s₁₀ ⟨ab, m₁₀, r0₁₀, _, _⟩ => ⟨ab, ?_⟩
  have hr0 : s₁₀.gpr .r0 = if ok then 1 else 0 := by
    rw [r0₁₀, g₉ _ (by decide) (by decide) (by decide) (by decide), h0₈]
  have hb : bytesAt s₁₀.mem (State.addr D) n =
      if ok then bytesAt s₅.mem (State.addr D) n else Spec.Ccm.zeros n := by
    have e := VG.Proof.AesSiv.Arm.bytesAt_writeBytes_self s₈.mem (State.addr D)
      (if ok then bytesAt s₈.mem (State.addr D) n else Spec.Ccm.zeros n) (by rw [hlen]; have := h.n32; omega)
    rw [hlen] at e
    rw [m₁₀, m₉, e, m₈]
  rw [M.iv, M.tag, M.pt] at hok
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith]
  by_cases e : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N))
      (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R) (Spec.Siv.counter (bytesAt s.mem (State.addr T) 16))
        (bytesAt s.mem (State.addr D) n)) = bytesAt s.mem (State.addr T) 16
  · have : ok = true := by rw [hok, e]; simp
    simp only [e, ite_true]
    rw [hr0, hb, this, M.pt]; exact ⟨rfl, rfl⟩
  · have : ok = false := by rw [hok]; simpa using Ne.symm e
    simp only [e, ite_false]
    rw [hr0, hb, this]; exact ⟨rfl, rfl⟩

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.CTMac`. -/
section

/-!
# AES-SIV on ARMv7: the CMAC of a string is constant time

Untrusted: everything here is checked by Lean. Two runs of `cmacOf` on
strings at the same address and of the same length (`MPre`) leak the same:
the blocks between the calls the taint analysis checks from the registers
that hold the string's address and length, the context, the rounds and `W`;
the calls get the same arguments in both runs (`upd_rel`, `fin_rel`), which
the correctness lemmas give.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.AesCcm.Arm (UArgs upd_call upd_rel)
open VG.Impl.AesGcm.Arm (imm)

/-- The registers an environment fixes. -/
theorem env_eq {c w sp : BitVec 32} {R : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁) (h₂ : VG.Proof.AesSiv.Arm.Env c w sp R s₂)
    {r : Reg} (hr : r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

/-- Before `cmacOf`: the string, `n` bytes at `P`, in `r6` and `r5`. -/
structure MPre (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  env : VG.Proof.AesSiv.Arm.Env c w sp R s
  buf : VG.Proof.AesSiv.Arm.Buf w sp s P n
  r6 : s.gpr .r6 = P
  r5 : s.gpr .r5 = BitVec.ofNat 32 n

/-- What the bytes after the chained ones are, as a buffer. -/
theorem Buf.rest {w sp P : BitVec 32} {n : Nat} {s : State} (hP : VG.Proof.AesSiv.Arm.Buf w sp s P n) :
    VG.Proof.AesSiv.Arm.Buf w sp s (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
  have hcl := VG.Proof.AesSiv.Arm.chainedLen_le n
  by_cases h0 : n - Spec.Cmac.chainedLen 16 n = 0
  · have : n = 0 := by
      by_contra hne; have := VG.Proof.AesSiv.Arm.chainedLen_ne hne; omega
    subst this
    rw [VG.Proof.AesSiv.Arm.chainedLen_zero, show P + BitVec.ofNat 32 0 = P from BitVec.add_zero P]
    exact hP
  · exact hP.sub (j := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega) (by omega)

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- Between the calls of `cmacOf`. -/
structure MMid (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  pre : VG.Proof.AesSiv.Arm.MPre c w sp R P n s
  r4 : s.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)

theorem cmacOf_ct {P : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (VG.Proof.AesSiv.Arm.MPre c w sp R P n) (cmacOf stOff) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      (cmacPre stOff) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r9, .r10, .r11])
      (.block (cmacMid stOff)) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.MMid c w sp R P n s ∧
      UArgs s c (w + BitVec.ofNat 32 stOff) P (w + BitVec.ofNat 32 256) R (Spec.Cmac.chainedLen 16 n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r5, h₂.r5]
      · rw [h₁.r6, h₂.r6]
      all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.env h₂.env (by simp)) hA)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.cmacPre_ok L h.env hR h.buf hn h.r6 h.r5) fun s' ⟨he, rd, wr, g, h4, U, _⟩ =>
      ⟨⟨⟨he, h.buf.of_eq rd wr, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.r6], by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h.r5]⟩, h4⟩, U⟩) ?_
  refine CT.seq (J := VG.Proof.AesSiv.Arm.MMid c w sp R P n)
    (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.pre.env.sp, hh.2.1.pre.env.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => by
      have g : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := h'.saved
      exact ⟨⟨h.1.pre.env.of_saved h'.saved h'.sp h'.rd h'.wr, h.1.pre.buf.of_eq h'.rd h'.wr,
        by rw [g _ (by decide) (by decide), h.1.pre.r6], by rw [g _ (by decide) (by decide), h.1.pre.r5]⟩,
        by rw [g _ (by decide) (by decide), h.1.r4]⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.Env c w sp R s ∧ VG.Proof.AesSiv.Arm.FArgs s c (w + BitVec.ofNat 32 stOff)
      (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (w + BitVec.ofNat 32 256) (n - Spec.Cmac.chainedLen 16 n) R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.pre.r5, h₂.pre.r5]
      · rw [h₁.pre.r6, h₂.pre.r6]
      all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.pre.env h₂.pre.env (by simp)) hB)
    (fun s h => by
      obtain ⟨s', run, he, _, _, F⟩ := VG.Proof.AesSiv.Arm.cmacMid_ok L h.pre.env hR hn h.pre.buf.rest h.r4 h.pre.r5 h.pre.r6
      exact WP.of_runBlock ⟨s', run, he, F⟩) ?_
  exact VG.Proof.AesSiv.Arm.fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩

/-! ## S2V over the components -/

/-- The descriptors' words in `m` are `dsc`, the same in both runs. -/
def DescEq (m : Mem) (a : BitVec 32) (N : Nat) (dsc : Nat → Nat → BitVec 32) : Prop :=
  ∀ i < N, ∀ j < 2, VG.Proof.AesSiv.Arm.descW m a i j = dsc i j

/-- Before component `i` (and, for `i = N`, after the last), in one run. -/
def AI (c w sp a : BitVec 32) (R N : Nat) (dsc : Nat → Nat → BitVec 32) (i : Nat) (s : State) : Prop :=
  ∃ m₀ σ, VG.Proof.AesSiv.Arm.AInv c w sp a R N m₀ σ i s ∧ VG.Proof.AesSiv.Arm.DescEq m₀ a N dsc

/-- One component. -/
theorem adBody_ct {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} {i : Nat} (hi : i < N) :
    CT (VG.Proof.AesSiv.Arm.AI c w sp a R N dsc i) (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r8]) (.block adNext) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7, .r8, .r9, .r10, .r11])
      (.block adStep) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.MPre c w sp R (dsc i 0) (dsc i 1).toNat s ∧
      s.gpr .r8 = a + BitVec.ofNat 32 (8 * i) ∧ s.gpr .r7 = BitVec.ofNat 32 (N - i))
    (CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r8, h₂.r8]) hA)
    (fun s ⟨m₀, σ, h, hd⟩ => WP.mono (VG.Proof.AesSiv.Arm.adNext_ok h.ads hi h.frame h.r8) fun s₁ ⟨h6, h5, g, k⟩ => by
      have hb := (h.ads.comp i hi).of_eq k.rd k.wr
      rw [hd i hi 0 (by decide), hd i hi 1 (by decide)] at hb
      exact ⟨⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) k.sp k.rd k.wr, hb,
        by rw [h6, hd i hi 0 (by decide)],
        by rw [h5, hd i hi 1 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩,
        by rw [g _ (by decide) (by decide), h.r8], by rw [g _ (by decide) (by decide), h.r7]⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.Env c w sp R s ∧ s.gpr .r8 = a + BitVec.ofNat 32 (8 * i) ∧
      s.gpr .r7 = BitVec.ofNat 32 (N - i))
    ((VG.Proof.AesSiv.Arm.cmacOf_ct L hR (BitVec.isLt _)).mono fun s h => h.1)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.cmacOf_ok L h.1.env hR h.1.buf (BitVec.isLt _) h.1.r6 h.1.r5)
      fun s' ⟨he, _, _, g, _, _⟩ => ⟨he, by rw [g _ (by decide) (by decide) (by decide), h.2.1],
        by rw [g _ (by decide) (by decide) (by decide), h.2.2]⟩) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.2.1, h₂.2.1]
    all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.1 h₂.1 (by simp)) hC

/-- One component, as `aStep_ok` but with the descriptors. -/
theorem adBody_wp {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} {i : Nat} (hi : i < N) {s : State}
    (h : VG.Proof.AesSiv.Arm.AI c w sp a R N dsc i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) s fun s' =>
      VG.Proof.AesSiv.Arm.AI c w sp a R N dsc (i + 1) s' ∧ s'.z = decide (N - (i + 1) = 0) := by
  obtain ⟨m₀, σ, h, hd⟩ := h
  exact WP.mono (VG.Proof.AesSiv.Arm.aStep_ok L hR h hi) fun s' ⟨h', hz⟩ => ⟨⟨m₀, σ, h', hd⟩, hz⟩

/-- S2V over the components. -/
theorem s2vAds_ct {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32) :
    CT (VG.Proof.AesSiv.Arm.AI c w sp a R N dsc 0) s2vAds := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7]) (.block [.cmp .r7 (imm 0)])
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.AI c w sp a R N dsc 0 s ∧ s.z = decide (N = 0))
    (CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r7, h₂.r7]) hA)
    (fun s ⟨m₀, σ, h, hd⟩ => by
      refine WP.of_runBlock ⟨_, by arun [], ⟨m₀, σ, ?_, hd⟩, ?_⟩
      · exact ⟨h.env.keep (fun r _ => rfl) rfl rfl rfl, h.ads.of_eq rfl rfl, h.r8, h.r7, h.rd, h.wr, h.frame,
          h.acc⟩
      · simp only [Proof.AesGcm.Arm.z_subFlags, h.r7, Nat.sub_zero]; exact Proof.AesGcm.Arm.z_cmp hN (by decide))
    ?_
  refine CT.ite (decide (N = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hN0 => ?_
  have hN0' : N ≠ 0 := by simpa using hN0
  refine (RelCT.loop (M := isa) (c := .ne)
    (fun (k : Nat) (x y : State) => ∃ i, k = N - i ∧ i < N ∧ VG.Proof.AesSiv.Arm.AI c w sp a R N dsc i x ∧ VG.Proof.AesSiv.Arm.AI c w sp a R N dsc i y)
    (fun k => ?_) (N - 0)).mono (fun x y hxy => ⟨0, rfl, Nat.pos_of_ne_zero hN0', hxy.1.1, hxy.2.1⟩)
    fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : k = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (((VG.Proof.AesSiv.Arm.adBody_ct L hR hiN).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.Arm.AI c w sp a R N dsc (i + 1) s ∧ s.z = decide (N - (i + 1) = 0))
    (F₂ := fun (s : State) => VG.Proof.AesSiv.Arm.AI c w sp a R N dsc (i + 1) s ∧ s.z = decide (N - (i + 1) = 0))
    fun x y hxy => ⟨VG.Proof.AesSiv.Arm.adBody_wp L hR hiN hxy.1, VG.Proof.AesSiv.Arm.adBody_wp L hR hiN hxy.2⟩).mono
    (fun x y p => ⟨p.2.2.1, p.2.2.2⟩) fun x y p => ?_)
  have ea := Proof.AesGcm.Arm.eval_ne' p.2.1.2
  have eb := Proof.AesGcm.Arm.eval_ne' p.2.2.2
  refine ⟨by rw [ea, eb], fun e => trivial, fun e => ?_⟩
  have he : N - (i + 1) ≠ 0 := by rw [ea] at e; simpa using e
  exact ⟨N - (i + 1), by omega, i + 1, rfl, by omega, p.2.1.1, p.2.2.1⟩

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.CTFinish`. -/
section

/-!
# AES-SIV on ARMv7: S2V's end is constant time

Untrusted: everything here is checked by Lean. Two runs of `finish` on
strings at the same address and of the same length (`FI`) leak the same:
the branch is on the length, and so are the tails' copies and `j`, which
the taint analysis checks with the blocks between the calls; the calls get
the same arguments in both runs, which the correctness lemmas give
(`shortArgs_ok`, `longArgs₁_ok`, `longArgs₂_ok`, `longArgs₃_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.AesCcm.Arm (UArgs upd_call upd_rel)
open VG.Impl.AesGcm.Arm (imm)

/-- Before `finish`: the string, `n` bytes at `P`, in `r6` and `r5`. -/
abbrev FI (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) : State → Prop := VG.Proof.AesSiv.Arm.MPre c w sp R P n

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

omit L hR in
theorem env_regs {s₁ s₂ : State} (h₁ : VG.Proof.AesSiv.Arm.Env c w sp R s₁) (h₂ : VG.Proof.AesSiv.Arm.Env c w sp R s₂) :
    ∀ r ∈ ([.r9, .r10, .r11] : List Reg), s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesSiv.Arm.env_eq h₁ h₂ (by simp)

/-- The short case's call. -/
theorem shortMac_ct {out : Nat} (hout : out = 0 ∨ out = tOff) : CT (VG.Proof.AesSiv.Arm.Env c w sp R) (shortMac out) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r9, .r10, .r11])
      (.block (shortArgs out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact CT.seq (J := fun s => VG.Proof.AesSiv.Arm.Env c w sp R s ∧
      VG.Proof.AesSiv.Arm.FArgs s c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ => VG.Proof.AesSiv.Arm.env_regs h₁ h₂) hA)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.shortArgs_ok L h hR hout) fun s' h' => ⟨h'.1, h'.2.2.2.2.2⟩)
    (VG.Proof.AesSiv.Arm.fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩)

/-- Before the long case's calls: the string and `16 k`. -/
structure LI (c w sp : BitVec 32) (R : Nat) (P : BitVec 32) (n : Nat) (s : State) : Prop where
  pre : VG.Proof.AesSiv.Arm.MPre c w sp R P n s
  r4 : s.gpr .r4 = BitVec.ofNat 32 (16 * kOf n)

/-- The long case's calls. -/
theorem longMac_ct {P : BitVec 32} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) {out : Nat}
    (hout : out = 0 ∨ out = tOff) : CT (VG.Proof.AesSiv.Arm.LI c w sp R P n) (longMac out) := by
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le n
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r6, .r9, .r10, .r11])
      (.block (longArgs₁ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5]) jBlock h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r7, .r9, .r10, .r11])
      (.block (longArgs₂ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r7, .r9, .r10, .r11])
      (.block (longArgs₃ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The registers the pieces keep.
  let K := 16 * kOf n
  let j := jOf n
  let Rg (s : State) : Prop := VG.Proof.AesSiv.Arm.Env c w sp R s ∧ s.gpr .r4 = BitVec.ofNat 32 K ∧ s.gpr .r5 = BitVec.ofNat 32 n
  have keep : ∀ {s s' : State}, Rg s → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) → s'.sp = s.sp →
      s'.rd = s.rd → s'.wr = s.wr → Rg s' := fun h g hsp hrd hwr =>
    ⟨h.1.of_saved g hsp hrd hwr, by rw [g _ (by decide) (by decide), h.2.1],
      by rw [g _ (by decide) (by decide), h.2.2]⟩
  refine CT.seq (J := fun s => Rg s ∧ UArgs s c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.r4, h₂.r4]
      · rw [h₁.pre.r6, h₂.pre.r6]
      all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.pre.env h₂.pre.env (by simp)) hA)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.longArgs₁_ok L h.pre.env hR h.pre.buf (K := K) (by omega) (by omega) hn h.pre.r6 h.r4 hout)
      fun s' ⟨he, g, _, _, _, U⟩ => ⟨⟨he, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), h.r4], by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h.pre.r5]⟩, U⟩) ?_
  refine CT.seq (J := Rg) (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.1.sp, hh.2.1.1.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => keep h.1 h'.saved h'.sp h'.rd h'.wr) ?_
  refine CT.seq (J := fun s => Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2, h₂.2.2]) hB)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.jBlock_ok h16 hn h.2.2) fun s' ⟨h7, g, k⟩ =>
      ⟨⟨h.1.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) k.sp k.rd k.wr,
        by rw [g _ (by decide) (by decide), h.2.1], by rw [g _ (by decide) (by decide), h.2.2]⟩, h7⟩) ?_
  refine CT.seq (J := fun s => (Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j) ∧
      UArgs s c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) R j)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.1.1 h₂.1.1 (by simp)) hC)
    (fun s h => by
      obtain ⟨s', run, he, g, k, U⟩ := VG.Proof.AesSiv.Arm.longArgs₂_ok L h.1.1 hR hout hj1 h.2
      refine WP.of_runBlock ⟨s', run, ⟨⟨he, ?_, ?_⟩, ?_⟩, U⟩
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2.1]
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2.2]
      · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.2]) ?_
  refine CT.seq (J := fun s => Rg s ∧ s.gpr .r7 = BitVec.ofNat 32 j)
    (upd_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.1.1.sp, hh.2.1.1.1.sp⟩)
    (fun s h => WP.mono (upd_call h.2) fun s' h' => ⟨keep h.1.1 h'.saved h'.sp h'.rd h'.wr,
      by rw [h'.saved _ (by decide) (by decide), h.1.2]⟩) ?_
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.Env c w sp R s ∧ VG.Proof.AesSiv.Arm.FArgs s c (w + BitVec.ofNat 32 out)
      (w + BitVec.ofNat 32 (tailOff + 16 * j)) (w + BitVec.ofNat 32 256) (n - K - 16 * j) R)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2, h₂.1.2.2]
      · rw [h₁.2, h₂.2]
      all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.1.1 h₂.1.1 (by simp)) hD)
    (fun s h => by
      obtain ⟨s', run, he, _, _, F⟩ := VG.Proof.AesSiv.Arm.longArgs₃_ok L h.1.1 hR hout hn hT hJ hj1 h.2 h.1.2.2 h.1.2.1
      exact WP.of_runBlock ⟨s', run, he, F⟩) ?_
  exact VG.Proof.AesSiv.Arm.fin_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2, hh.1.1.sp, hh.2.1.sp⟩

/-- S2V's end with the string, into `W + out`. -/
theorem finish_ct {P : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    CT (VG.Proof.AesSiv.Arm.FI c w sp R P n) (finish out) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hS⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      shortTail h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hL⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6, .r9, .r10, .r11])
      longTail h).isSome = true := ⟨_, by taint_decide⟩
  have regs : ∀ s₁ s₂, VG.Proof.AesSiv.Arm.FI c w sp R P n s₁ → VG.Proof.AesSiv.Arm.FI c w sp R P n s₂ →
      ∀ r ∈ ([.r5, .r6, .r9, .r10, .r11] : List Reg), s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6]
    all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.env h₂.env (by simp)
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.FI c w sp R P n s ∧ s.z = decide (n / 16 = 0))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, hz, g, k⟩ := VG.Proof.AesSiv.Arm.finishPre_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.buf.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, hz⟩) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2) (fun ht => ?_) fun hf => ?_
  · have h16 : n < 16 := by have := of_decide_eq_true ht; omega
    exact (CT.seq (J := VG.Proof.AesSiv.Arm.Env c w sp R) (CT.taint _ regs hS)
      (fun s h => WP.mono (VG.Proof.AesSiv.Arm.shortTail_ok L h.env h.buf h16 h.r6 h.r5) fun s' h' => h'.1)
      (VG.Proof.AesSiv.Arm.shortMac_ct L hR hout)).mono fun s h => h.1
  · have h16 : 16 ≤ n := by have := of_decide_eq_false hf; omega
    exact (CT.seq (J := VG.Proof.AesSiv.Arm.LI c w sp R P n) (CT.taint _ regs hL)
      (fun s h => WP.mono (VG.Proof.AesSiv.Arm.longTail_ok L h.env h.buf h16 hn h.r6 h.r5) fun s' ⟨he, rd, wr, g, h4, _⟩ =>
        ⟨⟨he, h.buf.of_eq rd wr, by rw [g _ (by decide) (by decide) (by decide), h.r6],
          by rw [g _ (by decide) (by decide) (by decide), h.r5]⟩, h4⟩)
      (VG.Proof.AesSiv.Arm.longMac_ct L hR h16 hn hout)).mono fun s h => h.1

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.CTCtr`. -/
section

/-!
# AES-SIV on ARMv7: CTR is constant time

Untrusted: everything here is checked by Lean. Two runs of `ctr 0` on data
at the same address and of the same length (`CtrI`) leak the same: the
first block loads the data's address and length from the stack arguments,
the same in both runs; the branches are on the length, and so are the
numbers of blocks and bytes; the calls of `vg_aes_ctr32` get the same
arguments in both runs (`ctrWholeArgs_ok`, `ctrTailArgs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT CtrCall ctr_call)
open VG.Impl.AesGcm.Arm (imm addI xorLoop)
open VG.Impl.CmacAes.Arm (mov)

/-- Before CTR's pieces: the data, `n` bytes at `D`, in `r6` and `r5`. -/
structure CI (c w sp : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : VG.Proof.AesSiv.Arm.Env c w sp R s
  dat : VG.Proof.AesSiv.Arm.Dat c w sp s D n
  r6 : s.gpr .r6 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n

/-- After code that keeps the callee-saved registers. -/
theorem CI.keep {c w sp D : BitVec 32} {R n : Nat} {s s' : State} (h : VG.Proof.AesSiv.Arm.CI c w sp R D n s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.CI c w sp R D n s' :=
  ⟨h.env.of_saved hg hsp hrd hwr, h.dat.of_eq hrd hwr, by rw [hg _ (by decide) (by decide), h.r6],
    by rw [hg _ (by decide) (by decide), h.r5]⟩

/-- Before CTR: the data's address and length as the stack arguments, which
the regions the code may write are apart from. -/
structure CtrI (c w sp : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c w sp R s
  dat : Dat c w sp s D n
  wa : ∀ r ∈ s.wr, (⟨State.addr sp, 16⟩ : Region).Disjoint r
  afit : sp.toNat + 16 ≤ 2 ^ 32
  args : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)
  args_w : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  args_d : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩
  m0 : s.mem.readW (State.addr sp) 32 = D
  m1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  n32 : n < 2 ^ 32

/-- The first two stack arguments: the data's address and length. -/
theorem CtrI.arg {c w sp D : BitVec 32} {R n : Nat} {s : State} (h : VG.Proof.AesSiv.Arm.CtrI c w sp R D n s) :
    stackArg s 0 = D ∧ stackArg s 1 = BitVec.ofNat 32 n := by
  have hsp := h.env.sp
  refine ⟨?_, ?_⟩
  · rw [stackArg, stackArgAddr, hsp, show 4 * 0 = 0 from rfl, BitVec.add_zero, h.m0]
  · rw [stackArg, stackArgAddr, hsp, addr_add (by have := h.afit; omega), h.m1]

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- The whole blocks. -/
theorem ctrWhole_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (VG.Proof.AesSiv.Arm.CI c w sp R D n) ctrWhole := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r6, .r9, .r10, .r11])
      (.block (ctrArgs ++ [mov .r3 .r6])) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.CI c w sp R D n s ∧ s.z = decide (n / 16 = 0) ∧
      s.gpr .r12 = BitVec.ofNat 32 (n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, h12, hz, g, k⟩ := VG.Proof.AesSiv.Arm.split16_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, hz, h12⟩) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2.1) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.Env c w sp R s ∧
      CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) D (w + BitVec.ofNat 32 256) R (n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1.r6, h₂.1.r6]
      all_goals exact VG.Proof.AesSiv.Arm.env_eq h₁.1.env h₂.1.env (by simp)) hB)
    (fun s h => by
      obtain ⟨s', run, he, _, _, C⟩ := VG.Proof.AesSiv.Arm.ctrWholeArgs_ok L h.1.env hR h.1.dat h.1.r6 rfl h.2.2
      exact WP.of_runBlock ⟨s', run, he, C⟩) ?_
  exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.2, h₂.2, by rw [h₁.1.sp, h₂.1.sp]⟩

/-- What the whole blocks keep. -/
theorem ctrWhole_keeps {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) {s : State} (h : VG.Proof.AesSiv.Arm.CI c w sp R D n s) :
    WP isa ctrWhole s (VG.Proof.AesSiv.Arm.CI c w sp R D n) := by
  obtain ⟨s₁, run₁, h12, hz, g, k⟩ := VG.Proof.AesSiv.Arm.split16_ok hn h.r5
  have h₁ : VG.Proof.AesSiv.Arm.CI c w sp R D n s₁ := ⟨h.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
    by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · exact WP.ite true (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun _ => WP.block_nil h₁)
      (fun h => by cases h)
  refine WP.ite false (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun h => by cases h) fun _ => ?_
  obtain ⟨s₂, run₂, _, g₂, k₂, C⟩ := VG.Proof.AesSiv.Arm.ctrWholeArgs_ok L h₁.env hR h₁.dat h₁.r6 rfl h12
  have h₂ : VG.Proof.AesSiv.Arm.CI c w sp R D n s₂ := h₁.keep (fun r hr hlr => by
      have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2 hlr) k₂.sp k₂.rd k₂.wr
  exact WP.seq (WP.of_runBlock ⟨s₂, run₂, WP.mono (ctr_call C) fun s₃ p => h₂.keep p.saved p.sp p.rd p.wr⟩)

/-- The last bytes. -/
theorem ctrTail_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (VG.Proof.AesSiv.Arm.CI c w sp R D n) ctrTail := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.dp .and .r4 .r5 (imm 15), .cmp .r4 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r9, .r10, .r11])
      (.block (zero16 ksOff ++ ctrArgs ++ [addI .r3 .r11 ksOff, .mov .r12 (imm 1)])) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r11])
      (.seq (.block [addI .r1 .r11 ksOff, .dp .sub .r2 .r5 (.reg .r4), .dp .add .r2 .r2 (.reg .r6), mov .r3 .r4])
        xorLoop) h).isSome = true := ⟨_, by taint_decide⟩
  let J (s : State) : Prop := VG.Proof.AesSiv.Arm.CI c w sp R D n s ∧ s.gpr .r4 = BitVec.ofNat 32 (n % 16)
  refine CT.seq (J := fun s => J s ∧ s.z = decide (n % 16 = 0))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, h4, hz, g, k⟩ := VG.Proof.AesSiv.Arm.tailPre_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, h4⟩, hz⟩) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => J s ∧ CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff)
      (w + BitVec.ofNat 32 ksOff) (w + BitVec.ofNat 32 256) R 1)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact VG.Proof.AesSiv.Arm.env_eq h₁.1.1.env h₂.1.1.env (by simp)) hB)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.ctrTailArgs_ok L h.1.1.env hR) fun s' ⟨he, g, rd, wr, _, _, C⟩ =>
      ⟨⟨⟨he, h.1.1.dat.of_eq rd wr,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.r6],
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.r5]⟩,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2]⟩, C⟩) ?_
  refine CT.seq (J := J)
    (CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.2, h₂.2, by rw [h₁.1.1.env.sp, h₂.1.1.env.sp]⟩)
    (fun s h => WP.mono (ctr_call h.2) fun s' p =>
      ⟨h.1.1.keep p.saved p.sp p.rd p.wr, by rw [p.saved _ (by decide) (by decide), h.1.2]⟩) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.r5, h₂.1.r5]
    · rw [h₁.1.r6, h₂.1.r6]
    · exact VG.Proof.AesSiv.Arm.env_eq h₁.1.env h₂.1.env (by simp)) hC

/-- CTR from the IV at `W`. -/
theorem ctr_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (VG.Proof.AesSiv.Arm.CtrI c w sp R D n) (ctr 0) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r9, .r10, .r11] (4 * 2))
      (.block (counter 0 ++ [.ldrSp .r6 0, .ldrSp .r5 4])) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := VG.Proof.AesSiv.Arm.CI c w sp R D n)
    (CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ => VG.Proof.AesSiv.Arm.env_regs h₁.env h₂.env)
      (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
      (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega, fun r hr => by
        rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
      (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega)
        fun i hi => by
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · rw [h₁.arg.1, h₂.arg.1]
          · rw [h₁.arg.2, h₂.arg.2]) hA)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.ctrPre_ok L h.env h.dat h.afit h.args h.args_w h.m0 h.m1)
      fun s' ⟨he, hD, h6, h5, _⟩ => ⟨he, hD, h6, h5⟩) ?_
  exact CT.seq (VG.Proof.AesSiv.Arm.ctrWhole_ct L hR hn) (fun s h => VG.Proof.AesSiv.Arm.ctrWhole_keeps L hR hn h) (VG.Proof.AesSiv.Arm.ctrTail_ct L hR hn)

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.CTEnc`. -/
section

/-!
# AES-SIV on ARMv7: `encrypt` and `decrypt` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments and the same descriptors of the components (`E0`) leak the
same. The blocks reading the stack arguments are checked by the taint
analysis with them public (`CT.argTaint`); between the pieces, the
correctness lemmas give each run the next piece's invariant (`CtrI` for the
pieces after S2V of the associated data, which keep the stack arguments);
`decrypt` compares the IVs and masks the data without a branch, so nothing
it does depends on the result.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (CT savedR in_off bytesAt_frame Keeps)
open VG.Proof.MdStream.Arm (wp_ldrSp)

/-- The entry, with the regions the code may write apart from the stack
arguments, and the descriptors' words `dsc`. -/
structure E0 (c w sp a D T : BitVec 32) (R N n : Nat) (dsc : Nat → Nat → BitVec 32) (s : State) : Prop where
  pre : EPre c w sp a D T R N n s
  wa : ∀ r ∈ s.wr, (⟨State.addr sp, 16⟩ : Region).Disjoint r
  desc : DescEq s.mem a N dsc

/-- The descriptors' words, after writes apart from them. -/
theorem DescEq.frame {m m' : Mem} {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32}
    (h : VG.Proof.AesSiv.Arm.DescEq m a N dsc) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r) : VG.Proof.AesSiv.Arm.DescEq m' a N dsc := fun i hi j hj => by
  rw [← h i hi j hj]
  exact hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

/-- After code that keeps the stack arguments: writes apart from them, the
same regions and an environment. -/
theorem CtrI.next {c w sp D : BitVec 32} {R n : Nat} {s s' : State} (h : CtrI c w sp R D n s)
    (he : Env c w sp R s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    CtrI c w sp R D n s' where
  env := he
  dat := h.dat.of_eq hrd hwr
  wa := by rw [hwr]; exact h.wa
  afit := h.afit
  args := by rw [hrd, hwr]; exact h.args
  args_w := h.args_w
  args_d := h.args_d
  m0 := by
    rw [hf.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.m0]
  m1 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.m1]
  n32 := h.n32

/-- `siv`, the third stack argument, at `T`: 16 bytes apart from `W` that the
code may read. -/
structure SivA (w sp T : BitVec 32) (s : State) : Prop where
  m2 : s.mem.readW (State.addr sp + BitVec.ofNat 64 8) 32 = T
  fit : T.toNat + 16 ≤ 2 ^ 32
  rd : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩

theorem SivA.of_pre {c w sp a D T : BitVec 32} {R N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    SivA w sp T s :=
  ⟨h.a2, h.tfit, h.t_rd, h.t_w⟩

/-- `siv` where it was, after writes apart from the stack arguments. -/
theorem SivA.next {w sp T : BitVec 32} {s s' : State} (h : SivA w sp T s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) : SivA w sp T s' where
  m2 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.m2]
  fit := h.fit
  rd := by rw [hrd, hwr]; exact h.rd
  t_w := h.t_w

/-- The third stack argument: `siv`'s address. -/
theorem SivA.arg {c w sp D T : BitVec 32} {R n : Nat} {s : State} (hc : CtrI c w sp R D n s)
    (h : SivA w sp T s) : stackArg s 2 = T := by
  rw [stackArg, stackArgAddr, hc.env.sp, addr_add (by have := hc.afit; omega), h.m2]

section
variable {c w sp : BitVec 32} {R : Nat} (L : VG.Proof.AesSiv.Arm.Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

omit L hR in
/-- A region of `W` but its first 16 bytes, or the stack below `sp`, is apart
from the stack arguments. -/
theorem args_dis (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩) :
    ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)

omit L hR in
/-- What S2V's end writes, apart from the stack arguments. -/
theorem args_dis_oR (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩) {out : Nat}
    (hout : out = 0 ∨ out = tOff) : ∀ r ∈ oR w sp out, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hw.sub_right (Lay.wSub (by rcases hout with rfl | rfl <;> decide))
  · exact VG.Proof.AesSiv.Arm.args_dis hw r (List.mem_cons_of_mem _ hr)

omit L hR in
/-- What CTR writes, apart from the stack arguments. -/
theorem args_dis_ctr {D : BitVec 32} {n : Nat}
    (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩)
    (hd : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩) :
    ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  · exact hd

omit L hR in
/-- The pieces' invariant, from the entry, after writes that keep the stack
arguments. -/
theorem CtrI.of_entry {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} {σ s : State}
    (h : E0 c w sp a D T R N n dsc σ) (he : Env c w sp R s) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    {rs : List Region} (hf : Frame rs σ.mem s.mem) (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    CtrI c w sp R D n s where
  env := he
  dat := h.pre.data.of_eq hrd hwr
  wa := by rw [hwr]; exact h.wa
  afit := h.pre.afit
  args := by rw [hrd, hwr]; exact h.pre.args
  args_w := h.pre.args_w
  args_d := h.pre.args_d
  m0 := by
    rw [hf.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.pre.a0]
  m1 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.pre.a1]
  n32 := h.pre.n32

omit L hR in
/-- The data's address and length from the stack arguments. -/
theorem loadArgs_ct {D : BitVec 32} {n : Nat} :
    CT (VG.Proof.AesSiv.Arm.CtrI c w sp R D n) (.block [.ldrSp .r6 0, .ldrSp .r5 4]) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [] (4 * 2))
      (.block [.ldrSp .r6 0, .ldrSp .r5 4]) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun _ _ _ _ r hr => by simp at hr) (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
    (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega, fun r hr => by
      rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · rw [h₁.arg.1, h₂.arg.1]
        · rw [h₁.arg.2, h₂.arg.2]) hA

omit L hR in
theorem loadArgs_wp {D : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesSiv.Arm.CtrI c w sp R D n s) :
    WP isa (.block [.ldrSp .r6 0, .ldrSp .r5 4]) s fun s' => (VG.Proof.AesSiv.Arm.CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧
      s'.gpr .r5 = BitVec.ofNat 32 n) ∧ s'.gpr .r0 = s.gpr .r0 := by
  have hsp := h.env.sp
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp]; exact addr_add (by have := h.afit; omega)) (in_off h.args (by decide) (by decide))
    fun s₁ u₁ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₁.sp, hsp]; exact addr_add (by have := h.afit; omega))
    (by rw [u₁.rd, u₁.wr]; exact in_off h.args (by decide) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have he : VG.Proof.AesSiv.Arm.Env c w sp R s₂ := h.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.sp, u₁.sp]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  refine ⟨⟨h.next he (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (rs := [])
      (by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _) (fun _ hr => by simp at hr), ?_, ?_⟩,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide)]⟩
  · rw [u₂.other _ (by decide), u₁.gpr, BitVec.add_zero, h.m0]
  · rw [u₂.gpr, u₁.mem, h.m1]

/-! ## S2V of the associated data -/

/-- Between S2V's pieces, in one run: from the entry `σ`, the memory `m₀`
after the save, before component `i`. -/
def SI (c w sp a D T : BitVec 32) (R N n : Nat) (dsc : Nat → Nat → BitVec 32) (i : Nat) (s : State) : Prop :=
  ∃ σ m₀, E0 c w sp a D T R N n dsc σ ∧ Frame [savedR w] σ.mem m₀ ∧ AInv c w sp a R N m₀ σ i s ∧
    DescEq m₀ a N dsc

theorem encS2v_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32) :
    CT (E0 c w sp a D T R N n dsc) encS2v := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r0, .r1, .r2, .r3] (4 * 4))
      (.block (encPre ++ startPre)) h).isSome = true := ⟨_, by taint_decide⟩
  have ab : CT (E0 c w sp a D T R N n dsc) (.seq (.block (encPre ++ startPre)) finFrame) := by
    refine CT.seq (J := fun s => ∃ σ mₛ, Started c w sp a R N σ mₛ s)
      (CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.pre.r0, h₂.pre.r0]
        · rw [h₁.pre.r1, h₂.pre.r1]
        · rw [h₁.pre.r2, h₂.pre.r2]
        · rw [h₁.pre.r3, h₂.pre.r3]) (fun s₁ s₂ h₁ h₂ => by rw [h₁.pre.hsp, h₂.pre.hsp])
        (fun s h => ⟨by rw [h.pre.hsp]; exact h.pre.afit, fun r hr => by
          rw [h.pre.hsp]; exact h.wa r hr⟩)
        (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.pre.hsp, h₂.pre.hsp]) (by rw [h₁.pre.hsp]; exact h₁.pre.afit)
          fun i hi => by
            have e : ∀ {s : State}, E0 c w sp a D T R N n dsc s → ∀ {k : Nat}, k < 4 →
                stackArg s k = s.mem.readW (State.addr sp + BitVec.ofNat 64 (4 * k)) 32 := fun h k hk => by
              rw [stackArg, stackArgAddr, h.pre.hsp, addr_add (by have := h.pre.afit; omega)]
            rw [e h₁ hi, e h₂ hi]
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
            · rw [show 4 * 0 = 0 from rfl, BitVec.add_zero, h₁.pre.a0, h₂.pre.a0]
            · rw [h₁.pre.a1, h₂.pre.a1]
            · rw [h₁.pre.a2, h₂.pre.a2]
            · rw [h₁.pre.a3, h₂.pre.a3]) hA)
      (fun s h => WP.mono (startBlock_ok L h.pre) fun s' ⟨mₛ, St⟩ => ⟨s, mₛ, St⟩) ?_
    exact fin_rel fun s₁ s₂ hh => by
      obtain ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ := hh
      exact ⟨h₁.args, h₂.args, h₁.env.sp, h₂.env.sp⟩
  refine RelCT.assoc (CT.seq ab (J := SI c w sp a D T R N n dsc 0) (fun s h => WP.mono (start_ok L h.pre)
    fun s' ⟨mₛ, fs, _, I⟩ => ⟨s, mₛ, h, fs, I, h.desc.frame fs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.pre.ads.dw.sub_right (Lay.wSub (by decide))⟩) ?_)
  refine CT.seq (J := SI c w sp a D T R N n dsc N)
    ((s2vAds_ct L hR hN).mono fun s ⟨σ, m₀, _, _, I, hd⟩ => ⟨m₀, σ, I, hd⟩)
    (fun s ⟨σ, m₀, h, fs, I, hd⟩ => WP.mono (s2vAds_ok L hR I hN) fun s' I' => ⟨σ, m₀, h, fs, I', hd⟩) ?_
  exact (loadArgs_ct (c := c) (w := w) (sp := sp) (R := R) (D := D) (n := n)).mono fun s ⟨σ, m₀, h, fs, I, _⟩ =>
    CtrI.of_entry h I.env I.rd I.wr ((fs.mono (by simp)).trans (I.frame.mono fun r hr =>
      List.mem_cons_of_mem _ hr)) (VG.Proof.AesSiv.Arm.args_dis h.pre.args_w)

omit hR in
/-- After S2V of the associated data. -/
theorem encS2v_wp {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} {s : State}
    (h : E0 c w sp a D T R N n dsc s) :
    WP isa encS2v s fun s' => (CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n) ∧
      SivA w sp T s' ∧ s'.wr = s.wr :=
  WP.mono (s2v_ok L h.pre) fun s' ⟨mₛ, O⟩ => by
    have F : Frame (savedR w :: wR w sp) s.mem s'.mem :=
      (O.fs.mono (by simp)).trans (O.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
    exact ⟨⟨CtrI.of_entry h O.env O.rd O.wr F (args_dis h.pre.args_w), O.r6, O.r5⟩,
      (SivA.of_pre h.pre).next O.rd O.wr F (args_dis h.pre.args_w), O.wr⟩

/-! ## `siv` -/

omit hR in
/-- The IV copied to `siv`, which the code may write: what follows needs only
the environment. -/
theorem sivOut_wp {D T : BitVec 32} {n : Nat} {s : State}
    (h : CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr) :
    WP isa (.block sivOut) s (Env c w sp R) := by
  obtain ⟨hc, ht, hw⟩ := h
  have a8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [hc.env.sp]; exact addr_add (by have := hc.afit; omega)
  obtain ⟨s', run, -, -, g, rd, wr, sp'⟩ := sivOut_ok L hc.env (T := T)
    (by rw [a8]; exact in_off hc.args (by decide) (by decide)) (by rw [a8]; exact ht.m2) hw ht.fit
    (ht.t_w.sub_right (Region.sub_prefix (by decide)))
  exact WP.of_runBlock ⟨s', run, hc.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) sp' rd wr⟩

omit L hR in
theorem sivOut_ct {D T : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr) (.block sivOut) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r11] (4 * 3)) (.block sivOut) h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.r11, h₂.1.env.r11])
    (fun s₁ s₂ h₁ h₂ => by rw [h₁.1.env.sp, h₂.1.env.sp])
    (fun s h => ⟨by rw [h.1.env.sp]; have := h.1.afit; omega, fun r hr => by
      rw [h.1.env.sp]; exact (h.1.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.1.env.sp, h₂.1.env.sp]) (by rw [h₁.1.env.sp]; have := h₁.1.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · rw [h₁.1.arg.1, h₂.1.arg.1]
        · rw [h₁.1.arg.2, h₂.1.arg.2]
        · rw [SivA.arg h₁.1 h₁.2.1, SivA.arg h₂.1 h₂.2.1]) hA

omit hR in
/-- The received IV copied from `siv` to `W`. -/
theorem sivIn_wp {D T : BitVec 32} {n : Nat} {s : State} (h : CtrI c w sp R D n s ∧ SivA w sp T s) :
    WP isa (.block sivIn) s (CtrI c w sp R D n) := by
  obtain ⟨hc, ht⟩ := h
  have a8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [hc.env.sp]; exact addr_add (by have := hc.afit; omega)
  obtain ⟨s', run, -, f, g, rd, wr, sp'⟩ := sivIn_ok L hc.env (T := T)
    (by rw [a8]; exact in_off hc.args (by decide) (by decide)) (by rw [a8]; exact ht.m2) ht.rd ht.fit
    (ht.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.of_runBlock ⟨s', run, hc.next (hc.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) sp' rd wr) rd wr f fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact hc.args_w.sub_right (Region.sub_prefix (by decide))

omit L hR in
theorem sivIn_ct {D T : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ SivA w sp T s) (.block sivIn) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r11] (4 * 3)) (.block sivIn) h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.r11, h₂.1.env.r11])
    (fun s₁ s₂ h₁ h₂ => by rw [h₁.1.env.sp, h₂.1.env.sp])
    (fun s h => ⟨by rw [h.1.env.sp]; have := h.1.afit; omega, fun r hr => by
      rw [h.1.env.sp]; exact (h.1.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.1.env.sp, h₂.1.env.sp]) (by rw [h₁.1.env.sp]; have := h₁.1.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · rw [h₁.1.arg.1, h₂.1.arg.1]
        · rw [h₁.1.arg.2, h₂.1.arg.2]
        · rw [SivA.arg h₁.1 h₁.2, SivA.arg h₂.1 h₂.2]) hA

/-! ## The ends -/

omit L hR in
theorem restore_ct : CT (VG.Proof.AesSiv.Arm.Env c w sp R) (.block Impl.AesGcm.Arm.restore) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r11])
      (.block Impl.AesGcm.Arm.restore) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hA

/-- S2V's end with the data into `W + out`, from the pieces' invariant with
the data in `r6` and `r5`. -/
theorem finish_next {D : BitVec 32} {n : Nat} {out : Nat} (hout : out = 0 ∨ out = tOff) {s : State}
    (h : CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n)
    (hA : ∀ r ∈ oR w sp out, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    WP isa (finish out) s (CtrI c w sp R D n) := by
  exact WP.mono (finish_ok L h.1.env hR h.1.dat.buf h.1.n32 h.2.1 h.2.2 hout) fun s' ⟨he, rd, wr, _, f, _⟩ =>
    h.1.next he rd wr f hA

omit L hR in
/-- The IVs compared, and the data's address and length loaded again. -/
theorem cmpLoad_ct {D : BitVec 32} {n : Nat} :
    CT (VG.Proof.AesSiv.Arm.CtrI c w sp R D n) (.block (compare ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r9, .r10, .r11] (4 * 2))
      (.block (compare ++ [.ldrSp .r6 0, .ldrSp .r5 4])) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ => VG.Proof.AesSiv.Arm.env_regs h₁.env h₂.env) (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
    (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega, fun r hr => by
      rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · rw [h₁.arg.1, h₂.arg.1]
        · rw [h₁.arg.2, h₂.arg.2]) hA

omit hR in
theorem cmpLoad_wp {D : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesSiv.Arm.CtrI c w sp R D n s) :
    WP isa (.block (compare ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) s fun s' =>
      (VG.Proof.AesSiv.Arm.CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n) ∧
        ∃ ok : Bool, s'.gpr .r0 = if ok then 1 else 0 := by
  obtain ⟨s₁, run, h0, g, k⟩ := VG.Proof.AesSiv.Arm.compare_ok L h.env
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run, ?_⟩)
  have he : VG.Proof.AesSiv.Arm.Env c w sp R s₁ := h.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr
  have h₁ : VG.Proof.AesSiv.Arm.CtrI c w sp R D n s₁ := h.next he k.rd k.wr (rs := []) (by rw [k.mem]; exact Frame.refl _ _)
    (fun _ hr => by simp at hr)
  refine WP.mono (VG.Proof.AesSiv.Arm.loadArgs_wp h₁) fun s' ⟨p, e0⟩ => ⟨p, decide (bytesAt s.mem (State.addr w + BitVec.ofNat 64 0) 16 =
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 tOff) 16), ?_⟩
  rw [e0, h0]; simp only [decide_eq_true_eq]

omit L hR in
/-- The data masked with `0 − r0`. -/
theorem maskData_ct {D : BitVec 32} {n : Nat} :
    CT (fun s => VG.Proof.AesSiv.Arm.CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n) maskData := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6]) maskData h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.2.1, h₂.2.1]) hA

/-- `vg_aes_siv_encrypt`, in two runs with the same public arguments and
descriptors, with `siv` writable. -/
theorem encrypt_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32)
    (hn : n < 2 ^ 32) :
    CT (fun s => E0 c w sp a D T R N n dsc s ∧ Covers [⟨State.addr T, 16⟩] s.wr) encrypt := by
  refine CT.seq ((encS2v_ct L hR hN).mono fun s h => h.1) (J := fun s =>
      (CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n) ∧ SivA w sp T s ∧
        Covers [⟨State.addr T, 16⟩] s.wr)
    (fun s h => WP.mono (encS2v_wp L h.1) fun s' ⟨p, q, e⟩ => ⟨p, q, by rw [e]; exact h.2⟩) ?_
  refine CT.seq (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr)
    ((finish_ct L hR hn (.inl rfl)).mono fun s h => ⟨h.1.1.env, h.1.1.dat.buf, h.1.2.1, h.1.2.2⟩)
    (fun s h => WP.mono (finish_ok L h.1.1.env hR h.1.1.dat.buf h.1.1.n32 h.1.2.1 h.1.2.2 (.inl rfl))
      fun s' ⟨he, rd, wr, _, f, _⟩ => ⟨h.1.1.next he rd wr f (args_dis_oR h.1.1.args_w (.inl rfl)),
        h.2.1.next rd wr f (args_dis_oR h.1.1.args_w (.inl rfl)), by rw [wr]; exact h.2.2⟩) ?_
  refine CT.seq (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr)
    ((ctr_ct L hR hn).mono fun s h => h.1)
    (fun s h => WP.mono (ctr_ok L h.1.env hR h.1.dat hn h.1.afit h.1.args h.1.args_w h.1.m0 h.1.m1)
      fun s' ⟨he, rd, wr, _, _, _, f, _⟩ => ⟨h.1.next he rd wr f (args_dis_ctr h.1.args_w h.1.args_d),
        h.2.1.next rd wr f (args_dis_ctr h.1.args_w h.1.args_d), by rw [wr]; exact h.2.2⟩) ?_
  exact CT.seq (J := Env c w sp R) sivOut_ct (fun s h => sivOut_wp L h) restore_ct

/-- `vg_aes_siv_decrypt`, in two runs with the same public arguments and descriptors. -/
theorem decrypt_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32)
    (hn : n < 2 ^ 32) : CT (E0 c w sp a D T R N n dsc) decrypt := by
  refine CT.seq (encS2v_ct L hR hN) (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s)
    (fun s h => WP.mono (encS2v_wp L h) fun s' ⟨p, q, _⟩ => ⟨p.1, q⟩) ?_
  refine CT.seq sivIn_ct (fun s h => sivIn_wp L h) ?_
  refine CT.seq (J := CtrI c w sp R D n) (ctr_ct L hR hn)
    (fun s h => WP.mono (ctr_ok L h.env hR h.dat hn h.afit h.args h.args_w h.m0 h.m1)
      fun s' ⟨he, rd, wr, _, _, _, f, _⟩ => h.next he rd wr f (args_dis_ctr h.args_w h.args_d)) ?_
  refine CT.seq loadArgs_ct (fun s h => WP.mono (loadArgs_wp h) fun s' p => p.1) ?_
  refine CT.seq (J := CtrI c w sp R D n) ((finish_ct L hR hn (.inr rfl)).mono
      fun s h => ⟨h.1.env, h.1.dat.buf, h.2.1, h.2.2⟩)
    (fun s h => VG.Proof.AesSiv.Arm.finish_next L hR (.inr rfl) h (VG.Proof.AesSiv.Arm.args_dis_oR h.1.args_w (.inr rfl))) ?_
  refine CT.seq VG.Proof.AesSiv.Arm.cmpLoad_ct (fun s h => VG.Proof.AesSiv.Arm.cmpLoad_wp L h) ?_
  exact CT.seq (J := VG.Proof.AesSiv.Arm.Env c w sp R) (maskData_ct.mono fun s h => h.1)
    (fun s ⟨⟨h, h6, h5⟩, ok, h0⟩ => WP.mono (VG.Proof.AesSiv.Arm.maskData_ok h.env h.dat hn h6 h5 h0) fun s' p => p.1) VG.Proof.AesSiv.Arm.restore_ct

end

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Init`. -/
section

/-!
# AES-SIV on ARMv7: `vg_aes_siv_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
`r4`–`r6`, `r11` and `lr` in the scratch buffer, expands `K1` into the
context with `vg_aes_expand_key_scratch`, derives its subkeys after the schedule
with `vg_cmac_aes_subkeys`, expands `K2` after them and restores the
registers (`init_wp`): the context is then that of the key
(`Proof.AesSiv.keyRepr_of`). The code between the calls is constant time
by the taint analysis, and the calls by their own proofs (`init_ct`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.CmacAes.Stream.Arm (EArgs EPost SArgs SPost ek_call sub_call ek_rel sub_rel blw8)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsr wp_mov wp_add)

/-- `vg_aes_siv_init(key = r0, key_len = r1, ctx = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let ctx : Region := ⟨State.addr (s.gpr .r2), 512⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2560⟩
    let blw : Region := ⟨State.addr s.sp - 8, 8⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      blw.Disjoint key ∧ blw.Disjoint ctx ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 512 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 32 ∨ (s.gpr .r1).toNat = 48 ∨ (s.gpr .r1).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem (State.addr (s.gpr .r2))
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (Kp Ct S : BitVec 32) (KL : Nat) : Prop where
  r0 : s₀.gpr .r0 = Kp
  r1 : (s₀.gpr .r1).toNat = KL
  r2 : s₀.gpr .r2 = Ct
  r3 : s₀.gpr .r3 = S
  rd : s₀.rd = [⟨State.addr Kp, KL⟩]
  wr : s₀.wr = [⟨State.addr Ct, 512⟩, ⟨State.addr S, 2560⟩]
  k_c : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr Ct, 512⟩
  k_s : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 2560⟩
  c_s : (⟨State.addr Ct, 512⟩ : Region).Disjoint ⟨State.addr S, 2560⟩
  b_k : (blw8 s₀).Disjoint ⟨State.addr Kp, KL⟩
  b_c : (blw8 s₀).Disjoint ⟨State.addr Ct, 512⟩
  b_s : (blw8 s₀).Disjoint ⟨State.addr S, 2560⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fC : Ct.toNat + 512 ≤ 2 ^ 32
  fS : S.toNat + 2560 ≤ 2 ^ 32
  sp : 8 ≤ s₀.sp.toNat
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) :
    VG.Proof.AesSiv.Arm.IPre s₀ (s₀.gpr .r0) (s₀.gpr .r2) (s₀.gpr .r3) (s₀.gpr .r1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n⟩

theorem half_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 32 KL >>> 1 = BitVec.ofNat 32 (KL / 2) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 32 (KL / 2) >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem initSaved_slots : Spill.Slots 2176 2196 initSaved := by decide

theorem initPost_eq : VG.Impl.AesSiv.Arm.initPost =
    (([(.r4, 2176), (.r5, 2180), (.r6, 2184), (.lr, 2192)] : List (Reg × Nat)) ++
      ([(.r11, 2188)] : List (Reg × Nat))).map
      (fun p => Instr.ldr p.1 .r11 p.2) := rfl

section
variable {s₀ : State} {Kp Ct S : BitVec 32} {KL : Nat}

theorem IPre.rounds (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) : KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.half (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) : KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.aC (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {d : Nat} (hd : d < 512) :
    State.addr (Ct + BitVec.ofNat 32 d) = State.addr Ct + BitVec.ofNat 64 d := addr_add (by have := hp.fC; omega)

theorem IPre.aK (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) :
    State.addr (Kp + BitVec.ofNat 32 (KL / 2)) = State.addr Kp + BitVec.ofNat 64 (KL / 2) :=
  addr_add (by have := hp.fK; have := hp.klen; omega)

theorem IPre.sC (_hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 512) :
    Region.Sub ⟨State.addr Ct + BitVec.ofNat 64 d, n⟩ ⟨State.addr Ct, 512⟩ := Offset.sub_base _ h

theorem IPre.sS (_hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 2560) :
    Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, n⟩ ⟨State.addr S, 2560⟩ := Offset.sub_base _ h

theorem IPre.sK (_hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ KL) :
    Region.Sub ⟨State.addr Kp + BitVec.ofNat 64 d, n⟩ ⟨State.addr Kp, KL⟩ := Offset.sub_base _ h

/-- A region of the context, writable. -/
theorem IPre.wC (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 512) :
    ∃ r' ∈ s₀.wr, ∃ off, State.addr Ct + BitVec.ofNat 64 d = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨⟨State.addr Ct, 512⟩, by rw [hp.wr]; simp, d, rfl, h⟩

/-- A region of the scratch buffer, writable. -/
theorem IPre.wS (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 2560) :
    ∃ r' ∈ s₀.wr, ∃ off, State.addr S + BitVec.ofNat 64 d = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨⟨State.addr S, 2560⟩, by rw [hp.wr]; simp, d, rfl, h⟩

/-- The arguments of a call of `vg_aes_expand_key_scratch`: half the key from byte
`a`, into the context from byte `c`. -/
theorem IPre.eargs (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {s : State} {a c : Nat} (ha : a = 0 ∨ a = KL / 2)
    (hc : c = 0 ∨ c = 272) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h0 : s.gpr .r0 = Kp + BitVec.ofNat 32 a) (h1 : s.gpr .r1 = BitVec.ofNat 32 (KL / 2))
    (h2 : s.gpr .r2 = Ct + BitVec.ofNat 32 c) (h3 : s.gpr .r3 = S) :
    EArgs s (Kp + BitVec.ofNat 32 a) (Ct + BitVec.ofNat 32 c) S (KL / 2) := by
  have hK := hp.fK
  have hC := hp.fC
  have hl := hp.klen
  have eK : State.addr (Kp + BitVec.ofNat 32 a) = State.addr Kp + BitVec.ofNat 64 a := by
    rcases ha with rfl | rfl
    · simp
    · exact hp.aK
  have eC : State.addr (Ct + BitVec.ofNat 32 c) = State.addr Ct + BitVec.ofNat 64 c := hp.aC (by omega)
  have sK : Region.Sub ⟨State.addr (Kp + BitVec.ofNat 32 a), KL / 2⟩ ⟨State.addr Kp, KL⟩ := by
    rw [eK]; exact hp.sK (by omega)
  have sC : Region.Sub ⟨State.addr (Ct + BitVec.ofNat 32 c), 240⟩ ⟨State.addr Ct, 512⟩ := by
    rw [eC]; exact hp.sC (by omega)
  exact
    { r0 := h0, r1 := h1, r2 := h2, r3 := h3
      klen := hp.half
      kw := (hp.k_c.sub_left sK).sub_right sC
      ks := (hp.k_s.sub_left sK).sub_right (Region.sub_prefix (by decide))
      ws := (hp.c_s.sub_left sC).sub_right (Region.sub_prefix (by decide))
      fK := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rcases ha with rfl | rfl <;> simp <;> omega
      fW := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rcases hc with rfl | rfl <;> simp <;> omega
      fS := by have := hp.fS; omega
      reads := by
        rw [hrd, hwr, hp.rd]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr Kp, KL⟩, by simp, a, eK, by show a + KL / 2 ≤ KL; rcases ha with rfl | rfl <;> omega⟩
      writes := by
        rw [hwr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', hr', off, e, l⟩ := hp.wC (d := c) (n := 240) (by omega)
          exact ⟨r', hr', off, by rw [eC]; exact e, l⟩
        · obtain ⟨r', hr', off, e, l⟩ := hp.wS (d := 0) (n := 512) (by decide)
          exact ⟨r', hr', off, by rw [← e]; simp, l⟩ }

/-- The arguments of the call of `vg_cmac_aes_subkeys`. -/
theorem IPre.sargs (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.sp = s₀.sp) (h0 : s.gpr .r0 = Ct) (h1 : s.gpr .r1 = BitVec.ofNat 32 (KL / 8 + 6))
    (h2 : s.gpr .r2 = Ct + BitVec.ofNat 32 240) (h3 : s.gpr .r3 = S) :
    SArgs s Ct (Ct + BitVec.ofNat 32 240) S (KL / 8 + 6) := by
  have hC := hp.fC
  have eC : State.addr (Ct + BitVec.ofNat 32 240) = State.addr Ct + BitVec.ofNat 64 240 := hp.aC (by decide)
  have sC : Region.Sub ⟨State.addr (Ct + BitVec.ofNat 32 240), 32⟩ ⟨State.addr Ct, 512⟩ := by
    rw [eC]; exact hp.sC (by decide)
  have bl : blw8 s = blw8 s₀ := by rw [blw8, blw8, hsp]
  exact
    { r0 := h0, r1 := h1, r2 := h2, r3 := h3
      rounds := hp.rounds
      hsp := by rw [hsp]; exact hp.sp
      wk := by rw [eC]; exact Offset.base_disjoint _ (by decide) (by omega)
      ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.c_s.sub_left sC).sub_right (Region.sub_prefix (by decide))
      bw := by rw [bl]; exact hp.b_c.sub_right (Region.sub_prefix (by decide))
      bk := by rw [bl]; exact hp.b_c.sub_right sC
      bs := by rw [bl]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
      fW := by omega
      fK := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
      fS := by have := hp.fS; omega
      reads := by
        rw [hrd, hwr, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr Ct, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      writes := by
        rw [hwr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', hr', off, e, l⟩ := hp.wC (d := 240) (n := 32) (by decide)
          exact ⟨r', hr', off, by rw [eC]; exact e, l⟩
        · obtain ⟨r', hr', off, e, l⟩ := hp.wS (d := 0) (n := 2176) (by decide)
          exact ⟨r', hr', off, by rw [← e]; simp, l⟩ }

end

/-! ## The code between the calls -/

/-- What every piece of `init` keeps: the key, the half length, the context
and the scratch buffer in `r4`, `r5`, `r6` and `r11`, the other callee-saved
registers (but `lr`), the stack pointer and the regions. -/
structure IKeep (s₀ : State) (Kp Ct S : BitVec 32) (KL : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = Kp
  r5 : s.gpr .r5 = BitVec.ofNat 32 (KL / 2)
  r6 : s.gpr .r6 = Ct
  r11 : s.gpr .r11 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r11 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- After a call, which keeps the callee-saved registers. -/
theorem IKeep.call {s₀ s s' : State} {Kp Ct S : BitVec 32} {KL : Nat} (h : VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s' :=
  ⟨by rw [hg _ (by simp [preserved]) (by decide), h.r4], by rw [hg _ (by simp [preserved]) (by decide), h.r5],
    by rw [hg _ (by simp [preserved]) (by decide), h.r6], by rw [hg _ (by simp [preserved]) (by decide), h.r11],
    fun r hr a b c d e => by rw [hg r hr e, h.keep r hr a b c d e], by rw [hsp, h.sp], by rw [hrd, h.rd],
    by rw [hwr, h.wr]⟩

/-- The memory after saving the registers. -/
abbrev iMem (s₀ : State) (S : BitVec 32) : Mem := Spill.saveMem s₀.mem (State.addr S) s₀.gpr initSaved

theorem initPre_wp {s₀ : State} {Kp Ct S : BitVec 32} {KL : Nat} (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL) :
    WP isa (.block VG.Impl.AesSiv.Arm.initPre) s₀ fun s => VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s ∧ s.mem = VG.Proof.AesSiv.Arm.iMem s₀ S ∧
      EArgs s Kp Ct S (KL / 2) := by
  have hS := hp.fS
  refine Spill.save_slots_ok VG.Proof.AesSiv.Arm.initSaved_slots (by rw [hp.r3]; omega) (fun d h₁ h₂ => ?_) ?_
  · rw [hp.r3, hp.wr]
    exact ⟨⟨State.addr S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    WP.block_nil ?_
  have hKL : s₀.gpr .r1 = BitVec.ofNat 32 KL :=
    BitVec.eq_of_toNat_eq (by
      rw [hp.r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases hp.klen with h | h | h <;> omega)])
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have r5 : s₅.gpr .r5 = BitVec.ofNat 32 (KL / 2) := by
    simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]
    rw [hKL]; exact VG.Proof.AesSiv.Arm.half_bv hp.klen
  refine ⟨⟨?_, r5, ?_, ?_, fun r hr a b c d e => ?_, sp₅, rd₅, wr₅⟩,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hp.r3], ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, hp.r0]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, hp.r2]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, hp.r3]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  · have e := hp.eargs (s := s₅) (a := 0) (c := 0) (.inl rfl) (.inl rfl) rd₅ wr₅
      (by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, hp.r0, BitVec.add_zero])
      (by rw [u₅.gpr, ← u₅.other _ (by decide), r5])
      (by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, hp.r2, BitVec.add_zero])
      (by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, hp.r3])
    simpa only [BitVec.add_zero] using e

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : BitVec 32} {KL : Nat} (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL)
    (h : VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s) :
    WP isa (.block initMid₁) s fun s' => VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s' ∧ s'.mem = s.mem ∧
      SArgs s' Ct (Ct + BitVec.ofNat 32 240) S (KL / 8 + 6) := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr a b c d e => ?_, sp₅, rd₅, wr₅⟩,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], hp.sargs rd₅ wr₅ sp₅ ?_ ?_ ?_ ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r4]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r5]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r11]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | (simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
       exact h.keep _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h.r6]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.gpr, u₁.other, h.r5]
    exact VG.Proof.AesSiv.Arm.rounds_bv hp.klen
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, h.r11]

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : BitVec 32} {KL : Nat} (hp : VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL)
    (h : VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s) :
    WP isa (.block initMid₂) s fun s' => VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s' ∧ s'.mem = s.mem ∧
      EArgs s' (Kp + BitVec.ofNat 32 (KL / 2)) (Ct + BitVec.ofNat 32 272) S (KL / 2) := by
  refine wp_add (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₄ : s₄.sp = s₀.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr a b c d e => ?_, sp₄, rd₄, wr₄⟩,
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    hp.eargs (.inr rfl) (.inr rfl) rd₄ wr₄ ?_ ?_ ?_ ?_⟩
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r4]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r5]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r11]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | (simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other]
       exact h.keep _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h.r4, h.r5]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h.r5]
  · simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h.r11]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .r0 = Kp at hp
  generalize s₀.gpr .r2 = Ct at hp
  generalize s₀.gpr .r3 = S at hp
  generalize (s₀.gpr .r1).toNat = KL at hp
  have hS := hp.fS
  have hC := hp.fC
  have hK := hp.fK
  have hl := hp.klen
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.initPre_wp hp) fun s₁ ⟨k₁, m₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (ek_call e₁) fun s₂ h₂ => ?_)
  have k₂ := k₁.call h₂.saved h₂.sp h₂.rd h₂.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.initMid₁_wp hp k₂) fun s₃ ⟨k₃, m₃, a₃⟩ => ?_)
  refine WP.seq (WP.mono (sub_call a₃) fun s₄ h₄ => ?_)
  have k₄ := k₃.call h₄.saved h₄.sp h₄.rd h₄.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.Arm.initMid₂_wp hp k₄) fun s₅ ⟨k₅, m₅, a₅⟩ => ?_)
  refine WP.seq (WP.mono (ek_call a₅) fun s₆ h₆ => ?_)
  have k₆ := k₅.call h₆.saved h₆.sp h₆.rd h₆.wr
  have e240 := hp.aC (d := 240) (by decide)
  have e272 := hp.aC (d := 272) (by decide)
  have bl₃ : blw8 s₃ = blw8 s₀ := by rw [blw8, blw8, k₃.sp]
  -- The memory, call by call.
  have f₁ : Frame [⟨State.addr S + BitVec.ofNat 64 2176, 20⟩] s₀.mem s₁.mem := by
    rw [m₁]; exact Spill.saveMem_frame_slots VG.Proof.AesSiv.Arm.initSaved_slots _ _ _
  have f₂ : Frame [⟨State.addr Ct, 240⟩, ⟨State.addr S, 512⟩] s₁.mem s₂.mem := by
    have := h₂.frame; simpa using this
  have f₄ : Frame [⟨State.addr Ct + BitVec.ofNat 64 240, 32⟩, ⟨State.addr S, 2176⟩, blw8 s₀] s₂.mem s₄.mem := by
    have := h₄.frame; rw [e240, bl₃, m₃] at this; exact this
  have f₆ : Frame [⟨State.addr Ct + BitVec.ofNat 64 272, 240⟩, ⟨State.addr S, 512⟩] s₄.mem s₆.mem := by
    have := h₆.frame; rw [e272, m₅] at this; exact this
  -- The saved registers.
  have dSv : ∀ r ∈ [(⟨State.addr Ct, 240⟩ : Region), ⟨State.addr S, 512⟩,
      ⟨State.addr Ct + BitVec.ofNat 64 240, 32⟩, ⟨State.addr S, 2176⟩, blw8 s₀,
      ⟨State.addr Ct + BitVec.ofNat 64 272, 240⟩],
      (⟨State.addr S + BitVec.ofNat 64 2176, 2196 - 2176⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 2176, 2196 - 2176⟩ ⟨State.addr S, 2560⟩ :=
      hp.sS (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact (hp.b_s.sub_right sub).symm
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved s₁.mem (State.addr S) s₀.gpr initSaved := by
    rw [m₁]; exact Spill.saveMem_saved _ _ _ _ VG.Proof.AesSiv.Arm.initSaved_slots
  have sv₆ : Spill.Saved s₆.mem (State.addr S) s₀.gpr initSaved :=
    ((sv₁.frame VG.Proof.AesSiv.Arm.initSaved_slots f₂ fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)).frame
      VG.Proof.AesSiv.Arm.initSaved_slots f₄ fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      VG.Proof.AesSiv.Arm.initSaved_slots f₆ fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [VG.Proof.AesSiv.Arm.initPost_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_slots_ok (lo := 2176) (hi := 2196) (by decide) (by decide) (g := s₀.gpr)
    (by rw [k₆.r11]; omega)
    (fun d h₁ h₂ => by
      rw [k₆.r11, k₆.rd, k₆.wr, hp.rd, hp.wr]
      exact ⟨⟨State.addr S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [k₆.r11]; exact fun p hp' => sv₆ p hp')
    fun s₇ hl₇ ho₇ m₇ _ _ sp₇ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [sp₇, k₆.sp]⟩, ?_⟩
  · have hr' := hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl₇ (.r4, 2176) (by decide)
    · exact hl₇ (.r5, 2180) (by decide)
    · exact hl₇ (.r6, 2184) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hl₇ (.r11, 2188) (by decide)
    · exact hl₇ (.lr, 2192) (by decide)
  · show Spec.Siv.KeyRepr s₇.mem (State.addr (s₀.gpr .r2))
      (Spec.Aes.bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
    rw [hp.r2, hp.r0, hp.r1, m₇]
    -- The key, outside everything the code writes.
    have dK {a n : Nat} (ha : a + n ≤ KL) : ∀ r ∈ [(⟨State.addr Ct, 240⟩ : Region), ⟨State.addr S, 512⟩,
        ⟨State.addr Ct + BitVec.ofNat 64 240, 32⟩, ⟨State.addr S, 2176⟩, blw8 s₀,
        ⟨State.addr S + BitVec.ofNat 64 2176, 20⟩],
        (⟨State.addr Kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
      have sub := hp.sK ha
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_c.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_c.sub_left sub).sub_right (hp.sC (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.b_k.sub_right sub).symm
      · exact (hp.k_s.sub_left sub).sub_right (hp.sS (by decide))
    have key {a : Nat} (ha : a + KL / 2 ≤ KL) :
        Spec.Aes.bytesAt s₅.mem (State.addr Kp + BitVec.ofNat 64 a) (KL / 2) =
          Spec.Aes.bytesAt s₀.mem (State.addr Kp + BitVec.ofNat 64 a) (KL / 2) := by
      rw [m₅, Proof.Cmac.bytesAt_frame f₄ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega),
        Proof.Cmac.bytesAt_frame f₂ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
          (by omega),
        Proof.Cmac.bytesAt_frame f₁ (fun r hr => dK ha r (by simp only [List.mem_singleton] at hr; subst hr; simp))
          (by omega)]
    have key₁ : Spec.Aes.bytesAt s₁.mem (State.addr Kp) (KL / 2) = Spec.Aes.bytesAt s₀.mem (State.addr Kp) (KL / 2) := by
      have := Proof.Cmac.bytesAt_frame f₁ (fun r hr => dK (a := 0) (n := KL / 2) (by omega) r
        (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega)
      rwa [BitVec.add_zero] at this
    have hRb : 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
    have sch : Spec.Aes.bytesAt s₂.mem (State.addr Ct) (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (State.addr Kp) (KL / 2)) := by
      have := h₂.out; rw [key₁] at this; exact this
    refine Proof.AesSiv.keyRepr_of hp.klen ?_ ?_ ?_
    · rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.base_disjoint _ (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide)))
          (by omega),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint _ (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
          · exact (hp.b_c.sub_right (Region.sub_prefix (by omega))).symm)
          (by omega), sch]
    · rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)
          · exact (hp.c_s.sub_left (hp.sC (by decide))).sub_right (Region.sub_prefix (by decide))) (by decide),
        ← e240, h₄.out, m₃,
        show 16 * (KL / 8 + 6 + 1) = 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) by
          simp only [Spec.Aes.rounds]; omega, sch]
    · have := h₆.out
      rw [e272, hp.aK, key (a := KL / 2) (by omega)] at this
      exact this

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.CTInit`. -/
section

/-!
# AES-SIV on ARMv7: `init` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same
pointers, key length and stack pointer leak the same: the blocks between
the calls the taint analysis checks from the registers holding the
arguments (`initPre`) or what `init` keeps from them (the key, the half
length, the context and the scratch buffer, `IKeep`); the calls get the same
arguments in both runs (`ek_rel`, `sub_rel`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT)
open VG.Proof.CmacAes.Stream.Arm (EArgs SArgs ek_call sub_call ek_rel sub_rel)

/-- After the entry, in one run from `s₀`, whose stack pointer is `sp₀`. -/
def IK (sp₀ Kp Ct S : BitVec 32) (KL : Nat) (s : State) : Prop :=
  ∃ s₀ : State, s₀.sp = sp₀ ∧ VG.Proof.AesSiv.Arm.IPre s₀ Kp Ct S KL ∧ VG.Proof.AesSiv.Arm.IKeep s₀ Kp Ct S KL s

theorem IK.regs {sp₀ Kp Ct S : BitVec 32} {KL : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL s₁)
    (h₂ : VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL s₂) : ∀ r ∈ ([.r4, .r5, .r6, .r11] : List Reg), s₁.gpr r = s₂.gpr r := by
  obtain ⟨_, _, _, k₁⟩ := h₁
  obtain ⟨_, _, _, k₂⟩ := h₂
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [k₁.r4, k₂.r4]
  · rw [k₁.r5, k₂.r5]
  · rw [k₁.r6, k₂.r6]
  · rw [k₁.r11, k₂.r11]

/-- After a call, which keeps the callee-saved registers. -/
theorem IK.call {sp₀ Kp Ct S : BitVec 32} {KL : Nat} {s s' : State} (h : VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL s' :=
  let ⟨s₀, e, hp, k⟩ := h
  ⟨s₀, e, hp, k.call hg hsp hrd hwr⟩

theorem init_ct' {sp₀ Kp Ct S : BitVec 32} {KL : Nat} :
    CT (fun s => s.sp = sp₀ ∧ VG.Proof.AesSiv.Arm.IPre s Kp Ct S KL) init := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3])
      (.block VG.Impl.AesSiv.Arm.initPre) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r11])
      (.block initMid₁) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r11])
      (.block initMid₂) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r11])
      (.block VG.Impl.AesSiv.Arm.initPost) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL s ∧ EArgs s Kp Ct S (KL / 2))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2.r0, h₂.2.r0]
      · exact BitVec.eq_of_toNat_eq (by rw [h₁.2.r1, h₂.2.r1])
      · rw [h₁.2.r2, h₂.2.r2]
      · rw [h₁.2.r3, h₂.2.r3]) hA)
    (fun s h => WP.mono (VG.Proof.AesSiv.Arm.initPre_wp h.2) fun s' ⟨k, _, e⟩ => ⟨⟨s, h.1, h.2, k⟩, e⟩) ?_
  refine CT.seq (J := VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL) (ek_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2⟩)
    (fun s h => WP.mono (ek_call h.2) fun s' p => h.1.call p.saved p.sp p.rd p.wr) ?_
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL s ∧ SArgs s Ct (Ct + BitVec.ofNat 32 240) S (KL / 8 + 6))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ => h₁.regs h₂) hB)
    (fun s ⟨s₀, e, hp, k⟩ => WP.mono (VG.Proof.AesSiv.Arm.initMid₁_wp hp k) fun s' ⟨k', _, a⟩ => ⟨⟨s₀, e, hp, k'⟩, a⟩) ?_
  refine CT.seq (J := VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL)
    (sub_rel (sp₀ := sp₀) fun s₁ s₂ hh => by
      obtain ⟨⟨⟨_, e₁, _, k₁⟩, a₁⟩, ⟨⟨_, e₂, _, k₂⟩, a₂⟩⟩ := hh
      exact ⟨a₁, a₂, k₁.sp.trans e₁, k₂.sp.trans e₂⟩)
    (fun s h => WP.mono (sub_call h.2) fun s' p => h.1.call p.saved p.sp p.rd p.wr) ?_
  refine CT.seq (J := fun s => VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL s ∧
      EArgs s (Kp + BitVec.ofNat 32 (KL / 2)) (Ct + BitVec.ofNat 32 272) S (KL / 2))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ => h₁.regs h₂) hC)
    (fun s ⟨s₀, e, hp, k⟩ => WP.mono (VG.Proof.AesSiv.Arm.initMid₂_wp hp k) fun s' ⟨k', _, a⟩ => ⟨⟨s₀, e, hp, k'⟩, a⟩) ?_
  refine CT.seq (J := VG.Proof.AesSiv.Arm.IK sp₀ Kp Ct S KL) (ek_rel fun s₁ s₂ hh => ⟨hh.1.2, hh.2.2⟩)
    (fun s h => WP.mono (ek_call h.2) fun s' p => h.1.call p.saved p.sp p.rd p.wr) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h₁.regs h₂ _ (by simp)) hD

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp₂ : VG.Proof.AesSiv.Arm.IPre s₂ (s₁.gpr .r0) (s₁.gpr .r2) (s₁.gpr .r3) (s₁.gpr .r1).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h₂
  exact (VG.Proof.AesSiv.Arm.init_ct' (sp₀ := s₁.sp) _ _ _ _ _ _ ⟨⟨rfl, IPre.of h₁⟩, ⟨q1.symm, hp₂⟩⟩ e₁ e₂).1

end VG.Proof.AesSiv.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Arm.Verified`. -/
section

/-!
# AES-SIV on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Siv/Contract.lean`. `init` calls `vg_cmac_aes_subkeys`, which uses 8
bytes of stack, and keeps its 2560-byte working space in a frame of its own
(`init_framed`); `encrypt` and `decrypt` are proved against the shared
contracts with the working space as a last argument
(`Proof/AesSiv/Scratch.lean`), using 16 bytes of stack: each call pushes two
words, and `vg_cmac_aes_update` and `vg_cmac_aes_finalize` push two more for
their own calls. On ARMv7 the arguments on the stack are read-only, apart
from every region the code may write (`E0`): the data, `work` and, for
`encrypt`, `siv`.
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def sivSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-! ## `vg_aes_siv_init` -/

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State :=
  VG.Proof.AesSiv.Arm.sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 32⟩] [⟨0x2000, 512⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Proof.AesSiv.initScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesSiv.Arm.init_wp hs) VG.Proof.AesSiv.Arm.init_ct (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, VG.Proof.AesSiv.Arm.initArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [initSat, sivSat] using VG.Proof.AesSiv.Arm.initSat)

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the
working space. -/
def initFrameSat : State :=
  VG.Proof.AesSiv.Arm.sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 32⟩] [⟨0x2000, 512⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract Arm.abi 2568).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, sivSat] using VG.Proof.AesSiv.Arm.initFrameSat

/-- `init` with its working space in a frame of 2560 bytes. -/
theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init)
    (Spec.Siv.initContract Arm.abi 2568) :=
  Arm.Verified.regScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre Arm.abi.ptrBits) (post := Spec.Siv.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) VG.Proof.AesSiv.Arm.init_verified (by decide) (by decide) (by decide) VG.Proof.AesSiv.Arm.initFrameSat_pre

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cov_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- Component `i`'s region, as the descriptors list it. -/
theorem listed_mem (m : Mem) (a : BitVec 32) {N i : Nat} (hi : i < N) :
    (⟨State.addr (VG.Proof.AesSiv.Arm.descW m a i 0), (VG.Proof.AesSiv.Arm.descW m a i 1).toNat⟩ : Region) ∈ Sig.listed 32 m .u8 (State.addr a) N := by
  refine List.mem_map.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  simp only [VG.Proof.AesSiv.Arm.descW, State.addr, Elem.size, Nat.mul_one]
  rw [show i * (2 * (32 / 8)) = 8 * i + 4 * 0 by omega, show (32 / 8 : Nat) = 4 from rfl, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, show 8 * i + 4 * 0 + 4 = 8 * i + 4 * 1 by omega]

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

/-- The entry invariant of the proofs, for the shared contracts' arguments:
`siv` is the third stack argument and `work` the fourth. -/
abbrev E0S (s : State) : Prop :=
  E0 (s.gpr .r0) (stackArg s 3) s.sp (s.gpr .r2) (stackArg s 0) (stackArg s 2) (s.gpr .r1).toNat
    (s.gpr .r3).toNat (stackArg s 1).toNat (fun i j => descW s.mem (s.gpr .r2) i j) s

set_option linter.unusedSimpArgs false in
/-- The precondition of `encrypt`'s shared contract gives the proofs' entry
invariant, with the descriptors' words in the entry memory, and `siv`
writable and apart from the data. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract Arm.abi 16).pre s) :
    E0S s ∧ Covers [⟨State.addr (stackArg s 2), 16⟩] s.wr ∧
      (⟨State.addr (stackArg s 2), 16⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, VG.Proof.AesSiv.Arm.filter_true', VG.Proof.AesSiv.Arm.filter_false', VG.Proof.AesSiv.Arm.filterMap_some',
    VG.Proof.AesSiv.Arm.filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i sp16 afit cd cT bc bd bT bw fc fd fT fw hrd hwr pw bl fl
  obtain ⟨cW, dT, dW, dA, ⟨dL, dArg⟩, tW, -, ⟨-, tArg⟩, wA, ⟨wL, wArg⟩, -⟩ := pw
  obtain ⟨bA, bL, -⟩ := bl
  obtain ⟨fA, fL⟩ := fl
  rw [stackArgAddr0] at hrd wArg dArg tArg
  have hA : (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 := by omega
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have e4 : State.addr (s.sp + BitVec.ofNat 32 4) = State.addr s.sp + BitVec.ofNat 64 4 := addr_add (by omega)
  have e8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr s.sp + BitVec.ofNat 64 8 := addr_add (by omega)
  have e12 : State.addr (s.sp + BitVec.ofNat 32 12) = State.addr s.sp + BitVec.ofNat 64 12 := addr_add (by omega)
  have mC : (⟨State.addr (s.gpr .r0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : (⟨State.addr s.sp, 16⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have mD : (⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_self
  have mT : (⟨State.addr (stackArg s 2), 16⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mW : (⟨State.addr (stackArg s 3), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have wa : ∀ r ∈ s.wr, (⟨State.addr s.sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dArg.symm
    · exact tArg.symm
    · exact wArg.symm
  refine ⟨⟨⟨⟨fc, fw, sp16, cW, bc, bw⟩, ⟨cov_mem (inRd mC), cov_mem mW⟩,
    rfl, by simp, rfl, by simp, rfl, h, afit, cov_mem (inRd mS), wArg.symm, dArg.symm, ?_, ?_, ?_, ?_,
    ⟨cov_mem (inRd mA), hA, by rw [Nat.mul_comm]; exact wA.symm, by rw [Nat.mul_comm]; exact bA, fun i hi => ?_⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, bd⟩, cov_mem mD, cd⟩, BitVec.isLt _, fT, cov_mem (inWr mT), tW, bT⟩, wa,
    fun _ _ _ _ => rfl⟩, cov_mem mT, dT.symm⟩
  · rw [stackArg, stackArgAddr0]
  · rw [stackArg, stackArgAddr, show 4 * 1 = 4 from rfl, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [stackArg, stackArgAddr, show 4 * 2 = 8 from rfl, e8]
  · rw [stackArg, stackArgAddr, show 4 * 3 = 12 from rfl, e12]
  · have hm := listed_mem s.mem (s.gpr .r2) hi
    have f := fL _ hm
    have mP : (⟨State.addr (VG.Proof.AesSiv.Arm.descW s.mem (s.gpr .r2) i 0), (VG.Proof.AesSiv.Arm.descW s.mem (s.gpr .r2) i 1).toNat⟩ : Region) ∈
        s.rd := by
      rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm))
    exact ⟨VG.Proof.AesSiv.Arm.cov_mem (inRd mP), f, (wL _ hm).symm, bL _ hm⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of `decrypt`'s shared contract gives the proofs' entry
invariant, with the descriptors' words in the entry memory. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract Arm.abi 16).pre s) : E0S s := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i sp16 afit cd bc bd bT bw fc fd fT fw hrd hwr pw bl fl
  obtain ⟨cW, -, dW, dA, ⟨dL, dArg⟩, tW, wA, ⟨wL, wArg⟩, -⟩ := pw
  obtain ⟨bA, bL, -⟩ := bl
  obtain ⟨fA, fL⟩ := fl
  rw [stackArgAddr0] at hrd wArg dArg
  have hA : (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 := by omega
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have e4 : State.addr (s.sp + BitVec.ofNat 32 4) = State.addr s.sp + BitVec.ofNat 64 4 := addr_add (by omega)
  have e8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr s.sp + BitVec.ofNat 64 8 := addr_add (by omega)
  have e12 : State.addr (s.sp + BitVec.ofNat 32 12) = State.addr s.sp + BitVec.ofNat 64 12 := addr_add (by omega)
  have mC : (⟨State.addr (s.gpr .r0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mT : (⟨State.addr (stackArg s 2), 16⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mA : (⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mS : (⟨State.addr s.sp, 16⟩ : Region) ∈ s.rd := by
    rw [hrd]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self)))
  have mD : (⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_self
  have mW : (⟨State.addr (stackArg s 3), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have wa : ∀ r ∈ s.wr, (⟨State.addr s.sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dArg.symm
    · exact wArg.symm
  refine ⟨⟨⟨fc, fw, sp16, cW, bc, bw⟩, ⟨cov_mem (inRd mC), cov_mem mW⟩,
    rfl, by simp, rfl, by simp, rfl, h, afit, cov_mem (inRd mS), wArg.symm, dArg.symm, ?_, ?_, ?_, ?_,
    ⟨cov_mem (inRd mA), hA, by rw [Nat.mul_comm]; exact wA.symm, by rw [Nat.mul_comm]; exact bA, fun i hi => ?_⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, bd⟩, cov_mem mD, cd⟩, BitVec.isLt _, fT, cov_mem (inRd mT), tW, bT⟩, wa,
    fun _ _ _ _ => rfl⟩
  · rw [stackArg, stackArgAddr0]
  · rw [stackArg, stackArgAddr, show 4 * 1 = 4 from rfl, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [stackArg, stackArgAddr, show 4 * 2 = 8 from rfl, e8]
  · rw [stackArg, stackArgAddr, show 4 * 3 = 12 from rfl, e12]
  · have hm := listed_mem s.mem (s.gpr .r2) hi
    have f := fL _ hm
    have mP : (⟨State.addr (descW s.mem (s.gpr .r2) i 0), (descW s.mem (s.gpr .r2) i 1).toNat⟩ : Region) ∈
        s.rd := by
      rw [hrd]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
    exact ⟨cov_mem (inRd mP), f, (wL _ hm).symm, bL _ hm⟩

/-- Descriptors whose bytes are the same in two memories have the same words. -/
theorem descW_eq {m m' : Mem} {a : BitVec 32} {N : Nat}
    (h : ∀ k < N * 8, m (State.addr a + BitVec.ofNat 64 k) = m' (State.addr a + BitVec.ofNat 64 k))
    {i j : Nat} (hi : i < N) (hj : j < 2) : VG.Proof.AesSiv.Arm.descW m' a i j = VG.Proof.AesSiv.Arm.descW m a i j := by
  have e := Mem.read_congr (m := m) (m' := m') (a := State.addr a + BitVec.ofNat 64 (8 * i + 4 * j))
    (n := 32 / 8) fun k hk => by rw [Offset.add_add]; exact h _ (by omega)
  simp only [VG.Proof.AesSiv.Arm.descW, Mem.readW, e]

/-- What two runs of `encrypt` or `decrypt` agree on: the stack pointer, the
arguments and the descriptors. -/
def EncPub (s₁ s₂ : State) : Prop :=
  (s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3) ∧
  ∀ i < (s₁.gpr .r3).toNat * 8, s₁.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 i) =
    s₂.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 i)

/-- The second run's entry invariant, with the first run's public values. -/
theorem encPre_pub {X : BitVec 32 → State → Prop} {s₁ s₂ : State} (E : E0S s₂) (hX : X (stackArg s₂ 2) s₂)
    (hq : EncPub s₁ s₂) :
    E0 (s₁.gpr .r0) (stackArg s₁ 3) s₁.sp (s₁.gpr .r2) (stackArg s₁ 0) (stackArg s₁ 2) (s₁.gpr .r1).toNat
      (s₁.gpr .r3).toNat (stackArg s₁ 1).toNat (fun i j => descW s₁.mem (s₁.gpr .r2) i j) s₂ ∧
      X (stackArg s₁ 2) s₂ := by
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hd⟩ := hq
  have hd' : DescEq s₂.mem (s₁.gpr .r2) (s₁.gpr .r3).toNat (fun i j => descW s₁.mem (s₁.gpr .r2) i j) :=
    fun i hi j hj => descW_eq hd hi hj
  rw [q3, q4] at hd'
  rw [q0, q1, q2, q3, q4, q5, q6, q7, q8]
  exact ⟨⟨E.pre, E.wa, hd'⟩, hX⟩

/-- `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` are constant time, given
their constant time on the entry invariant and `X` of `siv`. -/
theorem enc_ct {c : Prog isa} {k : Contract isa} {X : BitVec 32 → State → Prop}
    (hk : ∀ s, k.pre s → E0S s ∧ X (stackArg s 2) s) (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → EncPub s₁ s₂)
    (hc : ∀ {c' w sp a D T : BitVec 32} {R N n : Nat} {dsc : Nat → Nat → BitVec 32}, Lay c' w sp →
      (R = 10 ∨ R = 12 ∨ R = 14) → N < 2 ^ 32 → n < 2 ^ 32 →
      Proof.AesGcm.Arm.CT (fun s => E0 c' w sp a D T R N n dsc s ∧ X T s) c) :
    ConstantTime isa k.pre k.pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨E₁, X₁⟩ := hk _ h₁
  obtain ⟨E₂, X₂⟩ := hk _ h₂
  exact (hc E₁.pre.lay E₁.pre.rounds (BitVec.isLt _) (BitVec.isLt _) _ _ _ _ _ _
    ⟨⟨E₁, X₁⟩, encPre_pub E₂ X₂ (hpub _ _ hq)⟩ e₁ e₂).1

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data and no data, `siv` at
`0x5000` and `work` at `0x4000` (the stack arguments' words at `0x8008` and
`0x800c`). -/
def encSat (rd wr : List Region) : State :=
  { sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0) rd wr with
    mem := fun a => if a = 0x8009 then 0x50 else if a = 0x800d then 0x40 else 0 }

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract Arm.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [encSat, sivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract Arm.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [encSat, sivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0x4000, 2576⟩]

theorem encrypt_verified : Verified Arm.target encrypt (Proof.AesSiv.encryptScratchContract Arm.abi 16) := by
  refine ⟨fun s hs => ?_, enc_ct (X := fun T s => Covers [⟨State.addr T, 16⟩] s.wr)
    (fun s h => ⟨(encPre_of h).1, (encPre_of h).2.1⟩) (fun s₁ s₂ hp => ?_)
    (fun L hR hN hn => encrypt_ct L hR hN hn), encSat_pre⟩
  · obtain ⟨E, hTw, hTd⟩ := encPre_of hs
    obtain ⟨t, s', he, hq⟩ := encrypt_wp E.pre.lay E.pre hTw hTd
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at hp
    sig_split hp
    rename_i q0 q1 q2 q3 q4 q5 q6 q7 q8
    exact ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩

theorem decrypt_verified : Verified Arm.target decrypt (Proof.AesSiv.decryptScratchContract Arm.abi 16) := by
  refine ⟨fun s hs => ?_, enc_ct (X := fun _ _ => True) (fun s h => ⟨decPre_of h, trivial⟩)
    (fun s₁ s₂ hp => ?_) (fun L hR hN hn => (decrypt_ct L hR hN hn).mono fun s h => h.1), decSat_pre⟩
  · obtain ⟨t, s', he, hq⟩ := decrypt_wp (decPre_of hs).pre.lay (decPre_of hs).pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    rw [e]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptLeak, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at hp
    sig_split hp
    rename_i q0 _ q1 q2 q3 q4 q5 q6 q7 q8
    exact ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩

end VG.Proof.AesSiv.Arm

end
