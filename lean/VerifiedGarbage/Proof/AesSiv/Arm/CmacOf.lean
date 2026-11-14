module

public import VerifiedGarbage.Proof.AesSiv.Arm.Env
public import VerifiedGarbage.Proof.AesCcm.Arm.Callee
public import VerifiedGarbage.Proof.AesGcm.Arm.Blocks
public import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Call
public import VerifiedGarbage.Proof.CmacAes.Arm.Verified
public import VerifiedGarbage.Impl.AesSiv.Arm
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesSiv.Arm.Call`, which only this module used -/

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

@[expose] public section

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

theorem FArgs.pre {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    Proof.CmacAes.Arm.finalizeArm.pre (view .r12 .lr s (fRd s K P L) (fWr St S)) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega_using [this])
  have hb := view_blw (ra := .r12) (rb := .lr) (rd := fRd s K P L) (wr := fWr St S) h.hsp
  simp only [Proof.CmacAes.Arm.finalizeArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, hR, hL, State.withRegions_rd, State.withRegions_wr]
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, (h.bst.sub_left slot_sub).symm,
    (h.bs.sub_left slot_sub).symm, h.bk.sub_left hb, h.bp.sub_left hb, h.bst.sub_left hb, h.bs.sub_left hb,
    h.fK, h.fSt, h.fP, h.fS, ?_, ?_, h.rounds, h.len⟩
  · rw [view_sp, hspv]; omega_using [this]
  · rw [view_sp, hspv]; have := s.sp.isLt; omega_using []

theorem fin_call {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.AesSiv.Arm.finFrame s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega_using [this])
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
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h' | h' | h' <;> omega_using [h']
  simp only [Proof.CmacAes.Arm.finalizeRawArm, Proof.CmacAes.Arm.finalizeRaw, Proof.CmacAes.Arm.mn,
    Proof.CmacAes.Arm.ciph, Proof.CmacAes.Arm.ciphAt, Proof.CmacAes.Arm.W, Proof.CmacAes.Arm.R,
    Proof.CmacAes.Arm.St, Proof.CmacAes.Arm.Dp, Proof.CmacAes.Arm.N, view_arg0 h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, hR, hL, State.withRegions_mem, State.callEntry_mem] at hpost
  have eK := keep (h.bk.sub_right (Region.sub_prefix hRb)) (by omega_using [hR])
  have eK1 : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 240) 16 =
      Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 240) 16 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 256) 16 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := keep h.bst (by decide)
  have eP := keep h.bp (by have := h.len; omega_using [hL])
  rw [eK, eK1, eK2, eSt, eP] at hpost
  rw [hm]
  exact hpost

theorem fin_rel {K St P S sp₀ : BitVec 32} {L R : Nat} {Pr : State → State → Prop}
    (h : ∀ s₁ s₂, Pr s₁ s₂ → FArgs s₁ K St P S L R ∧ FArgs s₂ K St P S L R ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
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
  refine ⟨e₁.trans e₂.symm, by omega_using [this], by have := h₂.hsp; omega_using [this], p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂,
    covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.finalizeArm, view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide),
    view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12,
    h₂.lr, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesSiv.Arm

end

end


/-!
# AES-SIV on ARMv7: the CMAC of a string (`cmacOf`)

Untrusted: everything here is checked by Lean. `cmacOf` computes the CMAC
of the string with the context's PRF into the state at `W + 176`: the code
zeroes the state, computes `16 nb`, the bytes of the whole blocks before the
last 1 to 16 (`Spec.Cmac.chainedLen`), into `r4`, chains the `nb` blocks
with `vg_cmac_aes_update` and finalizes the rest with
`vg_cmac_aes_finalize`, from the subkeys in the context
(`Siv.macWith_chained`).
-/

@[expose] public section

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
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_rest (n : Nat) : n - Spec.Cmac.chainedLen 16 n ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_div (n : Nat) : 16 * (Spec.Cmac.chainedLen 16 n / 16) = Spec.Cmac.chainedLen 16 n := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_zero : Spec.Cmac.chainedLen 16 0 = 0 := rfl

theorem chainedLen_pos {n : Nat} (_h : n ≠ 0) : Spec.Cmac.chainedLen 16 n = 16 * ((n - 1) / 16) := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_ne {n : Nat} (h : n ≠ 0) : 0 < n - Spec.Cmac.chainedLen 16 n := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem shl4 {n : Nat} (hn : 16 * n < 2 ^ 32) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- What the CMAC of a string writes: the state at `W + 176`, the working
space of the functions called and the stack below `sp`. -/
abbrev macR (w sp : BitVec 32) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 stOff, 16⟩, scrR w, blw sp]

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-! ## The calls' arguments -/

/-- A call of `vg_cmac_aes_update` with the context's key schedule, the
state at `W + st`, `n` blocks at `D` and the working space at `W + 256`. -/
theorem uargs_of {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {st : Nat}
    (hst : st + 16 ≤ 256) {D : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) (fD : D.toNat + 16 * n ≤ 2 ^ 32)
    (dC : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 st, 16⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint (scrR w))
    (dB : (blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (rD : Covers [⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr))
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 st)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 256) :
    UArgs s c (w + BitVec.ofNat 32 st) D (w + BitVec.ofNat 32 256) R n := by
  have eY := L.wA (d := st) (by omega_arith)
  have eS := L.wA (d := 256) (by decide)
  have hb := blw16_eq he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, hn, by rw [he.sp]; exact L.sp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by have := L.cw; omega_arith, ?_, fD, ?_, covers_cons (he.perm.c0C (by decide)) rD, ?_⟩
  · rw [eY]; exact L.c0_w' (by decide) (by omega_arith)
  · rw [eS]; exact L.c0_w' (by decide) (by decide)
  · rw [eY]; exact dC
  · rw [eS]; exact dS
  · rw [eY, eS]; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · rw [hb]; exact L.stk_c.sub_right (Region.sub_prefix (by decide))
  · rw [hb]; exact dB
  · rw [hb, eY]; exact L.stk_w' (by omega_arith)
  · rw [hb, eS]; exact L.stk_w' (by decide)
  · rw [L.wN (by omega_arith)]; have := L.ww; omega_arith
  · rw [L.wN (by decide)]; have := L.ww; omega_arith
  · rw [eY, eS]; exact covers_cons (he.perm.wC (by omega_arith)) (he.perm.wC (by decide))

/-- A call of `vg_cmac_aes_finalize` with the context as its key, the state
at `W + st`, the `n` last bytes at `D` and the working space at `W + 256`. -/
theorem fargs_of {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {st : Nat}
    (hst : st + 16 ≤ 256 ∨ (2432 ≤ st ∧ st + 16 ≤ 2576)) {D : BitVec 32} {n : Nat} (hn : n ≤ 16) (fD : D.toNat + n ≤ 2 ^ 32)
    (dC : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 st, 16⟩)
    (dS : (⟨State.addr D, n⟩ : Region).Disjoint (scrR w))
    (dB : (blw sp).Disjoint ⟨State.addr D, n⟩) (rD : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr))
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 st)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 256) :
    FArgs s c (w + BitVec.ofNat 32 st) D (w + BitVec.ofNat 32 256) n R := by
  have eY := L.wA (d := st) (by omega_arith)
  have eS := L.wA (d := 256) (by decide)
  have hb := blw16_eq he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, hn, by rw [he.sp]; exact L.sp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by have := L.cw; omega_arith, ?_, fD, ?_, covers_cons (he.perm.c0C (by decide)) rD, ?_⟩
  · rw [eY]; exact L.c0_w' (by decide) (by omega_arith)
  · rw [eS]; exact L.c0_w' (by decide) (by decide)
  · rw [eY]; exact dC
  · rw [eS]; exact dS
  · rw [eY, eS]; exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · rw [hb]; exact L.stk_c.sub_right (Region.sub_prefix (by decide))
  · rw [hb]; exact dB
  · rw [hb, eY]; exact L.stk_w' (by omega_arith)
  · rw [hb, eS]; exact L.stk_w' (by decide)
  · rw [L.wN (by omega_arith)]; have := L.ww; omega_arith
  · rw [L.wN (by decide)]; have := L.ww; omega_arith
  · rw [eY, eS]; exact covers_cons (he.perm.wC (by omega_arith)) (he.perm.wC (by decide))

/-! ## Zeroing a block of `W` -/

theorem zero16_ok {s : State} (he : Env c w sp R s) {d : Nat} (hd : d + 16 ≤ 2576) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 d) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (zero16 d ++ is)) s Q := by
  rw [zero16_eq, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have h11 : s₁.gpr .r11 = w := by rw [u₁.other _ (by decide), he.r11]
  refine zeroBlk_ok (by rw [u₁.gpr]; rfl) (by omega_arith) (by rw [h11]; have := L.ww; omega_arith)
    (by rw [h11, u₁.wr]; exact he.perm.wC hd) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine k s₂ (fun r hr => by rw [g₂, u₁.other _ hr]) (by rw [m₂, h11, u₁.mem]) (by rw [rd₂, u₁.rd])
    (by rw [wr₂, u₁.wr]) (by rw [sp₂, u₁.sp])

/-! ## `cmacOf` -/

/-- `cmacPre`: the state zeroed, `16 nb` in `r4`, and the arguments of the
update. -/
theorem cmacPre_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32}
    {n : Nat} (hP : Buf w sp s P n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa (cmacPre stOff) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) ∧
      UArgs s' c (w + BitVec.ofNat 32 stOff) P (w + BitVec.ofNat 32 256) R (Spec.Cmac.chainedLen 16 n / 16) ∧
      s'.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 stOff) := by
  have hcl := chainedLen_le n
  have hcd := chainedLen_div n
  rw [cmacPre]
  refine WP.seq (zero16_ok L he (d := stOff) (by decide) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_)
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
  have he₂ : Env c w sp R s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [g₂ _ (by decide), g₁ _ (by decide)])
    (by rw [k₂.sp, sp₁]) (by rw [k₂.rd, rd₁]) (by rw [k₂.wr, wr₁])
  have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n := by rw [g₂ _ (by decide), g₁ _ (by decide), h5]
  have h6₂ : s₂.gpr .r6 = P := by rw [g₂ _ (by decide), g₁ _ (by decide), h6]
  -- `r4 := 16 nb`, in both branches.
  have last : ∀ s₃ : State, Env c w sp R s₃ → s₃.rd = s.rd → s₃.wr = s.wr →
      (∀ r, r ≠ .r4 → s₃.gpr r = s₂.gpr r) → s₃.mem = s₂.mem →
      s₃.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) →
      WP isa (.block (macArgs stOff ++ [mov .r3 .r6, .mov .r12 (.shifted .r4 .lsr 4)])) s₃ fun s' =>
        Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
        s'.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) ∧
        UArgs s' c (w + BitVec.ofNat 32 stOff) P (w + BitVec.ofNat 32 256) R (Spec.Cmac.chainedLen 16 n / 16) ∧
        s'.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 stOff) := by
    intro s₃ he₃ rd₃ wr₃ g₃ m₃ h4₃
    have h6₃ : s₃.gpr .r6 = P := by rw [g₃ _ (by decide), h6₂]
    refine WP.of_runBlock ⟨_, by simp only [macArgs, csOff, stOff, mov]; arun [he₃.r9, he₃.r10, he₃.r11], ?_⟩
    have hsh : BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) >>> 4 =
        BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n / 16) := shr4 (by omega_arith)
    have hq := hP.take hcl
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, rd₃, wr₃,
      fun r a b c' d e f g => by
        simp only [gpr_setReg, a, b, c', d, f, g, ite_false, reduceCtorEq, ne_eq, not_false_eq_true]
        rw [g₃ r e, g₂ r e, g₁ r f], by simp [gpr_setReg, h4₃], ?_, by simp [mem_setReg, m₃, k₂.mem, m₁]⟩
    refine uargs_of L ?_ hR (st := stOff) (by decide)
      (n := Spec.Cmac.chainedLen 16 n / 16) (by omega_arith) (by rw [hcd]; exact hq.fit) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
      have e1 : BitVec.ofNat 32 n - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega_arith) hn
      have e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := shr4 (by omega_arith)
      have e3 : BitVec.ofNat 32 ((n - 1) / 16) <<< 4 = BitVec.ofNat 32 (16 * ((n - 1) / 16)) := shl4 (by omega_arith)
      refine ⟨_, by arun [h5₂], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, h5₂]
        rw [show (BitVec.ofNat 32 1 : BitVec 32) = 1 from rfl] at e1
        rw [chainedLen_pos h0, ← e3, ← e2, ← e1]
        rfl
      · intro r a; simp [gpr_setReg, a]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    exact last s₃ (he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr)
      (by rw [k₃.rd, k₂.rd, rd₁]) (by rw [k₃.wr, k₂.wr, wr₁]) g₃ k₃.mem h4₃

/-- `cmacMid`: the arguments of `vg_cmac_aes_finalize` for the last bytes. -/
theorem cmacMid_ok {s₂ : State} (he₂ : Env c w sp R s₂) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hn : n < 2 ^ 32)
    (hq : Buf w sp s₂ (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n))
    (h4₂ : s₂.gpr .r4 = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n)
    (h6₂ : s₂.gpr .r6 = P) :
    ∃ s₃, runBlock isa (cmacMid stOff) s₂ = some s₃ ∧ Env c w sp R s₃ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ ∧
      FArgs s₃ c (w + BitVec.ofNat 32 stOff) (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n))
        (w + BitVec.ofNat 32 256) (n - Spec.Cmac.chainedLen 16 n) R := by
  have hcl := chainedLen_le n
  have hrest := chainedLen_rest n
  refine ⟨_, by simp only [cmacMid, macArgs, csOff, stOff, mov]; arun [he₂.r9, he₂.r10, he₂.r11], ?_⟩
  have es : BitVec.ofNat 32 n - BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n) =
      BitVec.ofNat 32 (n - Spec.Cmac.chainedLen 16 n) := ofNat_sub32 hcl hn
  refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine fargs_of L ?_ hR (st := stOff) (by decide)
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
theorem cmacOf_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32}
    {n : Nat} (hP : Buf w sp s P n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa (cmacOf stOff) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (macR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 stOff) 16 =
        Spec.Siv.ctxMac s.mem (State.addr c) R (bytesAt s.mem (State.addr P) n) := by
  have hcl := chainedLen_le n
  have hcd := chainedLen_div n
  have hrest := chainedLen_rest n
  have eSt := L.wA (d := stOff) (by decide)
  have eS := L.wA (d := 256) (by decide)
  have hRb := rounds_le hR
  refine WP.seq (WP.mono (cmacPre_ok L he hR hP hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, h4₁, U, m₁⟩ => ?_)
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
  have hq : Buf w sp s₂ (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
    by_cases h0 : n - Spec.Cmac.chainedLen 16 n = 0
    · have : n = 0 := by
        by_contra hne; have := chainedLen_ne hne; omega_arith
      subst this
      rw [chainedLen_zero, show P + BitVec.ofNat 32 0 = P from BitVec.add_zero P]
      exact hP.of_eq (by rw [h₂.rd, rd₁]) (by rw [h₂.wr, wr₁])
    · exact (hP.sub (j := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega_arith)
        (by omega_arith)).of_eq (by rw [h₂.rd, rd₁]) (by rw [h₂.wr, wr₁])
  obtain ⟨s₃, run₃, he₃, g₃, k₃, F⟩ := cmacMid_ok L he₂ hR hn hq h4₂ h5₂ h6₂
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (fin_call F) fun s₄ h₄ => ?_
  have he₄ := he₃.of_saved h₄.saved h₄.sp h₄.rd h₄.wr
  have hb₁ : blw16 s₁ = blw sp := blw16_eq he₁.sp
  have hb₃ : blw16 s₃ = blw sp := blw16_eq he₃.sp
  -- The memory: what each step writes.
  have f₁ : Frame (macR w sp) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)
  have f₂ : Frame (macR w sp) s₁.mem s₂.mem := by
    have := h₂.frame; rw [eSt, eS, hb₁] at this; exact this.mono (by simp)
  have f₄ : Frame (macR w sp) s₃.mem s₄.mem := by
    have := h₄.frame; rw [eSt, eS, hb₃] at this; exact this.mono (by simp)
  have fT : Frame (macR w sp) s.mem s₄.mem := f₁.trans (f₂.trans (by rw [← k₃.mem]; exact f₄))
  refine ⟨he₄, by rw [h₄.rd, k₃.rd, h₂.rd, rd₁], by rw [h₄.wr, k₃.wr, h₂.wr, wr₁], fun r hr h4 hlr => ?_, fT, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₄.saved r hr hlr, g₃ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr, h₂.saved r hr hlr,
      g₁ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 a.2.2.2.2 hlr]
  -- What the calls read is as on entry.
  have dc : ∀ r ∈ macR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  have dp : ∀ r ∈ macR w sp, (⟨State.addr P, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
  have f₁₂ := f₁.trans f₂
  have hlt := hP.lt
  have cK {d k : Nat} (hd : d + k ≤ 512) {m' : Mem} (hf : Frame (macR w sp) s.mem m') :
      bytesAt m' (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (fun r hr => (dc r hr).sub_left (Lay.cSub hd)) (by omega_arith)
  have cP {d k : Nat} (hd : d + k ≤ n) {m' : Mem} (hf : Frame (macR w sp) s.mem m') :
      bytesAt m' (State.addr P + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr P + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (fun r hr => (dp r hr).sub_left (Offset.sub_base _ hd)) (by omega_arith)
  have k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  have sch₁ := cK (d := 0) (k := 16 * (R + 1)) (by omega_arith) f₁
  have sch₃ := cK (d := 0) (k := 16 * (R + 1)) (by omega_arith) f₁₂
  have k1 := cK (d := 240) (k := 16) (by decide) f₁₂
  have k2 := cK (d := 256) (k := 16) (by decide) f₁₂
  have pre₁ := cP (d := 0) (k := Spec.Cmac.chainedLen 16 n) (by omega_arith) f₁
  have rest₃ := cP (d := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega_arith) f₁₂
  rw [k0] at sch₁ sch₃ pre₁
  have eP : State.addr (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 n)) =
      State.addr P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) := by
    by_cases h0 : n = 0
    · subst h0; rw [chainedLen_zero]; exact addr_add (by have := P.isLt; omega_arith)
    · exact addr_add (by have := hP.fit; have := chainedLen_ne h0; omega_arith)
  have hz : bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 stOff) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero4_bytes]
  have hS : (bytesAt s.mem (State.addr P) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hsplit : n = Spec.Cmac.chainedLen 16 n + (n - Spec.Cmac.chainedLen 16 n) := by omega_arith
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
  rw [out₄, Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.macWith_chained, hS, tk, dr, Proof.Cmac.xor_comm]
  rfl

end

end VG.Proof.AesSiv.Arm
