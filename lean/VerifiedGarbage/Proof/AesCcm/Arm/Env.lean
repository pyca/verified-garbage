module

public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Call
public import VerifiedGarbage.Impl.AesCcm.Arm
import VerifiedGarbage.Proof.CmacAes.Arm.Verified
import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
import VerifiedGarbage.Proof.Cmac.Frame

/-! ### `AesCcm.Arm.Callee`, which the modules that import this one used -/

section

/-!
# AES-CCM on ARMv7: the calls of `vg_cmac_aes_update`

Untrusted: everything here is checked by Lean. As streaming AES-CMAC's
(`Proof/CmacAes/Stream/Arm/Call.lean`, `upd_call`, `upd_rel`), but with the
two stack arguments pushed from `r12` (the number of blocks) and `lr` (the
working space), which `seal` and `open` do not keep across calls: what a
call needs (`UArgs`), what it leaves (`UPost`), and that two calls with the
same arguments leak the same (`upd_rel`). The calls of `vg_aes_ctr32` are
AES-GCM's (`Proof.AesGcm.Arm.ctr_call`, `ctr_rel`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.CmacAes.Stream.Arm (view blw16 view_gpr view_sp view_arg0 view_arg1 view_argAddr view_blw spA
  slot_sub push_frame cov_push covW_push WP.frameCallF RelCT.frameCall stackUse_update uRd uWr)
open VG.Proof.CmacAes.Arm (toNat_rounds)

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`, with `n` in `r12` and `S` in `lr`, to push. -/
structure UArgs (s : State) (W C D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 32
  hsp : 16 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  dc : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (blw16 s).Disjoint ⟨State.addr W, 240⟩
  bd : (blw16 s).Disjoint ⟨State.addr D, 16 * n⟩
  bc : (blw16 s).Disjoint ⟨State.addr C, 16⟩
  bs : (blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩, blw16 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr C) 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16) (Spec.Cmac.blocksAt s.mem (State.addr D) 16 n)

theorem UArgs.pre {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n) :
    Proof.CmacAes.Arm.updateArm.pre (view .r12 .lr s (uRd s W D n) (uWr C S)) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega_using [this])
  have hb := view_blw (ra := .r12) (rb := .lr) (rd := uRd s W D n) (wr := uWr C S) h.hsp
  have hslot : Region.Sub ⟨stackArgAddr (view .r12 .lr s (uRd s W D n) (uWr C S)) 0, 8⟩ (blw16 s) := by
    rw [view_argAddr h.hsp]; exact slot_sub
  simp only [Proof.CmacAes.Arm.updateArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, hR, hN, State.withRegions_rd, State.withRegions_wr]
  rw [view_argAddr h.hsp] at hslot
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, (h.bc.sub_left slot_sub).symm,
    (h.bs.sub_left slot_sub).symm, h.bw.sub_left hb, h.bd.sub_left hb, h.bc.sub_left hb, h.bs.sub_left hb,
    h.fW, h.fC, h.fD, h.fS, ?_, ?_, h.rounds⟩
  · rw [view_sp, hspv]; omega_using [this]
  · rw [view_sp, hspv]; have := s.sp.isLt; omega_using []

theorem upd_call {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n) :
    WP isa Impl.AesCcm.Arm.updFrame s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega_using [this])
  refine WP.frameCallF (k := Proof.CmacAes.Arm.updateArm) (fun _ hs => Proof.CmacAes.Arm.update_wp hs)
    stackUse_update rfl h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bc
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := push_frame h.hsp .r12 .lr
  have keep : ∀ {p : Addr} {k : Nat}, (blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega_using [h']
  simp only [Proof.CmacAes.Arm.updateArm, Proof.CmacAes.Arm.ciphAt, view_arg0 h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, hR, hN, State.withRegions_mem, State.callEntry_mem] at hpost
  rw [Proof.Cmac.bytesAt_frame hm (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h.bc.symm) (by decide),
    hpost, keep (h.bw.sub_right (Region.sub_prefix hRb)) (by omega_using [hR]), keep h.bc (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep (h.bd.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega_using [hi]

theorem upd_rel {W C D S sp₀ : BitVec 32} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Impl.AesCcm.Arm.updFrame fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.updateArm) (rd := [⟨State.addr W, 240⟩,
    ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := uWr C S)
    (fun _ hs => Proof.CmacAes.Arm.update_wp hs) Proof.CmacAes.Arm.update_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : uRd s₁ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₁]
  have r₂ : uRd s₂ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₂]
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
  simp only [Proof.CmacAes.Arm.updateArm, view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide),
    view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12,
    h₂.lr, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCcm.Arm

end

end

/-!
# AES-CCM on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The key schedule (240 bytes
at `k`), the working space (2560 bytes at `w`) and the 16 bytes of stack
below `sp` that the calls use (`Lay`), all 32-bit pointers; what a state may
access (`Perm`); and the registers holding `k`, `w`, the number of rounds
and `q − 1`, and the stack pointer (`Env`). The pieces write the parts of
`W` in `mutR` (and the data, and the stack below `sp`), so our caller's
registers saved in `W` stay as the entry left them.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (covers_off in_off in_left covers_left covers_of_mem covers_prefix)

/-- The 16 bytes below `sp`. -/
abbrev blw (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 16, 16⟩

/-- The key schedule, `W` and the stack below `sp` used by the calls. -/
structure Lay (k w sp : BitVec 32) : Prop where
  kw : k.toNat + 240 ≤ 2 ^ 32
  ww : w.toNat + 2560 ≤ 2 ^ 32
  sp16 : 16 ≤ sp.toNat
  k_w : (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk_k : (blw sp).Disjoint ⟨State.addr k, 240⟩
  stk_w : (blw sp).Disjoint ⟨State.addr w, 2560⟩

/-- What a state may access. -/
structure Perm (k w : BitVec 32) (s : State) : Prop where
  k : Covers [⟨State.addr k, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨State.addr w, 2560⟩] s.wr

/-- The registers holding the rounds `R`, the key schedule, `q − 1` and `W`,
the stack pointer, and what the state may access. -/
structure Env (k w sp : BitVec 32) (R q1 : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  r9 : s.gpr .r9 = k
  r10 : s.gpr .r10 = BitVec.ofNat 32 q1
  r11 : s.gpr .r11 = w
  sp : s.sp = sp
  perm : Perm k w s

theorem Perm.of_eq {k w : BitVec 32} {s s' : State} (h : Perm k w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm k w s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r8`–`r11`, `sp` and the permissions. -/
theorem Env.keep {k w sp : BitVec 32} {R q1 : Nat} {s s' : State} (h : Env k w sp R q1 s)
    (hg : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env k w sp R q1 s' :=
  ⟨by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9], by rw [hg _ (by simp), h.r10],
    by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- After code that keeps the callee-saved registers (but `lr`). -/
theorem Env.of_saved {k w sp : BitVec 32} {R q1 : Nat} {s s' : State} (h : Env k w sp R q1 s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env k w sp R q1 s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {k w sp : BitVec 32} (L : Lay k w sp)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 2560) : State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega_using [hd, this])

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d m : Nat} (h : a + n ≤ d ∨ d + m ≤ a) (ha : a + n ≤ 2560) (hd : d + m ≤ 2560) :
    (⟨State.addr w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, m⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha]) (by have := L.ww; omega_using [hd])

theorem wN {d : Nat} (hd : d < 2560) : (w + BitVec.ofNat 32 d).toNat = w.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (blw sp).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

theorem k_w' {a n : Nat} (ha : a + n ≤ 2560) :
    (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.k_w.sub_right (wSub ha)

end Lay

namespace Perm

variable {k w : BitVec 32} {s : State} (P : Perm k w s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (State.addr w + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (State.addr w + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr w + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at the 32-bit pointer `D` that the code may read,
apart from `W`, the key schedule and the stack below `sp`. -/
structure Buf (w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr)
  fit : D.toNat + n ≤ 2 ^ 32
  w : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (blw sp).Disjoint ⟨State.addr D, n⟩

namespace Buf

variable {w sp : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Buf w sp s D n)
include h

theorem lt : n < 2 ^ 64 := by have := h.fit; omega_using [this]

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf w sp s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- Byte `j` of the buffer, for `j < n`, as a 64-bit address. -/
theorem addr {j : Nat} (hj : j < n) : State.addr (D + BitVec.ofNat 32 j) = State.addr D + BitVec.ofNat 64 j :=
  addr_add (by have := h.fit; omega_using [hj, this])

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_using [hj, this]), Nat.mod_eq_of_lt (by omega_using [hj, this])]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf w sp s D k where
  rd := covers_prefix h.rd hk
  fit := by have := h.fit; omega_using [hk, this]
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : Buf w sp s (D + BitVec.ofNat 32 j) k := by
  have ha := h.addr (j := j) (by omega_using [hjk, hk])
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]; exact covers_off h.rd hjk h.lt
  · rw [h.toNat_add (by omega_using [hjk, hk])]; have := h.fit; omega_using [hjk, this]
  · rw [ha]; exact h.w.sub_left hs
  · rw [ha]; exact h.stk.sub_right hs

end Buf

end VG.Proof.AesCcm.Arm
