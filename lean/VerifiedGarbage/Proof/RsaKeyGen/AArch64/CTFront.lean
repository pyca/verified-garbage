import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase

/-!
# A candidate on AArch64: constant time, the stages before Montgomery setup

`kMain_ct`: `kMain` leaks the same in runs that agree on the public data
(`K0`), given that Montgomery setup, Miller–Rabin and the result do from
`TS` (`kTail_ct`). `loadC` runs from `K0` (`loadC_ct`), then each check from
`KSt` (`closeCheck_ct`, `trial_ct`, `gcdCheck_ct`); after each, correctness
gives `KSt` again and the flag its branch tests as the schedule's
(`closeStage_ok`, `trialStage_ok`, `gcdStage_ok`), so both runs take the same
branch (`two_ite`).

The taint analysis knows only registers, and every load gives a secret, so
each piece is checked from registers pinned to values of the public data by
correctness: `x0` (the working space), `w` and the stride after `ws`
(`ws_ct0`), the pointers and lengths the header words give (`loadA_ct0`,
`finUsed_ct'`, `gePin_ok`), the base of `aY` and the index of its word for
`setWord` (`bdVal`), and the table's pointer and count in trial division
(`TI`, `two_loop`). `Mid c Φ a`, the states `c` reaches from states
satisfying `Φ a`, relates two runs after a piece proven constant time
without a correctness proof of its own (`two_mid`); what holds there follows
from a correctness proof of the piece (`Mid.prop`), and what the rest does
from one of the whole (`Mid.wp`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Proof.RsaKeyGen (Sched schedOf)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aY)

/-! ## Tools, and the stages' correctness -/

/-! ### Tools -/

/-- The states `c` reaches from states satisfying `Φ a`. -/
def Mid {α : Type} (c : Prog isa) (Φ : α → State → Prop) (a : α) (s : State) : Prop :=
  ∃ t tr, Φ a t ∧ Exec isa c t tr s

theorem two_mid {α : Type} {Φ : α → State → Prop} {c : Prog isa} (h : RelCT isa (Two Φ) c fun _ _ => True) :
    RelCT isa (Two Φ) c (Two (Mid c Φ)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  exact ⟨ht, a, ⟨_, _, h₁, e₁⟩, ⟨_, _, h₂, e₂⟩, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

theorem Mid.prop {α : Type} {Φ : α → State → Prop} {c : Prog isa} {P : α → State → Prop}
    (hw : ∀ a t, Φ a t → WP isa c t (P a)) {a : α} {s : State} (h : Mid c Φ a s) : P a s := by
  obtain ⟨t, tr, ht, e⟩ := h
  obtain ⟨_, u, x, y⟩ := hw a t ht
  obtain ⟨-, rfl⟩ := Exec.det e x
  exact y

theorem Mid.wp {α : Type} {Φ : α → State → Prop} {c₁ c₂ : Prog isa} {Q : α → State → Prop}
    (hw : ∀ a t, Φ a t → WP isa (.seq c₁ c₂) t (Q a)) {a : α} {s : State} (h : Mid c₁ Φ a s) :
    WP isa c₂ s (Q a) := by
  obtain ⟨t, tr, ht, e⟩ := h
  obtain ⟨_, u, x, y⟩ := hw a t ht
  cases x with
  | seq x₁ x₂ =>
    obtain ⟨-, rfl⟩ := Exec.det e x₁
    exact ⟨_, _, x₂, y⟩

/-- `Mid` of two pieces in sequence. -/
theorem Mid.seq {α : Type} {Φ : α → State → Prop} {c₁ c₂ : Prog isa} {a : α} {s : State}
    (h : Mid c₂ (Mid c₁ Φ) a s) : Mid (.seq c₁ c₂) Φ a s := by
  obtain ⟨t, tr, ⟨u, tr', hu, e₁⟩, e₂⟩ := h
  exact ⟨u, _, hu, .seq e₁ e₂⟩

theorem RelCT.assoc_r {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

/-- `pin_seq`, with no postcondition. -/
theorem pin_seq0 {α : Type} {Φ : α → State → Prop} {c₁ c₂ : Prog isa} (rs : List Reg)
    (f : α → Reg → BitVec 64) (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True)
    (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs) c₂ hc₂).isSome = true) :
    RelCT isa (Two Φ) (.seq c₁ c₂) fun _ _ => True :=
  RelCT.seq (two_post (Ψ := fun a t => ∀ r ∈ rs, t.gpr r = f a r) h₁ hp)
    (two_taint rs (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm) ht₂)

/-- `ws_ct`, with no postcondition. -/
theorem ws_ct0 {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    {body : Prog isa} (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc).isSome = true) :
    RelCT isa (Two Φ) (.seq (.block (ws ++ rest)) body) fun _ _ => True :=
  RelCT.block_seq (pin_seq0 [.x0, .x12, .x11] (fun a => wsVal (B a) (w a))
    (two_taint [.x0] (pins_ws B Z w hws) (by taint_decide)) (fun a s h => ws_pin (hws a s h)) ht)

/-- `ws_block_ct`, with no postcondition. -/
theorem ws_block_ct0 {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true) :
    RelCT isa (Two Φ) (.block (ws ++ rest)) fun _ _ => True :=
  RelCT.block_append (pin_seq0 [.x0, .x12, .x11] (fun a => wsVal (B a) (w a))
    (two_taint [.x0] (pins_ws B Z w hws) (by taint_decide)) (fun a s h => ws_pin (hws a s h)) ht)

/-- The registers `loadBE` needs pinned (`CvCT`'s `ioVal`). -/
def kioVal (B base ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => base
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

/-- The block before `loadBE`: the base of `[j]`, the pointer and the length. -/
theorem kLoadBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen])) s fun t =>
      ∀ r ∈ [Reg.x0, .x8, .x1, .x2], t.gpr r = kioVal B (off B (slot w j)) ptr len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = ptr ∧ t.gpr .x2 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hp, hl])
        rfl rfl rfl)
      fun t ⟨⟨h1, h2⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h2))

/-- `loadA j sPtr sLen`, from states with the working space and the pointer
and the length in the header slots `sPtr` and `sLen`. -/
theorem loadA_ct0 {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {j sPtr sLen : Nat}
    (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : α → Addr) (len : α → Nat)
    (hA : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a) ∧ word s.mem (B a) (8 * sPtr) = ptr a ∧
      word s.mem (B a) (8 * sLen) = BitVec.ofNat 64 (len a))
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two Φ) (seqs (loadA j sPtr sLen)) fun _ _ => True := by
  -- After the clearing: the working space and the header words.
  have hz : ∀ a s, Φ a s → WP isa (zeroA j) s fun t => Ws t (B a) (Z a) (w a) ∧
      word t.mem (B a) (8 * sPtr) = ptr a ∧ word t.mem (B a) (8 * sLen) = BitVec.ofNat 64 (len a) := by
    intro a s h
    obtain ⟨hw, hp, hl⟩ := hA a s h
    have hn := hw.scr.nowrap
    have sj := hw.sl hj
    have h256 := hw.h256
    have hs : 8 * 32 ≤ slot (w a) j := by unfold slot hdrBytes; omega
    exact WP.mono (zeroA_ok hw hj) fun t ⟨_, o, _, _, _, k⟩ =>
      ⟨hw.congr' (Frm.of_outside o (List.mem_singleton_self _)) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide),
        by rw [o.word (by omega) (by omega)]; exact hp, by rw [o.word (by omega) (by omega)]; exact hl⟩
  have e : zeroA j = .seq (.block (ws ++ (base j .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  refine RelCT.assoc (pin_seq0 [.x0, .x8, .x1, .x2]
    (fun a => kioVal (B a) (off (B a) (slot (w a) j)) (ptr a) (len a))
    (RelCT.seq (two_post (e ▸ ws_ct0 B Z w (fun a s h => (hA a s h).1) ht₁) hz)
      (two_taint [.x0] (pins_ws B Z w fun _ _ h => h.1) ht₂)) (fun a s h => ?_) ht₃)
  exact WP.seq (WP.mono (hz a s h) fun t ⟨hw, hp, hl⟩ => kLoadBlk_ok hw hP hL hp hl)

/-! ### Facts of the public data -/

theorem pins_KSt : Pins KSt [.x0] := pins_ws FPub.B FPub.Z FPub.w fun _ _ h => h.ws

theorem pins_K0 : Pins K0 [.x0] := fun _ s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  obtain ⟨-, -, _, _, m₁, -⟩ := h₁
  obtain ⟨-, -, _, _, m₂, -⟩ := h₂
  rw [m₁.x0, m₂.x0]

theorem cand_gt {w : Nat} (hw : 4 ≤ w) (x : Nat) : 8161 < Spec.RsaKeyGen.candidate (64 * w) x := by
  obtain ⟨_, hlo, _⟩ := VG.Proof.RsaKeyGen.candidate_shape (bits := 64 * w) (by omega) x
  have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-! ### The stages' correctness -/

/-- `loadC`, from `K0`. -/
theorem loadCStage_ok {q : FPub} {s : State} (h : K0 q s) : WP isa (seqs loadC) s (KSt q) := by
  obtain ⟨hw, hd, pB, r, hm, hpl, hrl, hS⟩ := h
  have hs := hm.scr
  have hnw := hs.nowrap
  have hw4 := hm.w4
  have hrk := hm.rk
  have hZ := hm.z
  have hW : ∀ {rs : List (Nat × Nat)} {m m' : Mem}, Frm q.B rs m m' → ∀ {i : Nat}, i < 32 →
      (∀ r ∈ rs, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) → word m' q.B (8 * i) = word m q.B (8 * i) :=
    fun f _ hi hd => f.word_eq hd (by omega)
  have hsrcr : Src s q.B q.Z q.rP (r.take (8 * q.w)) :=
    ⟨fun i hi => hm.rsrc.rd i (by simp at hi; omega),
      fun i hi => by rw [hm.rsrc.val i (by simp at hi; omega), List.getElem_take],
      fun i hi => hm.rsrc.out i (by simp at hi; omega)⟩
  refine WP.mono (loadC_ok hs hm.x0 hw4 (by have := hm.w64; omega) hZ hm.len hm.rand hsrcr (by simp; omega))
    fun t ⟨ht, hM, hc, hus, f, k⟩ => ?_
  have hin : InScr q.B q.Z s.mem t.mem := InScr.of_frm f (by have := ht.hZ; k_le)
  refine ⟨k.wr.trans hw, hd, ht, ⟨(hW f (by decide) (by k_disj)).trans hm.out, (hW f (by decide) (by k_disj)).trans hm.len,
    (hW f (by decide) (by k_disj)).trans hm.usedP, (hW f (by decide) (by k_disj)).trans hm.e,
    (hW f (by decide) (by k_disj)).trans hm.elen, (hW f (by decide) (by k_disj)).trans hm.p,
    by rw [← hpl]; exact (hW f (by decide) (by k_disj)).trans hm.plen,
    (hW f (by decide) (by k_disj)).trans hm.rand,
    by rw [← hrl]; exact (hW f (by decide) (by k_disj)).trans hm.rlen, hus, hM⟩,
    hm.ou.congr k.wr, pB, r, hc, hm.psrc.congrK hin k, hm.esrc.congrK hin k, hm.rsrc.congrK hin k, hpl, hrl, hS⟩

theorem w64_eq (w : Nat) : 8 * (8 * w) = 64 * w := by omega

theorem closeRanges_hd (w : Nat) : ∀ r ∈ closeRanges w, 8 * 28 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 16 ∨ r = (8 * 26, 8) := by
  simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, slot, hdrBytes, aX,
    aAcc, aTmp, aY, kT0, Public.sCnt, sFn]
  exact ⟨.inl (by omega), .inl (by omega), .inl (by omega), .inl (by omega), .inr (.inr trivial)⟩

/-- `closeCheck`, from `KSt`: `x15` the mask of the schedule's `close`. -/
theorem closeStage_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (seqs closeCheck) s fun t => KSt q t ∧ t.gpr .x15 = mask q.sch.close := by
  obtain ⟨-, hd, hws, hh, -, pB, r, hc, hp, -, -, hpl, -, hS⟩ := id h
  have hZ := hws.hZ
  refine WP.mono (closeCheck_ok hws hd.w4 hh.p (by rw [hpl]; exact hh.plen) (by rw [hpl]; exact hd.pl) hp)
    fun t ⟨h15, ht, f, k⟩ => ⟨h.step ht f (closeRanges_hd q.w) (fun r hr => ?_) (by k_disj) k, ?_⟩
  · have : r.1 + r.2 ≤ slot q.w 16 := by revert r hr; k_le
    omega
  · rw [h15, hc, ← hS, VG.Proof.RsaKeyGen.sched_close, w64_eq]

/-- `trial`, from `KSt` and a candidate not too close: `x1` not zero iff the
schedule's `comp`. -/
theorem trialStage_ok {q : FPub} {s : State} (h : KSt q s) (hcl : q.sch.close = false) :
    WP isa (seqs trial) s fun t => KSt q t ∧ (t.gpr .x1 != 0) = q.sch.comp := by
  obtain ⟨-, hd, hws, -, -, pB, r, hc, -, -, -, -, -, hS⟩ := id h
  have hz := hd.z
  have hw4 := hd.w4
  have hcl' := hcl
  rw [← hS, VG.Proof.RsaKeyGen.sched_close] at hcl'
  have hT : slot q.w aTab + 2048 ≤ q.Z := by simp only [slot, hdrBytes, aTab]; omega
  refine WP.mono (trial_ok hws hT hw4 hd.w64) fun t ⟨hx, ht, f, k⟩ =>
    ⟨h.step ht f (by k_le) (by k_le) (by k_disj) k, ?_⟩
  rw [hx, hc, VG.Proof.RsaKeyGen.trialAny_eq (cand_gt hw4 _), ← hS, VG.Proof.RsaKeyGen.sched_comp hcl', w64_eq]

/-- `gcdCheck`, from `KSt` and a candidate neither too close nor obviously
composite: `x3` not zero iff the schedule's `gbad`. -/
theorem gcdStage_ok {q : FPub} {s : State} (h : KSt q s) (hcl : q.sch.close = false) (hco : q.sch.comp = false) :
    WP isa (seqs gcdCheck) s fun t => KSt q t ∧ (t.gpr .x3 != 0) = q.sch.gbad := by
  obtain ⟨-, hd, hws, hh, -, pB, r, hc, -, he, -, -, -, hS⟩ := id h
  have hw4 := hd.w4
  have hcl' := hcl
  rw [← hS, VG.Proof.RsaKeyGen.sched_close] at hcl'
  have hco' := hco
  rw [← hS, VG.Proof.RsaKeyGen.sched_comp hcl'] at hco'
  obtain ⟨hodd, -, -⟩ := VG.Proof.RsaKeyGen.candidate_shape (bits := 64 * q.w) (by omega)
    (Spec.Rsa.os2ip (r.take (8 * q.w)))
  have h3 := cand_gt hw4 (Spec.Rsa.os2ip (r.take (8 * q.w)))
  refine WP.mono (gcdCheck_ok hws (by rw [hc]; exact hodd) (by rw [hc]; omega) hh.e hh.elen hd.el1 hd.el8 he)
    fun t ⟨hx, ht, f, k⟩ => ⟨h.step ht f (by k_le) (fun r hr => ?_) (by k_disj) k, ?_⟩
  · have : r.1 + r.2 ≤ slot q.w 16 := by revert r hr; k_le
    have := hws.hZ
    omega
  · rw [hx, hc, ← hS, VG.Proof.RsaKeyGen.sched_gbad hcl' hco', w64_eq, trial_decide_beq]

/-- `finUsed st`'s loads: `x2` the pointer to `used`. -/
theorem finUsedHead_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (.block [ldh .x3 kUsed, ldh .x2 kUsedP]) s fun t => ∀ r ∈ [Reg.x2], t.gpr r = q.up := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have h256 := hws.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.mono (WP.keep [.x2, .x3] (Q := fun t => t.gpr .x2 = q.up) (by
    brun [hws.x0, hdr_enc (show kUsed < 32 by decide), hdr_enc (show kUsedP < 32 by decide), hl kUsed (by decide),
      hl kUsedP (by decide), h.hdr.usedP]) (by decide) (by decide) (by decide +kernel)) fun t ⟨h2, _⟩ r hr => by
    rw [List.mem_singleton.mp hr]; exact h2

theorem finUsed_split (n : Nat) :
    finUsed n = .block ([ldh .x3 kUsed, ldh .x2 kUsedP] ++ ([st .x3 .x2, movi .x0 n] : List Instr)) := rfl

/-- `finUsed st` leaks the same in runs that agree on the public data. -/
theorem finUsed_ct' {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) (n : Nat)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x2]) (.block [st .x3 .x2, movi .x0 n]) hc).isSome = true) :
    RelCT isa (Two Φ) (finUsed n) fun _ _ => True := by
  rw [finUsed_split]
  exact RelCT.block_append (pin_seq0 [.x2] (fun q _ => q.up)
    (two_taint [.x0] (fun q s₁ s₂ h₁ h₂ => pins_KSt q s₁ s₂ (hΦ _ _ h₁) (hΦ _ _ h₂)) (by taint_decide))
    (fun _ _ h => finUsedHead_ok (hΦ _ _ h)) ht)

theorem finUsed2_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (finUsed 2) fun _ _ => True :=
  finUsed_ct' hΦ 2 (by taint_decide)

theorem finUsed3_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (finUsed 3) fun _ _ => True :=
  finUsed_ct' hΦ 3 (by taint_decide)

/-! ## `loadC` and `closeCheck` -/

theorem seqs_cons_ct {P Q : State → State → Prop} {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (h : RelCT isa P (.seq e (seqs l)) Q) : RelCT isa P (seqs (e :: l)) Q := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact h

/-- The working space of the public data. -/
def KW (q : FPub) (s : State) : Prop := Ws s q.B q.Z q.w

/-- A piece that changes only memory in ranges `KMut` allows keeps `KW`. -/
theorem KW.frm {q : FPub} {s t : State} (h : Ws s q.B q.Z q.w) {rs : List (Nat × Nat)} (hf : Frm q.B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : KW q t :=
  h.congr' hf hm k hr

/-- `subA o a b`, from the working space. -/
theorem subA_ct0 {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) (o a b : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.seq (.block (([movi .x7 0, .subImm .x .x15 .x7 1, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++
        (base a .x16 ++ (base b .x17 ++ base o .x8)))) (countLoop .x14 subMBody)) hc).isSome = true) :
    RelCT isa (Two Φ) (seqs (subA o a b)) fun _ _ => True := by
  have e : seqs (subA o a b) = .seq (.block (ws ++ (([movi .x7 0, .subImm .x .x15 .x7 1, mov .x14 .x12,
      .subs .x .x3 .x7 .x7] : List Instr) ++ (base a .x16 ++ (base b .x17 ++ base o .x8))))) (countLoop .x14 subMBody) := by
    simp only [subA, seqs, List.append_assoc]
  rw [e]
  exact ws_ct0 B Z w hws ht

/-- `subA o a b` keeps the working space, and leaves `x7 = 0`. -/
theorem subA_kw {q : FPub} {s : State} (h : Ws s q.B q.Z q.w) {o a b : Nat} (ho : o < 16) (ha : a < 16)
    (hb : b < 16) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (seqs (subA o a b)) s fun t => (KW q t ∧ t.gpr .x7 = 0) ∧ Outside q.B (slot q.w o) (8 * q.w) s.mem t.mem :=
  WP.mono (subA_ok h ho ha hb (.inr hoa) hob) fun _ ⟨_, o', h7, _, _, k⟩ =>
    ⟨⟨h.congr' (Frm.of_outside o' (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide), h7⟩, o'⟩

/-! ### `loadC` -/

/-- After `Keys.head`: the working space, and `rand`'s pointer and the
length in the header. -/
def LH (q : FPub) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kRand) = q.rP ∧ word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) ∧
    ∃ bs, Src s q.B q.Z q.rP bs ∧ bs.length = 8 * q.w

theorem headLH_ok {q : FPub} {s : State} (h : K0 q s) :
    WP isa (.block VG.Impl.Rsa.AArch64.Keys.head) s (LH q) := by
  obtain ⟨-, -, pB, r, hm, -, -, -⟩ := h
  have hs := hm.scr
  have hn := hs.nowrap
  have hZ := hm.z
  have hw4 := hm.w4
  have hrk := hm.rk
  have ew : wk (8 * q.w) = q.w := by simp only [wk]; omega
  refine WP.mono (kHead_ok hs hm.x0 (by omega) (by have := hm.w64; omega) (by omega) hm.len)
    fun t ⟨ht, _, f, k⟩ => ?_
  rw [ew] at ht
  have hin : InScr q.B q.Z s.mem t.mem := InScr.of_frm f (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, sW, sArr, sStride,
      Public.sMask, sFn]; omega)
  have hsrcr : Src s q.B q.Z q.rP (r.take (8 * q.w)) :=
    ⟨fun i hi => hm.rsrc.rd i (by simp at hi; omega),
      fun i hi => by rw [hm.rsrc.val i (by simp at hi; omega), List.getElem_take],
      fun i hi => hm.rsrc.out i (by simp at hi; omega)⟩
  refine ⟨ht, ?_, ?_, r.take (8 * q.w), hsrcr.congrK hin k, by simp; omega⟩
  · rw [f.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kRand,
      sW, sArr, sStride, Public.sMask, sFn]; omega) (by simp only [kRand, sFn]; omega)]; exact hm.rand
  · rw [f.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kLen,
      Public.sK, sW, sArr, sStride, Public.sMask, sFn]; omega) (by simp only [kLen, Public.sK, sFn]; omega)]
    exact hm.len

theorem loadAN_ok {q : FPub} {s : State} (h : LH q s) : WP isa (seqs (loadA aN kRand kLen)) s (KW q) := by
  obtain ⟨hw, hR, hK, bs, hsrc, hbl⟩ := h
  have := hw.w1
  exact WP.mono (loadA_ok hw (j := aN) (sPtr := kRand) (sLen := kLen) (by decide) (by decide) (by decide) hR hK
    hsrc hbl (by omega) (by omega)) fun t ⟨_, o, _, _, k⟩ => hw.congr' (Frm.of_outside o (List.mem_singleton_self _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

/-- `loadC` leaks the same in runs that agree on the public data. -/
theorem loadC_ct : RelCT isa (Two K0) (seqs loadC) fun _ _ => True := by
  unfold loadC
  simp only [List.append_assoc, List.singleton_append]
  refine seqs_cons_ct (by simp [loadA]) (RelCT.seq (two_post (two_taint [.x0] pins_K0 (by taint_decide))
    fun _ _ h => headLH_ok h) ?_)
  refine RelCT.seqs_append (by simp [loadA]) (by simp) (RelCT.seq (two_post (loadA_ct0 FPub.B FPub.Z FPub.w
    (by decide) (by decide) (by decide) FPub.rP (fun q => 8 * q.w) (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) fun _ _ h => loadAN_ok h) ?_)
  exact ws_block_ct0 FPub.B FPub.Z FPub.w (fun _ _ h => h) (by taint_decide)

/-! ### `closeCheck` -/

/-- `p`'s length into `x3`. -/
theorem closeHead_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (.block [ldh .x3 kPlen, movi .x15 0]) s fun t => KSt q t ∧ t.gpr .x3 = BitVec.ofNat 64 q.pl := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have h256 := hws.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 q.pl ∧ t.mem = s.mem) (by
    brun [hws.x0, hdr_enc (show kPlen < 32 by decide), hl kPlen (by decide), h.hdr.plen])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ =>
      ⟨h.step (hws.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide)) (rs := [])
        (fun x _ => by rw [hm]) (by simp) (by simp) (by simp) k, h3⟩

/-- With `p`: its length is `8 w`. -/
def CE (q : FPub) (s : State) : Prop :=
  (KSt q s ∧ s.gpr .x3 = BitVec.ofNat 64 q.pl) ∧ isa.eval (.zero .x .x3) s = some false

theorem CE.pl {q : FPub} {s : State} (h : CE q s) : q.pl = 8 * q.w := by
  obtain ⟨⟨hk, h3⟩, he⟩ := h
  have hd := hk.dims
  rw [eval_zero, h3] at he
  rcases hd.pl with h0 | h0
  · rw [h0] at he; simp at he
  · exact h0

theorem loadAX_ok {q : FPub} {s : State} (h : CE q s) : WP isa (seqs (loadA aX kP kPlen)) s (KW q) := by
  have hpl := h.pl
  obtain ⟨⟨hk, -⟩, -⟩ := h
  obtain ⟨-, hd, hw, hh, -, pB, r, -, hp, -, -, hpb, -⟩ := hk
  have := hw.w1
  exact WP.mono (loadA_ok hw (j := aX) (sPtr := kP) (sLen := kPlen) (by decide) (by decide) (by decide) hh.p hh.plen
    hp hpb (by omega) (by omega)) fun t ⟨_, o, _, _, k⟩ => hw.congr' (Frm.of_outside o (List.mem_singleton_self _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

/-- The working space, and the mask of the borrow in `kT0`. -/
def KT (q : FPub) (s : State) : Prop := Ws s q.B q.Z q.w ∧ ∃ b, word s.mem q.B (8 * kT0) = mask b

theorem borrow_ok {q : FPub} {s : State} (h : KW q s ∧ s.gpr .x7 = 0) :
    WP isa (.block (borrowMask ++ [sth .x15 kT0])) s (KT q) := by
  have hn := h.1.scr.nowrap
  have h256 := h.1.h256
  exact WP.mono (closeMask_ok h.1 h.2) fun t ⟨⟨_, hm⟩, k⟩ =>
    ⟨h.1.congr' (rs := [(8 * kT0, 8)]) (by rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by
      simp only [kT0, Public.sCnt, sFn]; omega)) (List.mem_singleton_self _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by simp [kT0, Public.sCnt, sFn, sArr, sStride]))
      k (by decide), _, by rw [hm]; exact word_writeW_self _ _ _ _⟩

theorem subTmp_ok {q : FPub} {s : State} (h : KT q s) : WP isa (seqs (subA aTmp aX aN)) s (KT q) := by
  obtain ⟨hw, b, hb⟩ := h
  have hn := hw.scr.nowrap
  have sT := hw.sl (show aTmp < 16 by decide)
  have hT : 8 * kT0 + 8 ≤ slot q.w aTmp := hdr_lt_slot q.w aTmp (by decide)
  exact WP.mono (subA_kw hw (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨⟨ht, _⟩, o⟩ =>
    ⟨ht, b, by rw [o.word (by omega) (by omega)]; exact hb⟩

/-- `|c − p|` into `aAcc`. -/
theorem sel_ok {q : FPub} {s : State} (h : KT q s) :
    WP isa (.seq (.block (ws ++ ldh .x15 kT0 :: mov .x14 .x12 :: (base aTmp .x16 ++ base aAcc .x17)))
      VG.Impl.Rsa.AArch64.Crt.selLoop) s (KW q) := by
  obtain ⟨hw, b, hb⟩ := h
  have hn := hw.scr.nowrap
  have hw1 := hw.w1
  have hw2 := hw.w2
  have sA := hw.sl (show aAcc < 16 by decide)
  have sT := hw.sl (show aTmp < 16 by decide)
  have eA : slot q.w aTmp = slot q.w aAcc + 8 * (q.w + 2) := by simp [slot, aTmp, aAcc]; omega
  have hh := closeSelHead_ok hw hb
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hh
  refine WP.seq (WP.mono hh fun s₆ ⟨⟨h15, h14, h16, h17, hm⟩, k₆⟩ => ?_)
  refine WP.mono (VG.Proof.Bignum.AArch64.selLoop_ok (hw.scr.congr k₆.wr) h16 h17 h14 h15 (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun t ⟨_, o, k⟩ => ?_
  rw [hm] at o
  exact hw.congr' (Frm.of_outside o (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) (k₆.trans k) (by decide)

/-- The registers `setWord aY` needs: its base, `w` and the index `w − 2`. -/
def bdVal (B : Addr) (w : Nat) : Reg → BitVec 64
  | .x8 => off B (slot w aY)
  | .x12 => BitVec.ofNat 64 w
  | .x13 => BitVec.ofNat 64 (w - 2)
  | _ => 0

theorem boundHead_ok {q : FPub} {s : State} (h : KW q s) :
    WP isa (.seq (.block [ldh .x12 sW, .movz .x .x9 0x1000 1, .subImm .x .x13 .x12 2])
      (.block [ldh .x8 (sArr aY), movi .x7 0])) s fun t => ∀ r ∈ [Reg.x8, .x12, .x13], t.gpr r = bdVal q.B q.w r := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  refine WP.seq (WP.mono (closeBound_ok h) fun s₁ ⟨⟨h12, _, h13, hm⟩, k₁⟩ => ?_)
  have sa : sArr aY < 32 := by decide
  refine WP.mono (WP.keep [.x8, .x7] (Q := fun t => t.gpr .x8 = off q.B (slot q.w aY)) (by
    brun [(k₁.gpr .x0 (by decide)).trans h.x0, hdr_enc sa, (hs.congr k₁.wr).ld (d := 8 * sArr aY) (by
      have := hdr_lt_slot q.w 8 sa; have := h.hZ; unfold slot at *; omega), hm, h.harr aY (by decide)])
    rfl rfl rfl) fun t ⟨h8, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h8
  · exact (k.gpr .x12 (by decide)).trans h12
  · exact (k.gpr .x13 (by decide)).trans h13

theorem bound_ok {q : FPub} {s : State} (h : KW q s) :
    WP isa (.seq (.block [ldh .x12 sW, .movz .x .x9 0x1000 1, .subImm .x .x13 .x12 2]) (setWord aY)) s (KW q) := by
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  refine WP.seq (WP.mono (closeBound_ok h) fun s₈ ⟨⟨h12, _, h13, m₈⟩, k₈⟩ => ?_)
  have h₈ : Ws s₈ q.B q.Z q.w := h.congr' (rs := []) (fun x _ => by rw [m₈]) (by simp) k₈ (by decide)
  exact WP.mono (setWord_ok h₈.scr h₈.x0 h₈.good.1.hdr h₈.good.2 h12 (by omega) (o := aY) (by decide)
    (i := q.w - 2) (by omega) h13) fun t ⟨_, o, k⟩ => h₈.congr' (Frm.of_outside o (List.mem_singleton_self _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

theorem pins_KW : Pins KW [.x0] := pins_ws FPub.B FPub.Z FPub.w fun _ _ h => h

/-- `closeCheck` leaks the same in runs that agree on the public data. -/
theorem closeCheck_ct : RelCT isa (Two KSt) (seqs closeCheck) fun _ _ => True := by
  simp only [closeCheck, List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.seq (two_post (two_taint [.x0] pins_KSt (by taint_decide)) fun _ _ h => closeHead_ok h) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
    (RelCT.block_nil fun _ _ _ => trivial) ?_
  -- `p` into `aX`.
  refine RelCT.seqs_append (by simp [loadA]) (by simp [subA]) (RelCT.seq (two_post (loadA_ct0 FPub.B FPub.Z FPub.w
    (Φ := CE) (by decide) (by decide) (by decide) FPub.pP FPub.pl (fun _ _ h => ⟨h.1.1.ws, h.1.1.hdr.p, h.1.1.hdr.plen⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) fun _ _ h => loadAX_ok h) ?_)
  -- `c − p`, and its borrow's mask.
  refine RelCT.seqs_append (by simp [subA]) (by simp) (RelCT.seq (two_post (subA_ct0 FPub.B FPub.Z FPub.w
    (fun _ _ h => h) aAcc aN aX (by taint_decide)) fun _ s h =>
      WP.mono (subA_kw (s := s) h (by decide) (by decide) (by decide) (by decide) (by decide)) fun _ h => h.1) ?_)
  refine seqs_cons_ct (by simp [subA]) (RelCT.seq (two_post (two_taint [.x0]
    (pins_ws FPub.B FPub.Z FPub.w fun _ _ h => h.1) (by taint_decide)) fun _ _ h => borrow_ok h) ?_)
  -- `p − c`.
  refine RelCT.seqs_append (by simp [subA]) (by simp) (RelCT.seq (two_post (subA_ct0 FPub.B FPub.Z FPub.w
    (fun _ _ h => h.1) aTmp aX aN (by taint_decide)) fun _ _ h => subTmp_ok h) ?_)
  -- `|c − p|`.
  refine RelCT.assoc (RelCT.seq (two_post (ws_ct0 FPub.B FPub.Z FPub.w (fun _ _ h => h.1) (by taint_decide))
    fun _ _ h => sel_ok h) ?_)
  -- The bound.
  refine RelCT.assoc (RelCT.seq (two_post (?_ : RelCT isa (Two KW) (.seq (.block [ldh .x12 sW,
    .movz .x .x9 0x1000 1, .subImm .x .x13 .x12 2]) (setWord aY)) fun _ _ => True) fun _ _ h => bound_ok h) ?_)
  · unfold setWord
    exact RelCT.assoc (pin_seq0 [.x8, .x12, .x13] (fun q => bdVal q.B q.w)
      (two_taint [.x0] pins_KW (by taint_decide)) (fun _ _ h => boundHead_ok h) (by taint_decide))
  -- The comparison.
  exact ws_ct0 FPub.B FPub.Z FPub.w (fun _ _ h => h) (by taint_decide)

/-! ## Trial division -/

theorem pins_nil₀ {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr (by simp)

/-- The words of the table. -/
def trN (q : FPub) : Nat := if 17 ≤ q.w then 256 else 128

/-- Before word `k` of the table. -/
def TI (q : FPub) (k : Nat) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ slot q.w aTab + 2048 ≤ q.Z ∧ s.gpr .x9 = off q.B (slot q.w aTab + 8 * k) ∧
    s.gpr .x10 = BitVec.ofNat 64 (trN q - k) ∧ s.gpr .x7 = 0 ∧ s.gpr .x8 = mask true ∧
    (∀ i < 256, word s.mem q.B (slot q.w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i)) ∧
    s.gpr .x1 = mask (anyPre (wv s.mem q.B (slot q.w aN) q.w) (4 * k))

/-- In word `k` of the table, entry by entry. -/
def TBI (p : FPub × Nat) (s : State) : Prop :=
  Ws s p.1.B p.1.Z p.1.w ∧ p.2 < 256 ∧ s.gpr .x17 = BitVec.ofNat 64 (tabWord p.2) ∧ s.gpr .x7 = 0 ∧
    s.gpr .x8 = mask true

theorem trN_le (q : FPub) : trN q ≤ 256 ∧ 1 ≤ trN q := by unfold trN; split <;> omega

/-- The table, and the counts. -/
theorem trialHead_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (.block (ws ++ base aTab .x9 ++ tabWrite ++ [movi .x3 128, movi .x4 256, movi .x5 17,
      .subs .x .x6 .x12 .x5, .csel .x .x10 .x4 .x3, movi .x1 0, movi .x7 0, .subImm .x .x8 .x7 1])) s fun t =>
      0 < trN q ∧ TI q 0 t := by
  have hw := h.ws
  have hd := h.dims
  have hn := hw.scr.nowrap
  have hz := hd.z
  have hw4 := hd.w4
  have hT : slot q.w aTab + 2048 ≤ q.Z := by simp only [slot, hdrBytes, aTab]; omega
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨⟨h12₁, h11₁, hm₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aTab .x9 ((k₁.gpr .x0 (by decide)).trans hw.x0) h11₁)
    fun s₂ ⟨⟨h9₂, hm₂, _⟩, k₂⟩ => ?_
  refine WP.mono (tabWrites_ok (hw.scr.congr (k₁.trans k₂).wr) hT h9₂ 256 (Nat.le_refl _))
    fun s₃ ⟨htab₃, ho₃, k₃⟩ => ?_
  rw [hm₂, hm₁] at ho₃
  have h12₃ : s₃.gpr .x12 = BitVec.ofNat 64 q.w :=
    (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12₁)
  refine WP.mono (trialInit_ok s₃ h12₃ hw.w2) fun s₄ ⟨⟨h10₄, h1₄, h7₄, h8₄, hm₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hf₄ : Frm q.B [(slot q.w aTab, 2048)] s.mem s₄.mem := by rw [hm₄]; exact Frm.of_outside ho₃ (by simp)
  refine ⟨(trN_le q).2, hw.congr' hf₄ (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k14
    (by decide), hT, by rw [k₄.gpr .x9 (by decide), k₃.gpr .x9 (by decide), h9₂, Nat.mul_zero, Nat.add_zero],
    by rw [h10₄, Nat.sub_zero]; rfl, h7₄, h8₄, fun i hi => by rw [hm₄]; exact htab₃ i hi,
    by rw [h1₄, Nat.mul_zero, anyPre_zero]; rfl⟩

theorem sub1_bne {n : Nat} (h1 : 1 ≤ n) (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 != 0) = decide (1 < n) := by
  have e : BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, bne, ofNat64_beq_zero (by omega)]
  by_cases hn : n - 1 = 0
  · rw [decide_eq_true hn, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false hn, decide_eq_true (by omega)]; rfl

/-- One word of the table. -/
theorem trialIter_ok {q : FPub} {k : Nat} {s : State} (hk : k < trN q) (h : TI q k s) :
    WP isa (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) s fun t =>
      isa.eval (.nonzero .x .x10) t = some (decide (k + 1 < trN q)) ∧ (k + 1 < trN q → TI q (k + 1) t) ∧
        (k + 1 = trN q → True) := by
  obtain ⟨hw, hT, h9, h10, h7, h8, htab, h1⟩ := h
  have hN := trN_le q
  refine WP.mono (tlIter_ok (s₀ := s) rfl hT (by omega) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9 h1)
    fun t ⟨⟨hI, h9', h1'⟩, h10'⟩ => ⟨?_, fun _ => ⟨hI.ws, hT, h9', ?_, hI.x7, hI.x8, fun i hi => by
      rw [hI.mem]; exact htab i hi, by rw [h1', hI.mem]⟩, fun _ => trivial⟩
  · rw [eval_nonzero, h10', h10, sub1_bne (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [h10', h10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-- An entry's prime and its inverse: registers only. -/
def entryPre (j : Nat) : List Instr :=
  (if j = 0 then [mov .x3 .x17] else [.lsr .x .x3 .x17 (16 * j)]) ++
    [.movz .x .x4 0xFFFF 0, .logic .and .x .x3 .x3 .x4] ++ minv ++ [mov .x13 .x3]

theorem entryPre_ok {p : FPub × Nat} {s : State} {j : Nat} (hj : j < 4) (h : TBI p s) :
    WP isa (.block (entryPre j)) s fun t => Ws t p.1.B p.1.Z p.1.w := by
  obtain ⟨hw, hk, h17, -, -⟩ := h
  obtain ⟨hodd, -, -⟩ := tabEntry_facts (i := 4 * p.2 + j) (by omega)
  unfold entryPre
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entrySel_ok hk hj h17) fun s₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (minv_ok s₁ (by rw [h3₁]; exact hodd)) fun s₂ ⟨_, k₂, hm₂⟩ => ?_
  refine WP.mono (WP.keep [.x13] (Q := fun t => t.mem = s₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨hm, k₃⟩ => ?_
  exact hw.congr' (rs := []) (fun x _ => by rw [hm, hm₂, hm₁]) (by simp) ((k₁.trans k₂).trans k₃) (by decide)

theorem trialEntry_eq (j : Nat) : seqs (trialEntry j) = .seq (.block (entryPre j ++ (ws ++ (base aN .x16 ++
    ([mov .x14 .x12, movi .x2 0] : List Instr)))))
    (.seq (countLoop .x14 (([ld .x5 .x16, .addImm .w .x4 .x5 0] : List Instr) ++
      redc32 ++ ([.lsr .x .x4 .x5 32] : List Instr) ++ redc32 ++ ([next .x16] : List Instr)))
    (.block [movi .x4 1, .subs .x .x3 .x2 .x4, .csel .x .x5 .x7 .x8, .logic .eor .x .x3 .x2 .x13,
      .subs .x .x3 .x3 .x4, .csel .x .x6 .x7 .x8, .logic .orr .x .x5 .x5 .x6, .logic .orr .x .x1 .x1 .x5])) := by
  simp only [trialEntry, entryPre, seqs, List.append_assoc]

/-- Entry `j` leaks the same, and keeps `TBI`. -/
theorem trialEntry_ct {j : Nat} (hj : j < 4) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (entryPre j)) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.seq (.block (base aN .x16 ++ ([mov .x14 .x12, movi .x2 0] : List Instr)))
      (.seq (countLoop .x14 (([ld .x5 .x16, .addImm .w .x4 .x5 0] : List Instr) ++ redc32 ++
        ([.lsr .x .x4 .x5 32] : List Instr) ++ redc32 ++ ([next .x16] : List Instr)))
      (.block [movi .x4 1, .subs .x .x3 .x2 .x4, .csel .x .x5 .x7 .x8, .logic .eor .x .x3 .x2 .x13,
        .subs .x .x3 .x3 .x4, .csel .x .x6 .x7 .x8, .logic .orr .x .x5 .x5 .x6, .logic .orr .x .x1 .x1 .x5])))
      hc₂).isSome = true) :
    RelCT isa (Two TBI) (seqs (trialEntry j)) (Two TBI) := by
  refine two_post ?_ fun p s h => WP.mono (trialEntry_ok h.1 h.2.1 hj h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    fun t ⟨_, hm, k⟩ => ⟨h.1.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide), h.2.1,
      (k.gpr .x17 (by decide)).trans h.2.2.1, (k.gpr .x7 (by decide)).trans h.2.2.2.1,
      (k.gpr .x8 (by decide)).trans h.2.2.2.2⟩
  rw [trialEntry_eq]
  exact RelCT.block_seq (RelCT.seq (two_post (two_taint [] (pins_nil₀ _) ht₁) fun _ _ h => entryPre_ok hj h)
    (ws_ct0 (fun p : FPub × Nat => p.1.B) (fun p => p.1.Z) (fun p => p.1.w) (fun _ _ h => h) ht₂))

/-- One word of the table leaks the same. -/
theorem trialBody_ct : RelCT isa (Two fun (p : FPub × Nat) s => p.2 < trN p.1 ∧ TI p.1 p.2 s)
    (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) fun _ _ => True := by
  simp only [List.append_assoc, List.singleton_append]
  have ne : ∀ j, trialEntry j ≠ [] := fun j => by unfold trialEntry; exact List.cons_ne_nil _ _
  refine seqs_cons_ct (by simp [ne]) (RelCT.seq (two_post (Ψ := TBI) (two_taint [.x9] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide))
    (fun p s h => ?_)) ?_)
  · obtain ⟨hk, hw, hT, h9, -, h7, h8, htab, -⟩ := h
    have hN := trN_le p.1
    exact WP.mono (tlLoad_ok hT (by omega) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9) fun t ⟨⟨h17, _, hm⟩, k⟩ =>
      ⟨hw.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide), by omega, h17,
        (k.gpr .x7 (by decide)).trans h7, (k.gpr .x8 (by decide)).trans h8⟩
  refine RelCT.seqs_append (ne 0) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 1) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 2) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 3) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  exact two_taint [] (pins_nil₀ _) (by taint_decide)

/-- `trial` leaks the same in runs that agree on the public data. -/
theorem trial_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (seqs trial) fun _ _ => True := by
  have hh := fun q s (h : Φ q s) => trialHead_ok (hΦ q s h)
  simp only [List.append_assoc] at hh
  simp only [trial, seqs, List.append_assoc]
  refine RelCT.seq (two_post (ws_block_ct0 FPub.B FPub.Z FPub.w (fun _ _ h => (hΦ _ _ h).ws) (by taint_decide)) hh)
    ((two_loop (Φ := TI) (Ψ := fun _ _ => True) trN trialBody_ct fun _ _ _ hk h => trialIter_ok hk h).mono
      (fun _ _ h => h) fun _ _ _ => trivial)

/-! ## `gcd(c − 1, e)` -/

/-- After `e` is loaded: `e` in `x3` and `kG`, and the candidate odd. -/
def GB (q : FPub) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ Spec.Rsa.os2ip q.eB < 2 ^ 64 ∧ s.gpr .x3 = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB) ∧
    word s.mem q.B (8 * kG) = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB) ∧ wv s.mem q.B (slot q.w aN) q.w % 2 = 1

/-- `GB`, and `e`'s low bit in `x5`. -/
def GE (q : FPub) (s : State) : Prop := GB q s ∧ s.gpr .x5 = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB % 2)

/-- The registers `loadE`'s loop needs: `x0`, `e`'s pointer and length. -/
def geVal (q : FPub) : Reg → BitVec 64
  | .x0 => q.B
  | .x1 => q.eP
  | .x2 => BitVec.ofNat 64 q.eB.length
  | _ => 0

theorem gePin_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (.block [ldh .x1 kE, ldh .x2 kElen, movi .x3 0]) s fun t => ∀ r ∈ [Reg.x0, .x1, .x2], t.gpr r = geVal q r := by
  have hw := h.ws
  have hs := hw.scr
  have hn := hs.nowrap
  have h256 := hw.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = q.eP ∧ t.gpr .x2 = BitVec.ofNat 64 q.eB.length)
    (by brun [hw.x0, hdr_enc (show kE < 32 by decide), hdr_enc (show kElen < 32 by decide), hl kE (by decide),
      hl kElen (by decide), h.hdr.e, h.hdr.elen]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h1, h2⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr .x0 (by decide)).trans hw.x0
  · exact h1
  · exact h2

theorem geFront_ok {q : FPub} {s : State} (h : KSt q s) :
    WP isa (.seq (seqs loadE) (.block [sth .x3 kG, movi .x4 1, .logic .and .x .x5 .x3 .x4])) s (GE q) := by
  obtain ⟨-, hd, hw, hh, -, pB, r, hc, -, he, -, -, -, -⟩ := id h
  have hs := hw.scr
  have hn := hs.nowrap
  have h256 := hw.h256
  have hw4 := hd.w4
  have hodd : wv s.mem q.B (slot q.w aN) q.w % 2 = 1 := by
    rw [hc]; exact (VG.Proof.RsaKeyGen.candidate_shape (bits := 64 * q.w) (by omega) _).1
  have hG8 : 8 * kG + 8 ≤ slot q.w aN := hdr_lt_slot q.w aN (by decide)
  have sN := hw.sl (show aN < 16 by decide)
  refine WP.seq (WP.mono (loadE_ok hw hh.e hh.elen hd.el1 hd.el8 he) fun s₁ ⟨h3₁, hm₁, k₁⟩ => ?_)
  have h₁ : Ws s₁ q.B q.Z q.w := hw.congr' (rs := []) (fun x _ => by rw [hm₁]) (by simp) k₁ (by decide)
  have hE64 : Spec.Rsa.os2ip q.eB < 2 ^ 64 := by rw [← h3₁]; exact (s₁.gpr .x3).isLt
  have hx3 : s₁.gpr .x3 = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB) := by rw [← h3₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (WP.keep [.x4, .x5] (Q := fun t => t.mem = s₁.mem.writeW (off q.B (8 * kG)) (s₁.gpr .x3) ∧
      t.gpr .x5 = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB % 2) ∧ t.gpr .x3 = s₁.gpr .x3) (by
    brun [h₁.x0, hdr_enc (show kG < 32 by decide), h₁.scr.st (d := 8 * kG) (by simp only [kG]; omega), one16]
    rw [hx3]; apply BitVec.eq_of_toNat_eq
    rw [and1_toNat]; simp only [BitVec.toNat_ofNat]; omega)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h5, h3⟩, k⟩ => ?_
  have o : Outside q.B (8 * kG) 8 s.mem t.mem := by rw [hm, hm₁]; exact writeW_outside _ _ _ (by omega)
  refine ⟨⟨hw.congr' (Frm.of_outside o (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact KMut.hdr (by simp [kG, sW])) (k₁.trans k) (by decide),
    hE64, h3.trans hx3, by rw [hm, word_writeW_self, hx3], by rw [o.wv (Or.inr hG8) (by omega)]; exact hodd⟩, h5⟩

/-- `e` odd, and `x5 = e − 1`. -/
def GE2 (q : FPub) (s : State) : Prop :=
  GB q s ∧ Spec.Rsa.os2ip q.eB % 2 = 1 ∧ s.gpr .x5 = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB) - BitVec.ofNat 64 1

theorem geDec_ok {q : FPub} {s : State} (h : GE q s ∧ isa.eval (.zero .x .x5) s = some false) :
    WP isa (.block [.subImm .x .x5 .x3 1]) s (GE2 q) := by
  obtain ⟨⟨⟨hw, hE, h3, hG, hc⟩, h5⟩, hz⟩ := h
  have hodd : Spec.Rsa.os2ip q.eB % 2 = 1 := by
    rw [eval_zero, h5, ofNat64_beq_zero (by omega)] at hz
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hz
    omega
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB) - BitVec.ofNat 64 1 ∧
      t.mem = s.mem) (by brun [h3]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h5', hm⟩, k⟩ =>
    ⟨⟨hw.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide), hE, (k.gpr .x3 (by decide)).trans h3,
      by rw [hm]; exact hG, by rw [hm]; exact hc⟩, hodd, h5'⟩

/-- Before `gcdE`: `e` odd and above 1 in `kG`, the candidate odd. -/
def GG (q : FPub) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ wv s.mem q.B (slot q.w aN) q.w % 2 = 1 ∧
    word s.mem q.B (8 * kG) = BitVec.ofNat 64 (Spec.Rsa.os2ip q.eB) ∧ 1 < Spec.Rsa.os2ip q.eB ∧
    Spec.Rsa.os2ip q.eB % 2 = 1 ∧ Spec.Rsa.os2ip q.eB < 2 ^ 64

theorem GE2.gg {q : FPub} {s : State} (h : GE2 q s ∧ isa.eval (.zero .x .x5) s = some false) : GG q s := by
  obtain ⟨⟨⟨hw, hE, -, hG, hc⟩, hodd, h5⟩, hz⟩ := h
  rw [eval_zero, h5, ofNat_sub_one_beq hE] at hz
  simp only [Option.some.injEq, decide_eq_false_iff_not] at hz
  exact ⟨hw, hc, hG, by omega, hodd, hE⟩

theorem copyKW_ok {q : FPub} {s : State} (h : GG q s) : WP isa (copyA aX aN) s (KW q) :=
  WP.mono (copyA_ok h.1 (o := aX) (a := aN) (by decide) (by decide) (by decide)) fun _ ⟨_, o, _, _, k⟩ =>
    h.1.congr' (Frm.of_outside o (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

theorem gcdE_kw {q : FPub} {s : State} (h : GG q s) : WP isa (seqs gcdE) s (KW q) :=
  WP.mono (gcdE_ok h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun _ ⟨_, ht, _⟩ => ht

/-- `gcdE` leaks the same in runs that agree on the public data. -/
theorem gcdE_ct : RelCT isa (Two GG) (seqs gcdE) (Two KW) := by
  have hw := fun q s (h : GG q s) => gcdE_kw h
  simp only [gcdE, modLoop, List.cons_append, List.nil_append, List.append_assoc] at hw ⊢
  refine RelCT.seq (two_mid (?_ : RelCT isa (Two GG) (copyA aX aN) fun _ _ => True))
    (two_post (ws_ct0 (Φ := Mid (copyA aX aN) GG) FPub.B FPub.Z FPub.w
      (fun _ _ h => Mid.prop (Φ := GG) (P := KW) (fun _ _ h => copyKW_ok h) h) (by taint_decide))
      fun _ _ h => Mid.wp (Φ := GG) hw h)
  simp only [copyA, List.append_assoc]
  exact ws_ct0 FPub.B FPub.Z FPub.w (fun _ _ h => h.1) (by taint_decide)

/-- `gcdCheck` leaks the same in runs that agree on the public data. -/
theorem gcdCheck_ct {Φ : FPub → State → Prop} (hΦ : ∀ q s, Φ q s → KSt q s) :
    RelCT isa (Two Φ) (seqs gcdCheck) fun _ _ => True := by
  unfold gcdCheck
  refine RelCT.seqs_append (by simp [loadE]) (by simp) (RelCT.assoc (RelCT.seq (two_post (Ψ := GE)
    (RelCT.assoc_r (pin_seq0 [.x0, .x1, .x2] geVal (two_taint [.x0]
      (fun q s₁ s₂ h₁ h₂ => pins_KSt q s₁ s₂ (hΦ _ _ h₁) (hΦ _ _ h₂)) (by taint_decide))
      (fun _ _ h => gePin_ok (hΦ _ _ h)) (by taint_decide))) fun _ _ h => geFront_ok (hΦ _ _ h)) ?_))
  refine RelCT.seq (?_ : RelCT isa (Two GE) _ (Two KW)) (two_taint [.x0] pins_KW (by taint_decide))
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
    (RelCT.block_nil fun _ _ h => two_mono (fun _ _ h => h.1.1.1) h) ?_
  refine RelCT.seq (two_post (two_taint [] (pins_nil₀ _) (by taint_decide)) fun _ _ h => geDec_ok h) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2, h₂.2.2])
    (RelCT.block_nil fun _ _ h => two_mono (fun _ _ h => h.1.1.1) h) ?_
  exact gcdE_ct.mono (fun _ _ h => two_mono (fun _ _ h => GE2.gg h) h) fun _ _ h => h

/-! ## `kMain` -/

theorem nonzero_false {s : State} {r : Reg} {b : Bool} (h : (s.gpr r != 0) = b)
    (he : isa.eval (.nonzero .x r) s = some false) : b = false := by
  rw [eval_nonzero, h] at he; simpa using he

/-- `kMain` leaks the same in runs that agree on the public data, given that
Montgomery setup, Miller–Rabin and the result do from `TS`. -/
theorem kMain_ct (M : Mont)
    (hT : RelCT isa (Two TS) (seqs (montSetup M.mm ++ millerRabin M.mm ++ [mrResult])) fun _ _ => True) :
    RelCT isa (Two K0) (kMain M.mm) fun _ _ => True := by
  unfold kMain
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [loadC]) (by simp [closeCheck])
    (RelCT.seq (two_post loadC_ct fun _ _ h => loadCStage_ok h) ?_)
  -- Too close to `p`.
  refine RelCT.seqs_append (by simp [closeCheck]) (by simp)
    (RelCT.seq (two_post closeCheck_ct fun _ _ h => closeStage_ok h) ?_)
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (finUsed2_ct fun _ _ h => h.1.1) ?_
  -- Trial division.
  refine RelCT.seqs_append (by simp [trial]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      (KSt q t ∧ (t.gpr .x1 != 0) = q.sch.comp) ∧ q.sch.close = false) (trial_ct fun _ _ h => h.1.1)
    fun q s h => ?_) ?_)
  · have hcl : q.sch.close = false := nonzero_false (by rw [h.1.2]; exact mask_bne _) h.2
    exact WP.mono (trialStage_ok h.1.1 hcl) fun t ht => ⟨ht, hcl⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.1.2, h₂.1.2])
    (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  -- `gcd(c − 1, e)`.
  refine RelCT.seqs_append (by simp [gcdCheck, loadE]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      (KSt q t ∧ (t.gpr .x3 != 0) = q.sch.gbad) ∧ q.sch.close = false ∧ q.sch.comp = false)
    (gcdCheck_ct fun _ _ h => h.1.1.1) fun q s h => ?_) ?_)
  · have hco : q.sch.comp = false := nonzero_false h.1.1.2 h.2
    exact WP.mono (gcdStage_ok h.1.1.1 h.1.2 hco) fun t ht => ⟨ht, h.1.2, hco⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.1.2, h₂.1.2])
    (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  -- Montgomery setup and Miller–Rabin.
  exact hT.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1, h.1.2.2, nonzero_false h.1.1.2 h.2⟩) h)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.AArch64
