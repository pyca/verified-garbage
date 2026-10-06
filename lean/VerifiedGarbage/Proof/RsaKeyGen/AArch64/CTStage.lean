import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase

/-!
# A candidate on AArch64: constant time, the tools and the stages' correctness

`Mid c Φ a`: the states `c` reaches from states satisfying `Φ a`. A piece
proven constant time relates two runs by `Mid` afterwards (`two_mid`), with no
correctness proof of its own; what holds there follows from a correctness
proof of the piece (`Mid.prop`), and what the rest of the code does, from one
of the whole (`Mid.wp`). `pin_seq0`, `ws_ct0` and `ws_block_ct0` are
`pin_seq`, `ws_ct` and `ws_block_ct` without a postcondition, and
`loadA_ct0` loads an array for any public data.

The stages' correctness from `KSt` (`closeStage_ok`, `trialStage_ok`,
`gcdStage_ok`), each with the flag the branch after it tests, and `loadC`'s
from `K0` (`loadCStage_ok`); `finUsed_ct`.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.RsaKeyGen (Sched schedOf)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aY)

/-! ## Tools -/

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

/-! ## Facts of the public data -/

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

/-! ## The stages' correctness -/

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

end VG.Proof.RsaKeyGen.AArch64
