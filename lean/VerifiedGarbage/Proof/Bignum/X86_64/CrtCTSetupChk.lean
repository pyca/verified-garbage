import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows

/-!
# RSA with the CRT on x86-64: constant time of the checks' pieces

Between the pieces of `checks`, what they read from the headers (`CK`: the
modulus' header, the primes' workspaces' bases, links, sizes and arrays, and
a mask in `sMask`) is kept by their frames. Each piece is constant time from
`CK` and `rdi` (`pq_ct`, `eq_ct`, `qinv_ct`, `fixP_ct`, …).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What the checks keep. -/
def CK (p : ChecksPub) (t : State) : Prop :=
  Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ word t.mem p.B (8 * sWsP) = off p.B p.op ∧
    word t.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsF t.mem p.B p.op p.wp ∧ WsF t.mem p.B p.oq p.wq ∧
    (∃ c, word t.mem p.B (8 * Public.sMask) = mask c) ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + tabBytes p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w

/-- `CK` with `rdi` at `f p`. -/
def CKr (f : ChecksPub → Addr) (p : ChecksPub) (t : State) : Prop := CK p t ∧ t.gpr .rdi = f p

theorem pins_ckr (f : ChecksPub → Addr) : Pins (CKr f) [.rdi] :=
  pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem CK.bounds {p : ChecksPub} {t : State} (h : CK p t) :
    p.B.toNat + p.Z ≤ 2 ^ 64 ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
      p.op + slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + tabBytes p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
      p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w :=
  let ⟨hs, _, _, _, _, _, _, b⟩ := h; ⟨hs.nowrap, b⟩

/-- A change above the modulus' header, keeping the primes' workspaces. -/
theorem CK.frm {p : ChecksPub} {t t' : State} (h : CK p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, 256 ≤ r.1) (hP : WsF t'.mem p.B p.op p.wp) (hQ : WsF t'.mem p.B p.oq p.wq) {regs : List Reg}
    (k : Keep regs t t') : CK p t' := by
  obtain ⟨hs, hH, hWP, hWQ, -, -, ⟨c, hM⟩, b⟩ := h
  have hn := hs.nowrap
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have hw : ∀ i < 32, word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega)) (by omega)
  exact ⟨hs.congr k.2.2, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩, (hw _ (by decide)).trans hWP,
    (hw _ (by decide)).trans hWQ, hP, hQ, ⟨c, (hw _ (by decide)).trans hM⟩, b⟩

theorem CK.mem {p : ChecksPub} {t t' : State} (h : CK p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : Keep regs t t') : CK p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (hm ▸ h.2.2.2.2.1) (hm ▸ h.2.2.2.2.2.1) k

/-- A change in the accumulators. -/
theorem CK.acc {p : ChecksPub} {t t' : State} (h : CK p t)
    (ho : Outside p.B (slot p.w Public.aAcc) (8 * (2 * p.w + 2)) t.mem t'.mem) {regs : List Reg}
    (k : Keep regs t t') : CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have hA := accs_le p.w
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h0 := hdr_lt_slot p.w Public.aAcc (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(slot p.w Public.aAcc, 8 * (2 * p.w + 2))]) ho (by simp)
  have hr : ∀ r ∈ [(slot p.w Public.aAcc, 8 * (2 * p.w + 2))], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega
  exact h.frm f (fun r hr' => by rw [List.mem_singleton.mp hr']; simp only; omega)
    (h.2.2.2.2.1.frm f (fun r hr' => Or.inr (hr r hr')) (by omega))
    (h.2.2.2.2.2.1.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega)) (by omega)) k

/-- A change of the mask. -/
theorem CK.newMask {p : ChecksPub} {t t' : State} (h : CK p t) (ho : Outside p.B (8 * Public.sMask) 8 t.mem t'.mem)
    (hM : ∃ c, word t'.mem p.B (8 * Public.sMask) = mask c) {regs : List Reg} (k : Keep regs t t') : CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 : 256 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(8 * Public.sMask, 8)]) ho (by simp)
  have hr : ∀ r ∈ [(8 * Public.sMask, 8)], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; unfold Public.sMask sFn; simp only; omega
  obtain ⟨hs, hH, hWP, hWQ, hP, hQ, -, b⟩ := h
  have hw : ∀ i < 32, i ≠ Public.sMask → word t'.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi hne =>
    ho.word (by unfold Public.sMask sFn at hne ⊢; omega) (by omega)
  exact ⟨hs.congr k.2.2, ⟨(hw _ (by decide) (by decide)).trans hH.hw, (hw _ (by decide) (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega) (by unfold sArr Public.sMask sFn; omega)).trans (hH.harr j hj)⟩,
    (hw _ (by decide) (by decide)).trans hWP, (hw _ (by decide) (by decide)).trans hWQ,
    hP.frm f (fun r hr' => Or.inr (hr r hr')) (by omega),
    hQ.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega)) (by omega), hM, b⟩

theorem ChecksPre.ck {p : ChecksPub} {s : State} (h : ChecksPre p s) : CKr (·.B) p s := by
  obtain ⟨mp, mq, P, Q, QI, m0, hg, a1, a2, b1, b2, b3, c1, c2, c3, c4, hsP, hsQ, hwsP, hwsQ, -, hM, -⟩ := h
  exact ⟨⟨hg.scr, hg.hdr, hsP, hsQ, ⟨hwsP.link, hwsP.hdr.hw, hwsP.hdr.harr⟩, ⟨hwsQ.link, hwsQ.hdr.hw, hwsQ.hdr.harr⟩,
    ⟨m0, hM⟩, a1, a2, b1, b2, b3, c1, c2, c3, c4⟩, hg.rdi⟩

theorem CK.good {p : ChecksPub} {t : State} (h : CK p t) (hdi : t.gpr .rdi = p.B) : Good t p.B p.Z p.w p.minv :=
  ⟨h.1, hdi, h.2.1⟩

theorem CK.slotZ {p : ChecksPub} {t : State} (h : CK p t) : slot p.w 8 ≤ p.Z := by
  obtain ⟨-, -, h28, hlo, hop, hoq, -⟩ := h.bounds; omega

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem CK.move {p : ChecksPub} {s : State} (h : CK p s) {X : Addr} {i : Nat} {A' : Addr}
    (hdi : s.gpr .rdi = X) (hl : InRegions (s.rd ++ s.wr) (off X (8 * i)) 8) (hw : word s.mem X (8 * i) = A') :
    WP isa (.block [.mov .rdi (.mem (hdr i))]) s (CKr (fun _ => A') p) :=
  WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = A' ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hw]) rfl) fun t ⟨⟨hdi', hm⟩, k⟩ => ⟨h.mem hm k, hdi'⟩

theorem CK.ldB {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 :=
  h.1.ld (by have := h.slotZ; have := hdr_lt_slot p.w 8 hi; omega)

theorem CK.ldP {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off (off p.B p.op) (8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wp 8 hi
  exact (h.1.sub (o := p.op) (n := slot p.wp 8) (by omega) (by omega)).ld (by omega)

theorem CK.ldQ {p : ChecksPub} {s : State} (h : CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off (off p.B p.oq) (8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wq 8 hi
  exact (h.1.sub (o := p.oq) (n := slot p.wq 8) (by omega) (by omega)).ld (by omega)

/-- `p`'s workspace. -/
abbrev ckP (p : ChecksPub) : Addr := off p.B p.op
/-- `q`'s workspace. -/
abbrev ckQ (p : ChecksPub) : Addr := off p.B p.oq

theorem enterP_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterP]) s (CKr ckP p) :=
  h.1.move (X := p.B) (i := sWsP) h.2 (h.1.ldB (by decide)) h.1.2.2.1

theorem enterQ_ck {p : ChecksPub} {s : State} (h : CKr (·.B) p s) : WP isa (.block [enterQ]) s (CKr ckQ p) :=
  h.1.move (X := p.B) (i := sWsQ) h.2 (h.1.ldB (by decide)) h.1.2.2.2.1

theorem leaveP_ck {p : ChecksPub} {s : State} (h : CKr ckP p s) : WP isa (.block [leave]) s (CKr (·.B) p) :=
  h.1.move (X := ckP p) (i := sLink) h.2 (h.1.ldP (by decide)) h.1.2.2.2.2.1.1

theorem leaveQ_ck {p : ChecksPub} {s : State} (h : CKr ckQ p s) : WP isa (.block [leave]) s (CKr (·.B) p) :=
  h.1.move (X := ckQ p) (i := sLink) h.2 (h.1.ldQ (by decide)) h.1.2.2.2.2.2.1.1

/-! ## `p q` -/

theorem CKr.rows {p : ChecksPub} {s : State} (h : CKr (·.B) p s) :
    RowsPre Public.aN ⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ s := by
  obtain ⟨⟨hs, hH, hWP, hWQ, hP, hQ, -, -, -, hlo, hop, hoq, -⟩, hdi⟩ := h
  exact ⟨hs, hdi, hH.harr _ (by decide), hWP, hWQ, hP.2.1, hQ.2.1, (hP.2.2 _ (by decide)).trans (off_off _ _ _),
    (hQ.2.2 _ (by decide)).trans (off_off _ _ _), by decide, hlo, by dsimp only; omega, by dsimp only; omega⟩

theorem pq_ct : RelCT isa (Two (CKr (·.B))) (seqs pqProduct) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · rw [pqProduct_eq]
    refine RelCT.seqs_append (by simp [zeroAccs]) (by simp) (RelCT.seq (two_post (Ψ := CKr (·.B))
      (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p s h => ⟨p.minv, h.1.good h.2, h.1.slotZ⟩)
        zeroAccs_ct) fun p s h => ?_) ?_)
    · obtain ⟨hn, -, h28, -⟩ := h.1.bounds
      exact WP.mono (zeroAccs_ok (h.1.good h.2) h.1.slotZ (by omega)) fun t ⟨_, ho, k⟩ =>
        ⟨h.1.acc ho k, (k.gpr (by decide)).trans h.2⟩
    · exact two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ : RowsPub))
        (fun p s h => h.rows) (rows_ct (by taint_decide))
  · obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, a3, a4⟩ := h.1.bounds
    have hR := h.rows
    exact WP.mono (pqProduct_ok (h.1.good h.2) (by omega) hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1
      hR.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.2.1 hlo hop hoq (show 1 ≤ p.wp by omega) a2 (show 1 ≤ p.wq by omega) a4)
      fun t ⟨_, ho, k⟩ => ⟨h.1.acc ho k, (k.gpr (by decide)).trans h.2⟩

/-! ## `p q = n` -/

/-- `eqCheck`'s registers. -/
def EQ1 (p : ChecksPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rbx = off p.B (slot p.w Public.aAcc) ∧
    t.gpr .r10 = off p.B (slot p.w Public.aN)

theorem eq_ct : RelCT isa (Two (CKr (·.B))) (seqs eqCheck) (Two (CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · unfold eqCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := EQ1) [.rdi] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (two_taint [.rdi, .r12, .rbx, .r10] (pins_of (fun (p : ChecksPub) r => if r = .rdi then p.B else
        if r = .r12 then BitVec.ofNat 64 p.w else if r = .rbx then off p.B (slot p.w Public.aAcc) else
        off p.B (slot p.w Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2) (by taint_decide))
    obtain ⟨hk, hdi⟩ := h
    have hH := hk.2.1
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = off p.B (slot p.w Public.aAcc) ∧ t.gpr .r10 = off p.B (slot p.w Public.aN))
      (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldB (i := sW) (by decide), hk.ldB (i := sArr Public.aAcc) (by decide),
        hk.ldB (i := sArr Public.aN) (by decide), hH.hw, hH.harr Public.aAcc (by decide),
        hH.harr Public.aN (by decide)]) rfl)
      fun t ⟨h', k⟩ => ⟨(k.gpr (by decide)).trans hdi, h'⟩
  · obtain ⟨hn, a1, a2, -⟩ := h.1.bounds
    obtain ⟨c, hM⟩ := h.1.2.2.2.2.2.2.1
    exact WP.mono (eqCheck_ok (h.1.good h.2) h.1.slotZ (by omega) (by omega)) fun t ⟨hM', ho, k⟩ =>
      ⟨h.1.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr (by decide)).trans h.2⟩

/-! ## `qInv < p` -/

/-- `qinvCheck`'s registers. -/
def QI1 (p : ChecksPub) (t : State) : Prop :=
  CKr ckP p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.wp ∧ t.gpr .rbx = off (ckP p) (slot p.wp aChunk) ∧
    t.gpr .r10 = off (ckP p) (slot p.wp Public.aN) ∧ t.gpr .rbp = mask false

theorem qinv_ct : RelCT isa (Two (CKr ckP)) (seqs qinvCheck) (Two (CKr ckP)) := by
  refine two_post ?_ fun p s h => ?_
  · unfold qinvCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := QI1) [.rdi] (pins_ckr _) (by taint_decide) fun p s h => ?_)
      (RelCT.seq (two_post (Ψ := CKr ckP) (two_taint [.r12, .rbx, .r10] (pins_of (fun (p : ChecksPub) r =>
        if r = .r12 then BitVec.ofNat 64 p.wp else if r = .rbx then off (ckP p) (slot p.wp aChunk) else
        off (ckP p) (slot p.wp Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2.1) (by taint_decide)) fun p s h => ?_)
      (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
        (two_piece (Ψ := fun p t => t.gpr .rax = p.B) [.rdi] (pins_ckr _) (by taint_decide) fun p s h => ?_)
        (two_taint [.rax] (pins_of (fun p _ => p.B) fun p s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)))))
    · obtain ⟨hk, hdi⟩ := h
      have hF := hk.2.2.2.2.1
      exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.wp ∧
          t.gpr .rbx = off (ckP p) (slot p.wp aChunk) ∧ t.gpr .r10 = off (ckP p) (slot p.wp Public.aN) ∧
          t.gpr .rbp = mask false ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldP (i := sW) (by decide), hk.ldP (i := sArr aChunk) (by decide),
          hk.ldP (i := sArr Public.aN) (by decide), hF.2.1, hF.2.2 aChunk (by decide),
          hF.2.2 Public.aN (by decide)]) rfl)
        fun t ⟨⟨a, b, c, d, hm⟩, k⟩ => ⟨⟨hk.mem hm k, (k.gpr (by decide)).trans hdi⟩, a, b, c, d⟩
    · obtain ⟨⟨hk, hdi⟩, h12, hbx, h10, hbp⟩ := h
      obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
      have := slot_le (w := p.wp) (show aChunk < 8 by decide)
      have := slot_le (w := p.wp) (show Public.aN < 8 by decide)
      exact WP.mono (cmpLoop_ok (hk.1.sub (o := p.op) (n := slot p.wp 8) (by omega)
        (by unfold slot hdrBytes; omega)) hbx h10 h12 hbp (by omega) (by omega) (by omega) (by omega))
        fun t ⟨_, hm, k⟩ => ⟨hk.mem hm k, (k.gpr (by decide)).trans hdi⟩
    · obtain ⟨hk, hdi⟩ := h
      exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B)
        (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldP (i := sLink) (by decide), hk.2.2.2.2.1.1]) rfl)
        fun t h => h.1
  · obtain ⟨hk, hdi⟩ := h
    obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    obtain ⟨c, hM⟩ := hk.2.2.2.2.2.2.1
    have hF := hk.2.2.2.2.1
    exact WP.mono (qinvCheck_ok hk.1 hdi (hdr_any hF.2.1 hF.2.2) (by omega)
      (by unfold Public.sMask sFn; unfold slot hdrBytes at hlo; omega) (by omega) (by omega) hF.1)
      fun t ⟨hM', ho, k⟩ => ⟨hk.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr (by decide)).trans hdi⟩

/-! ## The fixes -/

theorem pfRanges_le (wx : Nat) : ∀ r ∈ pfRanges wx, 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have := slot_le (w := wx) (show Public.aN < 8 by decide)
  have := slot_le (w := wx) (show Public.aOne < 8 by decide)
  intro r hr
  simp only [pfRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega

theorem CK.sub {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .rdi = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ p.Z) :
    ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z o p.w wx minv ∧ word s.mem p.B (8 * Public.sMask) = mask c := by
  obtain ⟨hs, hH, -, -, -, -, ⟨c, hM⟩, -⟩ := hk
  exact ⟨_, c, ⟨hs, hdi, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hhi⟩, hM⟩

theorem CK.pf {p : ChecksPub} {s : State} {o wx : Nat} (hk : CK p s) (hdi : s.gpr .rdi = off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : slot p.w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ p.Z) (h2 : 2 ≤ wx) (hwx : wx ≤ p.w) :
    PF ⟨p.B, p.Z, o, p.w, wx⟩ s := by
  have := hk.bounds
  obtain ⟨m, c, hc, hM⟩ := hk.sub hdi hF hlo hhi
  exact ⟨m, c, hc, hM, h2, by simp only; omega⟩

theorem fixP_ct : RelCT isa (Two (CKr ckP)) (seqs primeFix) (Two (CKr ckP)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.op, p.w, p.wp⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.1 hlo (by omega) a1 a2) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.1 hlo (by omega)
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := pfRanges_le p.wp
  refine WP.mono (primeFix_frm hc hM (by omega) (by omega)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega) fun r hr' => by have := hr r hr'; omega
  have hr' : ∀ r ∈ shiftRanges p.op (pfRanges p.wp), p.op + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.op + slot p.wp 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega) ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩
    (hk.2.2.2.2.2.1.frm f' (fun r h => Or.inr (by have := hr' r h; omega)) (by omega)) k, hc'.rdi⟩

theorem fixQ_ct : RelCT isa (Two (CKr ckQ)) (seqs primeFix) (Two (CKr ckQ)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.oq, p.w, p.wq⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.2.1 (by omega) hoq a3 a4) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.2.1 (by omega) hoq
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := pfRanges_le p.wq
  refine WP.mono (primeFix_frm hc hM (by omega) (by omega)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega) fun r hr' => by have := hr r hr'; omega
  have hr' : ∀ r ∈ shiftRanges p.oq (pfRanges p.wq), p.oq + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.oq + slot p.wq 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega)
    (hk.2.2.2.2.1.frm f' (fun r h => Or.inl (by have := hr' r h; omega)) (by omega))
    ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩ k, hc'.rdi⟩

end VG.Proof.Bignum.X86_64
