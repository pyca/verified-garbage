import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
import VerifiedGarbage.Proof.Framework.X86_64.Narrow

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. Between the pieces, each run
has the public arguments, some `Ctr₀`, its buffers and the address of `tag`
on the stack (`Mid`), which every piece keeps (`ctrs_mid`, `mac_mid`,
`tag_mid`, `ctr_mid`); the pieces are related from it (`mac_rel`, `tag_rel`,
`crypt_rel`), and the entry, which loads `W` from the stack first, by the
taint analysis from the public arguments (`entry_rel`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its pieces before the copy
of the tag do not, and run the same from its states with `tag` only readable
(`rel_narrow`). The copy of the tag and the exit are related by the taint
analysis from the registers that correctness says agree (`sealTail_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- The address of `tag`, `T`, at `SP + 24`, apart from what the pieces
write. -/
structure ArgT (W SP D : Addr) (n : Nat) (T : Addr) (s : State) : Prop where
  val : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  rd : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8
  w : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩
  d : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩

theorem ArgT.mut {W SP D T : Addr} {n : Nat} {s s' : State} (h : ArgT W SP D n T s)
    (hf : Frame (mutR W SP D n) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgT W SP D n T s' :=
  ⟨by rw [argT_kept (hf.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩) h.w h.d, h.val],
    by rw [hrd, hwr]; exact h.rd, h.w, h.d⟩

/-- A run between the pieces: the public arguments, some `Ctr₀` at `W + 48`,
the associated data and the data in its regions, and the address of the
tag. -/
def Mid (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  One K W SP R N A D nl al n tl s ∧ C0 W nl s ∧ Buf K W SP s A al ∧ Buf K W SP s D n ∧ ArgT W SP D n T s

theorem ctrs_mid {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {s : State}
    (o : One K W SP R N A D nl al n tl s) (hN : Buf K W SP s N nl) (hA : Buf K W SP s A al)
    (hD : Buf K W SP s D n) (hT : ArgT W SP D n T s) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa ctrs s (Mid K W SP R N A D nl al n tl T) :=
  WP.mono (ctrs_ok o.env o.sl hN h7 h13) fun _ ⟨E, f, c, rd, wr⟩ =>
    have f' : Frame (mutR W SP D n) s.mem _ := (f.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩).sub
      (wR_mut W SP D n)
    ⟨⟨E, slots_mut L hD.w f' o.sl, wr.trans o.wr⟩, ⟨_, length_bytesAt _ _ _, c⟩, hA.of_eq rd wr, hD.of_eq rd wr,
      hT.mut f' rd wr⟩

theorem mac_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : Mid K W SP R N A D nl al n tl T s) : WP isa (mac v.callee v.suffix y) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (mac_ok v L o.env o.sl hR hl h7 h13 ht4 ht16 hte hn' c hy hA hD) fun s' M => ?_
  refine ⟨o.macR L hD.w (by omega) M.env M.frame M.wr, ⟨nonce, hl, ?_⟩, hA.of_eq M.rd M.wr, hD.of_eq M.rd M.wr,
    hT.mut (M.frame.sub (macR_mut W SP D n (by omega))) M.rd M.wr⟩
  rw [bytesAt_frame M.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide), c]

theorem tag_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : Mid K W SP R N A D nl al n tl T s) : WP isa (tag v.callee y) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (tag_ok v L o.env hR o.sl.rounds (by omega) (by omega) c hy) fun s' ⟨E, _, rd, wr, f, _⟩ => ?_
  have f' : Frame (mutR W SP D n) s.mem s'.mem := f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨wA W, by simp, Offset.sub_base W (by omega)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨⟨E, slots_mut L hD.w f' o.sl, wr.trans o.wr⟩, ⟨nonce, hl, ?_⟩, hA.of_eq rd wr,
    hD.of_eq rd wr, hT.mut f' rd wr⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide), c]

/-- The context of counter mode, from a run between the pieces. -/
theorem Mid.ctx {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : Mid K W SP R N A D nl al n tl T s) :
    ∃ nonce, CtrCtx K W SP s R nonce D n := by
  obtain ⟨o, ⟨nonce, hl, c⟩, -, hD, -⟩ := h
  exact ⟨nonce, L, hR, o.sl.rounds, by omega, by omega, by rw [hl]; exact hn', c, hD,
    by rw [o.wr]; exact covers_of_mem List.mem_cons_self, hdk⟩

theorem ctr_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : Mid K W SP R N A D nl al n tl T s) :
    WP isa (ctr v.callee) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨nonce, C⟩ := h.ctx L hR h7 h13 hn' hdk
  obtain ⟨o, ⟨nonce', hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (ctr_ok v C o.env o.sl) fun s' ⟨E, rd, wr, f, _⟩ => ?_
  refine ⟨⟨E, slots_mut L hD.w (f.sub (ctrR_mut W SP D n)) o.sl, wr.trans o.wr⟩, ⟨nonce', hl, ?_⟩,
    hA.of_eq rd wr, hD.of_eq rd wr, hT.mut (f.sub (ctrR_mut W SP D n)) rd wr⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (hD.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c]

/-- A run after the entry: the public arguments, its buffers and the address
of the tag. -/
def Pre₀ (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  One K W SP R N A D nl al n tl s ∧ Buf K W SP s N nl ∧ Buf K W SP s A al ∧ Buf K W SP s D n ∧
    ArgT W SP D n T s

theorem ctrs_check : ∃ hc, (taint.check (ccmT []) ctrs hc).isSome = true := ⟨_, by taint_decide⟩

theorem restore_check : ∃ hc, (taint.check (ccmT []) (.block restore) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `seal` after its entry, up to the copy of the tag, in two runs. -/
theorem sealFront_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 64) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Pre₀ K W SP R N A D nl al n tl T s₁ ∧ Pre₀ K W SP R N A D nl al n tl T s₂) :
    RelCT isa P (sealFront v.callee v.suffix) fun s₁ s₂ =>
      True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂ := by
  have r₁ := (rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) ctrs_check).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T) fun s₁ s₂ h => by
      obtain ⟨⟨o₁, n₁, a₁, d₁, t₁⟩, ⟨o₂, n₂, a₂, d₂, t₂⟩⟩ := hP _ _ h
      exact ⟨ctrs_mid L o₁ n₁ a₁ d₁ t₁ h7 h13, ctrs_mid L o₂ n₂ a₂ d₂ t₂ h7 h13⟩
  have r₂ := (mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1⟩,
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.1,
      mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.2⟩
  have r₃ := (tag_rel v L hR hDW hn h7 h13 (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨tag_mid v L hR h7 h13 (.inl rfl) h.2.1, tag_mid v L hR h7 h13 (.inl rfl) h.2.2⟩
  have r₄ := (rel_of_pt (c := ctr v.callee)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact crypt_rel v C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨ctr_mid v L hR h7 h13 hn' hdk h.2.1, ctr_mid v L hR h7 h13 hn' hdk h.2.2⟩
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (r₄.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩)))

/-- `seal` after its entry, up to the copy of the tag, in one run. -/
theorem sealFront_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {s : State} (h : Pre₀ K W SP R N A D nl al n tl T s) :
    WP isa (sealFront v.callee v.suffix) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, hN, hA, hD, hT⟩ := h
  exact WP.seq (WP.mono (ctrs_mid L o hN hA hD hT h7 h13) fun _ h₁ =>
    WP.seq (WP.mono (mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h₁) fun _ h₂ =>
    WP.seq (WP.mono (tag_mid v L hR h7 h13 (.inl rfl) h₂) fun _ h₃ => ctr_mid v L hR h7 h13 hn' hdk h₃)))

/-! ## Moving the tag to the regions read only -/

/-- `s` with the tag `⟨T, tl⟩` read only, and the data and `W` its writable
regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T : Addr) (tl : Nat) (W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 2560⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-! ## The copy of the tag and the exit -/

/-- What the copy of the tag needs of a run: `r15` and `rsp` hold `W` and
`SP`, the tag length is in its slot, and the address of the tag `T` on the
stack, all where the run may read them. -/
def SealOut (W SP T : Addr) (tl : Nat) (s : State) : Prop :=
  s.gpr .r15 = W ∧ s.gpr .rsp = SP ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 tl ∧
    InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 ∧ s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8

theorem Mid.sealOut {K W SP : Addr} {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {σ s : State}
    (h : Mid K W SP R N A D nl al n tl T σ) (hg : σ.gpr = s.gpr) (hm : σ.mem = s.mem)
    (hc : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) : SealOut W SP T tl s := by
  obtain ⟨o, -, -, -, hT⟩ := h
  refine ⟨by rw [← hg]; exact o.env.r15, by rw [← hg]; exact o.env.rsp, by rw [← hm]; exact o.sl.tl,
    hc _ _ (o.env.perm.wR (show 208 + 8 ≤ 2560 by decide)), by rw [← hm]; exact hT.val, hc _ _ hT.rd⟩

/-- The arguments of the copy of the tag. -/
theorem tagOutArgs_ok {W SP T : Addr} {tl : Nat} {s : State} (h : SealOut W SP T tl s) :
    WP isa (.block [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))]) s
      fun s' => s'.gpr .rdi = T ∧ s'.gpr .rsi = W ∧ s'.gpr .rcx = BitVec.ofNat 64 tl ∧ s'.gpr .r15 = W := by
  obtain ⟨h15, hsp, htl, r₁, hT, r₂⟩ := h
  refine WP.of_runBlock ⟨_, by crun [h15, hsp, r₁, r₂], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hsp, hT]
  · simp [gpr_setReg, h15]
  · simp [gpr_setReg, htl]
  · simp [gpr_setReg, h15]

theorem tagOutArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r15, .rsp])
    (.block [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))]) hc).isSome =
      true := ⟨_, by taint_decide⟩

theorem tagCopy_check : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rcx, .r15])
    (.seq copyLoop (.block restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `(a; b); c`, related as `a; (b; c)`. -/
theorem rel_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- The copy of the tag and the exit, in two runs with the same `W`, `SP`,
tag length and tag. -/
theorem sealTail_rel {W SP T : Addr} {tl : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → SealOut W SP T tl s₁ ∧ SealOut W SP T tl s₂) :
    RelCT isa P (.seq tagOut (.block restore)) fun _ _ => True := by
  have a := (rel_taintR (P := P) [.r15, .rsp] (fun s₁ s₂ h r hr => by
      obtain ⟨⟨a₁, b₁, -⟩, ⟨a₂, b₂, -⟩⟩ := hP _ _ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) tagOutArgs_check).wp
    (F₁ := fun (s : State) => s.gpr .rdi = T ∧ s.gpr .rsi = W ∧ s.gpr .rcx = BitVec.ofNat 64 tl ∧ s.gpr .r15 = W)
    (F₂ := fun (s : State) => s.gpr .rdi = T ∧ s.gpr .rsi = W ∧ s.gpr .rcx = BitVec.ofNat 64 tl ∧ s.gpr .r15 = W)
    fun _ _ h => ⟨tagOutArgs_ok (hP _ _ h).1, tagOutArgs_ok (hP _ _ h).2⟩
  have b := rel_taintR (P := fun s₁ s₂ => True ∧
      (s₁.gpr .rdi = T ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 tl ∧ s₁.gpr .r15 = W) ∧
      (s₂.gpr .rdi = T ∧ s₂.gpr .rsi = W ∧ s₂.gpr .rcx = BitVec.ofNat 64 tl ∧ s₂.gpr .r15 = W))
    (c := .seq copyLoop (.block restore)) [.rdi, .rsi, .rcx, .r15] (fun _ _ h r hr => by
      obtain ⟨-, ⟨a₁, b₁, c₁, d₁⟩, ⟨a₂, b₂, c₂, d₂⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [d₁, d₂]) tagCopy_check
  exact rel_assoc' (RelCT.seq a b)

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 40) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 40))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by crun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 40))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 40) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 40) 8)
    (hE₁ : WP isa (.block entry) s₀ F₁) (hE₂ : WP isa (.block entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨loadW_ok hr₁, loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 40))]) (l₂ := entry.tail) (RelCT.seq l
      (rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

/-- What the entry leaves, for the arguments: the environment, the slots, the
same permissions, and the address of the tag still at `SP + 24`. -/
theorem entry_post {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (.block entry) s fun s₁ => Env K W SP s₁ ∧ Slots W R N A D nl al n tl s₁.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ ArgT W SP D n T s₁ := by
  obtain ⟨s₁, run₁, E₁, S₁, _, f₁, rd₁, wr₁⟩ :=
    entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  have hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8 := by
    have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    exact h
  refine WP.of_runBlock ⟨s₁, run₁, E₁, S₁, rd₁, wr₁, ⟨?_, by rw [rd₁, wr₁]; exact hTr, Ar.argsW, Ar.argsD⟩⟩
  rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact argT_disj (n := n) Ar.argsW Ar.argsD _ List.mem_cons_self) (by decide), hT]

theorem argW_in {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} (Ar : Args s K W SP N A D R nl al n tl)
    (hsp : s.gpr .rsp = SP) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 40) 8 := by
  have h := in_off (d := 32) (n := 8) Ar.args (by decide) (by decide)
  rw [add_ofNat_assoc] at h
  rw [hsp]; exact h

theorem pub_regs {s₀ s₀' : State} (hq : onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-- What the entry of `seal` leaves: with the tag read only, a run after the
entry. -/
def SealIn (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩] ∧ Pre₀ K W SP R N A D nl al n tl T (narrowT D n T tl W s)

theorem sealIn_of {s s₁ : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hwr : s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩])
    (h : Env K W SP s₁ ∧ Slots W R N A D nl al n tl s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ ArgT W SP D n T s₁) :
    SealIn K W SP R N A D nl al n tl T s₁ := by
  obtain ⟨E, S, rd, wr, hT⟩ := h
  have hwr₁ : s₁.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩] := by rw [wr]; exact hwr
  have hc : Covers (s₁.rd ++ s₁.wr) ((narrowT D n T tl W s₁).rd ++ (narrowT D n T tl W s₁).wr) := by
    rw [hwr₁]; exact covers_narrowT _ _ _ _
  have hb : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → Buf K W SP (narrowT D n T tl W s₁) P len := fun hP =>
    { hP.of_eq rd wr with rd := (hP.of_eq rd wr).rd.trans hc }
  exact ⟨hwr₁, ⟨⟨E.r13, E.r15, E.rsp, E.perm.k.trans hc, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩, S, rfl⟩, hb Ar.nonce, hb Ar.aad, hb Ar.data,
    ⟨hT.val, hc _ _ hT.rd, hT.w, hT.d⟩⟩

theorem entry_seal {s : State} (hp : sealX86_64.pre s) :
    WP isa (.block entry) s (SealIn (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .r8)
      (arg s 0) (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2)) :=
  WP.mono (entry_post (args_of_seal hp).1.1 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
      (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm)
    fun _ h => sealIn_of (args_of_seal hp).1.1 hp.2.1 h

/-- The second run, with the first's public arguments. -/
theorem entry_seal_pub {s₀ s₀' : State} (hp' : sealX86_64.pre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (SealIn (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .r8) (arg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat
      (arg s₀ 2)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), qa 3 (by decide), qa 4 (by decide), q1, q2, q3, q4,
    q5, q6, q7]
  exact entry_seal hp'

/-- `vg_aes_ccm_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : Ctr32Impl) {s₀ s₀' : State} (hp : sealX86_64.pre s₀) (hp' : sealX86_64.pre s₀')
    (hq : sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callee v.suffix) fun _ _ => True := by
  have Ar := (args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 4 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_seal hp').1.1 rfl) (entry_seal hp) (entry_seal_pub hp' hq)) ?_
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := sealFront v.callee v.suffix)
    (P := fun s₁ s₂ => True ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat (arg s₀ 2) s₁ ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat (arg s₀ 2) s₂)
    [⟨arg s₀ 2, (arg s₀ 3).toNat⟩]
    [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 4, 2560⟩]
    (sealFront_rel v L Ar.rounds Ar.data.w hn Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.aad.lt Ar.hn Ar.dk
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 2, (arg s₀ 3).toNat⟩, ⟨arg s₀ 4, 2560⟩] →
          Covers ([⟨arg s₀ 2, (arg s₀ 3).toNat⟩] ++ [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 4, 2560⟩]) s.wr ∧
          Covers [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 4, 2560⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := sealFront_mid v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn Ar.dk p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := sealFront_mid v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn Ar.dk p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (sealTail_rel fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.sealOut g₁ h₁ c₁, m₂.sealOut g₂ h₂ c₂⟩)

theorem seal_ct (v : Ctr32Impl) : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCcm.X86_64
