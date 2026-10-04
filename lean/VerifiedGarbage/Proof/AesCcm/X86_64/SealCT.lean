import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Seal

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. Between the pieces, each run
has the public arguments, some `Ctr₀` and its buffers (`Mid`), which every
piece keeps (`ctrs_mid`, `mac_mid`, `tag_mid`, `ctr_mid`); the pieces are
related from it (`mac_rel`, `tag_rel`, `crypt_rel`), and the entry, which
loads `W` from the stack first, by the taint analysis from the public
arguments (`entry_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
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

/-- A run between the pieces: the public arguments, some `Ctr₀` at `W + 48`,
and the associated data and the data in its regions. -/
def Mid (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (s : State) : Prop :=
  One K W SP R N A D nl al n tl s ∧ C0 W nl s ∧ Buf K W SP s A al ∧ Buf K W SP s D n

theorem ctrs_mid {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat} {s : State}
    (o : One K W SP R N A D nl al n tl s) (hN : Buf K W SP s N nl) (hA : Buf K W SP s A al)
    (hD : Buf K W SP s D n) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) : WP isa ctrs s (Mid K W SP R N A D nl al n tl) :=
  WP.mono (ctrs_ok o.env o.sl hN h7 h13) fun _ ⟨E, f, c, rd, wr⟩ =>
    ⟨⟨E, slots_mut L hD.w ((f.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩).sub
        (wR_mut W SP D n)) o.sl, wr.trans o.wr⟩,
      ⟨_, length_bytesAt _ _ _, c⟩, hA.of_eq rd wr, hD.of_eq rd wr⟩

theorem mac_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : Mid K W SP R N A D nl al n tl s) : WP isa (mac v.callee v.suffix y) s (Mid K W SP R N A D nl al n tl) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD⟩ := h
  refine WP.mono (mac_ok v L o.env o.sl hR hl h7 h13 ht4 ht16 hte hn' c hy hA hD) fun s' M => ?_
  refine ⟨o.macR L hD.w (by omega) M.env M.frame M.wr, ⟨nonce, hl, ?_⟩, hA.of_eq M.rd M.wr, hD.of_eq M.rd M.wr⟩
  rw [bytesAt_frame M.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide), c]

theorem tag_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : Mid K W SP R N A D nl al n tl s) : WP isa (tag v.callee y) s (Mid K W SP R N A D nl al n tl) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD⟩ := h
  refine WP.mono (tag_ok v L o.env hR o.sl.rounds (by omega) (by omega) c hy) fun s' ⟨E, _, rd, wr, f, _⟩ => ?_
  refine ⟨⟨E, slots_mut L hD.w (f.sub fun r hr => ?_) o.sl, wr.trans o.wr⟩, ⟨nonce, hl, ?_⟩, hA.of_eq rd wr,
    hD.of_eq rd wr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨wA W, by simp, Offset.sub_base W (by omega)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rcases hy with rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c]

/-- The context of counter mode, from a run between the pieces. -/
theorem Mid.ctx {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : Mid K W SP R N A D nl al n tl s) :
    ∃ nonce, CtrCtx K W SP s R nonce D n := by
  obtain ⟨o, ⟨nonce, hl, c⟩, -, hD⟩ := h
  exact ⟨nonce, L, hR, o.sl.rounds, by omega, by omega, by rw [hl]; exact hn', c, hD,
    by rw [o.wr]; exact covers_of_mem List.mem_cons_self, hdk⟩

theorem ctr_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : Mid K W SP R N A D nl al n tl s) :
    WP isa (ctr v.callee) s (Mid K W SP R N A D nl al n tl) := by
  obtain ⟨nonce, C⟩ := h.ctx L hR h7 h13 hn' hdk
  obtain ⟨o, ⟨nonce', hl, c⟩, hA, hD⟩ := h
  refine WP.mono (ctr_ok v C o.env o.sl) fun s' ⟨E, rd, wr, f, _⟩ => ?_
  refine ⟨⟨E, slots_mut L hD.w (f.sub (ctrR_mut W SP D n)) o.sl, wr.trans o.wr⟩, ⟨nonce', hl, ?_⟩,
    hA.of_eq rd wr, hD.of_eq rd wr⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (hD.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c]

/-- A run after the entry: the public arguments and its buffers. -/
def Pre₀ (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (s : State) : Prop :=
  One K W SP R N A D nl al n tl s ∧ Buf K W SP s N nl ∧ Buf K W SP s A al ∧ Buf K W SP s D n

theorem ctrs_check : ∃ hc, (taint.check (ccmT []) ctrs hc).isSome = true := ⟨_, by taint_decide⟩

theorem restore_check : ∃ hc, (taint.check (ccmT []) (.block restore) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `seal` after its entry, in two runs. -/
theorem sealBody_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64)
    (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Pre₀ K W SP R N A D nl al n tl s₁ ∧ Pre₀ K W SP R N A D nl al n tl s₂) :
    RelCT isa P (.seq ctrs (.seq (mac v.callee v.suffix 0) (.seq (tag v.callee 0)
      (.seq (ctr v.callee) (.block restore))))) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) ctrs_check).wp
    (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl) fun s₁ s₂ h => by
      obtain ⟨⟨o₁, n₁, a₁, d₁⟩, ⟨o₂, n₂, a₂, d₂⟩⟩ := hP _ _ h
      exact ⟨ctrs_mid L o₁ n₁ a₁ d₁ h7 h13, ctrs_mid L o₂ n₂ a₂ d₂ h7 h13⟩
  have r₂ := (mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂)
    fun _ _ h => ⟨h.2.1, h.2.2⟩).wp (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl)
    fun _ _ h => ⟨mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.1,
      mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.2⟩
  have r₃ := (tag_rel v L hR hDW hn h7 h13 (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl)
    fun _ _ h => ⟨tag_mid v L hR h7 h13 (.inl rfl) h.2.1, tag_mid v L hR h7 h13 (.inl rfl) h.2.2⟩
  have r₄ := (rel_of_pt (c := ctr v.callee)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact crypt_rel v C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl)
    fun _ _ h => ⟨ctr_mid v L hR h7 h13 hn' hdk h.2.1, ctr_mid v L hR h7 h13 hn' hdk h.2.2⟩
  have r₅ := rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.2.1.1 h.2.2.1 fun _ h => nomatch h) restore_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ r₅)))

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 24))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by crun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 24))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hE₁ : WP isa (.block entry) s₀ F₁) (hE₂ : WP isa (.block entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨loadW_ok hr₁, loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 24))]) (l₂ := entry.tail) (RelCT.seq l
      (rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

theorem entry_pre {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hwr : s.wr = [⟨D, n⟩, ⟨W, 2560⟩]) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (.block entry) s (Pre₀ K W SP R N A D nl al n tl) := by
  obtain ⟨s₁, run₁, E₁, S₁, _, _, rd₁, wr₁⟩ :=
    entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  exact WP.of_runBlock ⟨s₁, run₁, ⟨E₁, S₁, wr₁.trans hwr⟩, Ar.nonce.of_eq rd₁ wr₁, Ar.aad.of_eq rd₁ wr₁,
    Ar.data.of_eq rd₁ wr₁⟩

theorem entry_pre_self {s : State} (hp : onePre s) :
    WP isa (.block entry) s (Pre₀ (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .r8)
      (arg s 0) (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat) :=
  entry_pre (args_of hp) hp.2.1 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

/-- The second run, with the first's public arguments. -/
theorem entry_pre_pub {s₀ s₀' : State} (hp' : onePre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (Pre₀ (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .r8) (arg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), qa 3 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_pre_self hp'

theorem argW_in {s : State} (hp : onePre s) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  have h := in_off (d := 16) (n := 8) (args_of hp).args (by decide) (by decide)
  rw [add_ofNat_assoc] at h
  exact h

theorem pub_regs {s₀ s₀' : State} (hq : onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-- `vg_aes_ccm_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : Ctr32Impl) {s₀ s₀' : State} (hp : onePre s₀) (hp' : onePre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callee v.suffix) fun _ _ => True := by
  have Ar := args_of hp
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in hp) (argW_in hp')
    (entry_pre_self hp) (entry_pre_pub hp' hq)) ?_
  exact sealBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.aad.lt Ar.hn Ar.dk fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesCcm.X86_64
