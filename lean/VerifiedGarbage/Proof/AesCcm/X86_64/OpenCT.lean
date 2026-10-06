import VerifiedGarbage.Proof.AesCcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Open

/-!
# AES-CCM on x86-64: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`SealCT.lean`),
with counter mode before the MAC; the comparison, which leaves `ok` at
`W + 224`, and the mask and the exit are checked by the taint analysis from
the public arguments, between which correctness says each run keeps them
(`openCmp_ok`), and the received tag is read from the same address `tag`,
which correctness says is still on the stack (`loadTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

theorem openLoad_check : ∃ hc, (taint.check (ccmT [])
    (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem openCmp_check : ∃ hc, (taint.check (ccmT [.rbx, .rsi])
    (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax]))) hc).isSome = true := ⟨_, by taint_decide⟩

theorem openMask_check : ∃ hc, (taint.check (ccmT [])
    (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A run with the received tag `T`, of `tl` bytes, which it may read, apart
from `W`. -/
def TagR (W : Addr) (T : Addr) (tl : Nat) (s : State) : Prop :=
  Covers [⟨T, tl⟩] (s.rd ++ s.wr) ∧ (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩

/-- The tag length and the address of the received tag loaded, in a run. -/
theorem openLoad_one {K W SP : Addr} {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {s : State}
    (h : Mid K W SP R N A D nl al n tl T s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) s fun s' =>
      One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T ∧ s'.rd = s.rd := by
  obtain ⟨o, -, -, -, hT⟩ := h
  obtain ⟨s₁, run₁, hm₁, hbx₁, hsi₁, hg₁, hrd₁, hwr₁⟩ := loadTag_ok o.env o.sl hT.val hT.rd
  refine WP.of_runBlock ⟨s₁, run₁, ⟨o.env.keep (fun r hr => hg₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    hrd₁ hwr₁, by rw [hm₁]; exact o.sl, hwr₁.trans o.wr⟩, hbx₁, hsi₁, hrd₁⟩

/-- The comparison keeps the public arguments. -/
theorem openCmp_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) {s : State} (h : Mid K W SP R N A D nl al n tl T s) (hT : TagR W T tl s) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv
      (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax])))) s (One K W SP R N A D nl al n tl) := by
  obtain ⟨o, -, -, hD, hA⟩ := h
  refine WP.mono (openCmp_ok L o.env o.sl (by omega) ht16 hA.val hA.rd hT.1 hT.2) fun s₄ ⟨E₄, _, wr₄, f₄, _⟩ => ?_
  refine ⟨E₄, slots_mut L hD.w (f₄.sub fun r hr => ?_) o.sl, wr₄.trans o.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩

/-- `open` after its entry, up to the comparison, in one run. -/
theorem openFront_mid (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {s : State} (h : Pre₀ K W SP R N A D nl al n tl T s) :
    WP isa (openFront v.callee v.ctr.callee) s fun s' => Mid K W SP R N A D nl al n tl T s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨o, hN, hA, hD, hT⟩ := h
  obtain ⟨t, s', e, q⟩ := WP.seq (WP.mono (ctrs_mid L o hN hA hD hT h7 h13) fun _ h₁ =>
    WP.seq (WP.mono (ctr_mid v.ctr L hR h7 h13 hn' hdk h₁) fun _ h₂ =>
    WP.seq (WP.mono (mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inr rfl) h₂) fun _ h₃ =>
    tag_mid v.ctr L hR h7 h13 (.inr rfl) h₃)))
  exact ⟨t, s', e, q, Exec.rdwr e⟩

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 64) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → (Pre₀ K W SP R N A D nl al n tl T s₁ ∧ TagR W T tl s₁) ∧
      (Pre₀ K W SP R N A D nl al n tl T s₂ ∧ TagR W T tl s₂)) :
    RelCT isa P (.seq (openFront v.callee v.ctr.callee)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 okO) .rax]) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))) fun _ _ => True := by
  have hy : uO = 0 ∨ uO = 96 := .inr rfl
  have r₁ := (rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨⟨o₁, -⟩, -⟩, ⟨⟨o₂, -⟩, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) ctrs_check).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T) fun s₁ s₂ h => by
      obtain ⟨⟨⟨o₁, n₁, a₁, d₁, t₁⟩, -⟩, ⟨⟨o₂, n₂, a₂, d₂, t₂⟩, -⟩⟩ := hP _ _ h
      exact ⟨ctrs_mid L o₁ n₁ a₁ d₁ t₁ h7 h13, ctrs_mid L o₂ n₂ a₂ d₂ t₂ h7 h13⟩
  have r₂ := (rel_of_pt (c := ctr v.ctr.callee)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact crypt_rel v.ctr C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨ctr_mid v.ctr L hR h7 h13 hn' hdk h.2.1, ctr_mid v.ctr L hR h7 h13 hn' hdk h.2.2⟩
  have r₃ := (mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' hy
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1⟩,
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.1, mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.2⟩
  have r₄ := (tag_rel v.ctr L hR hDW hn h7 h13 hy
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨tag_mid v.ctr L hR h7 h13 hy h.2.1, tag_mid v.ctr L hR h7 h13 hy h.2.2⟩
  -- The pieces before the comparison keep the permissions, so the received tag stays readable.
  have front := (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))).wp
    (F₁ := TagR W T tl) (F₂ := TagR W T tl) fun s₁ s₂ h => by
      obtain ⟨⟨p₁, tr₁⟩, ⟨p₂, tr₂⟩⟩ := hP _ _ h
      exact ⟨WP.mono (openFront_mid v L hR h7 h13 ht4 ht16 hte hn' hdk p₁) fun _ ⟨_, rd', wr'⟩ =>
          ⟨by rw [rd', wr']; exact tr₁.1, tr₁.2⟩,
        WP.mono (openFront_mid v L hR h7 h13 ht4 ht16 hte hn' hdk p₂) fun _ ⟨_, rd', wr'⟩ =>
          ⟨by rw [rd', wr']; exact tr₂.1, tr₂.2⟩⟩
  have r₅a := (rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => (True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂) ∧
      TagR W T tl s₁ ∧ TagR W T tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.1.2.1.1 h.1.2.2.1 fun _ h => nomatch h) openLoad_check).wp
    (F₁ := fun (s' : State) => One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T)
    (F₂ := fun (s' : State) => One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T)
    fun _ _ h => ⟨WP.mono (openLoad_one h.1.2.1) fun _ q => ⟨q.1, q.2.1, q.2.2.1⟩,
      WP.mono (openLoad_one h.1.2.2) fun _ q => ⟨q.1, q.2.1, q.2.2.1⟩⟩
  have r₅b := rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax])))
    (P := fun s₁ s₂ => True ∧
      (One K W SP R N A D nl al n tl s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 tl ∧ s₁.gpr .rsi = T) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 tl ∧ s₂.gpr .rsi = T)) [.rbx, .rsi] hDW hn
    (fun _ _ h => Both.of h.2.1.1 h.2.2.1 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]) openCmp_check
  have r₅ := (RelCT.seq r₅a r₅b).wp
    (F₁ := One K W SP R N A D nl al n tl) (F₂ := One K W SP R N A D nl al n tl)
    fun _ _ h => ⟨openCmp_one L ht4 ht16 h.1.2.1 h.2.1, openCmp_one L ht4 ht16 h.1.2.2 h.2.2⟩
  have r₆ := rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.2.1 h.2.2 fun _ h => nomatch h) openMask_check
  exact RelCT.seq front (rel_assoc4 (RelCT.seq r₅ r₆))

/-- What the entry of `open` leaves: a run after the entry, with the received
tag readable. -/
theorem entry_open {s : State} (hp : openX86_64.pre s) :
    WP isa (.block entry) s fun s₁ =>
      Pre₀ (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .r8) (arg s 0)
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) s₁ ∧
      TagR (arg s 4) (arg s 2) (arg s 3).toNat s₁ := by
  have A := args_of_open hp
  refine WP.mono (entry_post A.1.1 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm) fun _ ⟨E, S, rd, wr, hT⟩ =>
    ⟨⟨⟨E, S, by rw [wr]; exact hp.2.1⟩, A.1.1.nonce.of_eq rd wr, A.1.1.aad.of_eq rd wr, A.1.1.data.of_eq rd wr, hT⟩,
      by rw [rd, wr]; exact A.2, A.1.2.w⟩

/-- The second run, with the first's public arguments. -/
theorem entry_open_pub {s₀ s₀' : State} (hp' : openX86_64.pre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' fun s₁ =>
      Pre₀ (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat (arg s₀ 2) s₁ ∧
      TagR (arg s₀ 4) (arg s₀ 2) (arg s₀ 3).toNat s₁ := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), qa 3 (by decide), qa 4 (by decide), q1, q2, q3, q4,
    q5, q6, q7]
  exact entry_open hp'

/-- `vg_aes_ccm_open`, in two runs with the same public arguments. -/
theorem open_rel (v : UpdateImpl) {s₀ s₀' : State} (hp : openX86_64.pre s₀) (hp' : openX86_64.pre s₀')
    (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee v.ctr.callee) fun _ _ => True := by
  have A := args_of_open hp
  have Ar := A.1.1
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 4 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_open hp').1.1 rfl) (entry_open hp) (entry_open_pub hp' hq)) ?_
  exact openBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.aad.lt Ar.hn Ar.dk fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesCcm.X86_64
