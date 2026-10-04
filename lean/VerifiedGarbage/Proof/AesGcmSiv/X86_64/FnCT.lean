import VerifiedGarbage.Proof.AesGcmSiv.X86_64.PolyvalCT

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are constant time

Untrusted: everything here is checked by Lean. The entry, which loads `W`
from the stack first, passes the taint analysis from the public arguments
(`entry_rel`); between the pieces each run has the public arguments and its
buffers (`St`), which every piece keeps (by correctness), and the pieces are
related from it (`keys_rel`, `polyval_rel`, `tag_rel`, `crypt_rel`, and the
taint analysis for the comparison, the mask and the restore).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl in_off)

/-- A run between the pieces: the public arguments and the buffers. -/
structure St (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop where
  bufs : Bufs K W SP R N A D al n t
  nonce : Buf K W SP t N 12

theorem St.frame {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t t' : State}
    (h : St K W SP R N A D al n t) (E : Env K W SP t') {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 272, 48⟩ : Region).Disjoint r) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    St K W SP R N A D al n t' :=
  ⟨⟨⟨E, h.bufs.one.sl.of_frame hf hd, hwr.trans h.bufs.one.wr⟩, h.bufs.aad.of_eq hrd hwr, h.bufs.data.of_eq hrd hwr⟩,
    h.nonce.of_eq hrd hwr⟩

/-- `St`, and the keys' results that POLYVAL needs. -/
def StK (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop :=
  St K W SP R N A D al n t ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} {t : State} (h : St K W SP R N A D al n t) : WP isa (keys v.callees) t (StK K W SP R N A D al n) :=
  WP.mono (keys_ok v L hR h.bufs.one.env h.bufs.one.sl h.nonce h.bufs.data.w) fun _ Ky =>
    ⟨h.frame Ky.env Ky.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) Ky.rd Ky.wr, Ky.hkey, Ky.acc⟩

theorem polyval_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : StK K W SP R N A D al n t) : WP isa (polyval v.callees) t (St K W SP R N A D al n) :=
  WP.mono (polyval_ok v L h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.aad h.1.bufs.data h.1.nonce h.2.1 h.2.2)
    fun _ Po => h.1.frame Po.env Po.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) Po.rd Po.wr

theorem tag_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} {o : Nat} (ho : o = 0 ∨ o = 128 ∨ o = 144) {t : State} (h : St K W SP R N A D al n t) :
    WP isa (tag v.callees o) t (St K W SP R N A D al n) :=
  WP.mono (tag_ok v L hR h.bufs.one.env h.bufs.one.sl ho) fun _ T => h.frame T.env T.frame (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by omega)) (by decide) (by omega)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) T.rd T.wr

theorem crypt_st0 (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} {t : State} (h : St K W SP R N A D al n t) : WP isa (crypt v.callees) t (St K W SP R N A D al n) :=
  WP.mono (crypt_ok v L hR h.bufs.one.env h.bufs.one.sl h.bufs.data
    (by rw [h.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp))) fun _ Cr =>
    h.frame Cr.env Cr.frame (slots_cryR L h.bufs.data) Cr.rd Cr.wr

theorem crypt_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} {t : State} (h : StK K W SP R N A D al n t) : WP isa (crypt v.callees) t (StK K W SP R N A D al n) := by
  refine WP.mono (crypt_ok v L hR h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp))) fun _ Cr => ?_
  have dK : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 96 → ∀ q ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
      · exact (h.1.bufs.data.w.sub_right (Lay.wSub (by omega))).symm
  refine ⟨h.1.frame Cr.env Cr.frame (slots_cryR L h.1.bufs.data) Cr.rd Cr.wr, ?_, ?_⟩
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.1,
      Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)]
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.2]

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 16))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by srun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 16))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 16) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 16) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 16) 8)
    (hE₁ : WP isa (.block entry) s₀ F₁) (hE₂ : WP isa (.block entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 16) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨loadW_ok hr₁, loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 16))]) (l₂ := entry.tail) (RelCT.seq l
      (rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 16) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

theorem entry_st {s : State} {K W SP N A D : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (hwr : s.wr = [⟨D, n⟩, ⟨W, 4096⟩]) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s (St K W SP R N A D al n) := by
  obtain ⟨s₁, run₁, E₁, S₁, _, _, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  exact WP.of_runBlock ⟨s₁, run₁, ⟨⟨E₁, S₁, wr₁.trans hwr⟩, Ar.aad.of_eq rd₁ wr₁, Ar.data.of_eq rd₁ wr₁⟩,
    Ar.nonce.of_eq rd₁ wr₁⟩

theorem entry_st_self {s : State} (hp : onePre s) :
    WP isa (.block entry) s (St (s.gpr .rdi) (arg s 1) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (arg s 0).toNat) :=
  entry_st (args_of hp) hp.2.1 rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

/-- The second run, with the first's public arguments. -/
theorem entry_st_pub {s₀ s₀' : State} (hp' : onePre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (St (s₀.gpr .rdi) (arg s₀ 1) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (arg s₀ 0).toNat) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_st_self hp'

theorem argW_in {s : State} (hp : onePre s) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 := by
  have h := in_off (d := 8) (n := 8) (args_of hp).args (by decide) (by decide)
  rw [add_ofNat_assoc] at h
  exact h

theorem pub_regs {s₀ s₀' : State} (hq : onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

theorem restore_check : ∃ hc, (taint.check (sivT []) (.block restore) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `seal` after its entry, in two runs. -/
theorem sealBody_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop} (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n t₁ ∧ St K W SP R N A D al n t₂) :
    RelCT isa P (.seq (keys v.callees) (.seq (polyval v.callees) (.seq (tag v.callees tagO)
      (.seq (crypt v.callees) (.block restore))))) fun _ _ => True := by
  have r₁ := (keys_rel v L hR hDW hn fun t₁ t₂ h => ⟨⟨(hP _ _ h).1.bufs.one, (hP _ _ h).1.nonce⟩,
      ⟨(hP _ _ h).2.bufs.one, (hP _ _ h).2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n) (F₂ := StK K W SP R N A D al n)
    fun t₁ t₂ h => ⟨keys_st v L hR (hP _ _ h).1, keys_st v L hR (hP _ _ h).2⟩
  have r₂ := (polyval_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n t₁ ∧
      StK K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := St K W SP R N A D al n) (F₂ := St K W SP R N A D al n)
    fun t₁ t₂ h => ⟨polyval_st v L h.2.1, polyval_st v L h.2.2⟩
  have r₃ := (tag_rel v L hR hDW hn (o := tagO) (by decide) (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n t₁ ∧
      St K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := St K W SP R N A D al n) (F₂ := St K W SP R N A D al n)
    fun t₁ t₂ h => ⟨tag_st v L hR (by decide) h.2.1, tag_st v L hR (by decide) h.2.2⟩
  have r₄ := (crypt_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n t₁ ∧
      St K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.bufs.data⟩, ⟨h.2.2.bufs.one, h.2.2.bufs.data⟩⟩).wp
    (F₁ := St K W SP R N A D al n) (F₂ := St K W SP R N A D al n)
    fun t₁ t₂ h => ⟨crypt_st0 v L hR h.2.1, crypt_st0 v L hR h.2.2⟩
  have r₅ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n t₁ ∧ St K W SP R N A D al n t₂) hDW hn
    (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) restore_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ r₅)))

/-- `vg_aes_gcm_siv_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : GcmImpl) {s₀ s₀' : State} (hp : onePre s₀) (hp' : onePre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees) fun _ _ => True := by
  have Ar := args_of hp
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 1 (by decide)) (argW_in hp) (argW_in hp')
    (entry_st_self hp) (entry_st_pub hp' hq)) ?_
  exact sealBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.aad.lt Ar.data.lt
    fun _ _ h => ⟨h.2.1, h.2.2⟩

/-! ## `open` -/

theorem cmp_check : ∃ hc, (taint.check (sivT []) (.block Impl.AesGcmSiv.X86_64.cmp) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ hc, (taint.check (sivT []) mask hc).isSome = true := ⟨_, by taint_decide⟩

theorem fin_check : ∃ hc, (taint.check (sivT [])
    (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `St`, with `ok` at `W + 208` either 1 or 0. -/
def StO (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop :=
  St K W SP R N A D al n t ∧
    (t.mem.readW (W + BitVec.ofNat 64 208) 64 = 1#64 ∨ t.mem.readW (W + BitVec.ofNat 64 208) 64 = 0#64)

theorem cmp_st {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n t) : WP isa (.block Impl.AesGcmSiv.X86_64.cmp) t (StO K W SP R N A D al n) := by
  obtain ⟨t', run', hm', hg', hrd', hwr'⟩ := cmp_ok h.bufs.one.env
  have fO : Frame [wO W] t.mem t'.mem := by
    rw [hm']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    hrd' hwr', ?_⟩
  rw [hm', Mem.readW_writeW_self64]
  split
  · exact .inl rfl
  · exact .inr rfl

theorem mask_st {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State} (h : StO K W SP R N A D al n t) :
    WP isa mask t (St K W SP R N A D al n) := by
  have hok : t.mem.readW (W + BitVec.ofNat 64 208) 64 =
      if t.mem.readW (W + BitVec.ofNat 64 208) 64 = 1#64 then 1#64 else 0#64 := by
    rcases h.2 with h' | h' <;> rw [h'] <;> decide
  refine WP.mono (mask_ok h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)) hok) fun _ Mk =>
    h.1.frame Mk.env Mk.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact (h.1.bufs.data.w.sub_right (Lay.wSub (by decide))).symm)
      Mk.rd Mk.wr

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop} (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n t₁ ∧ St K W SP R N A D al n t₂) :
    RelCT isa P (.seq (keys v.callees) (.seq (crypt v.callees) (.seq (polyval v.callees) (.seq (tag v.callees t2O)
      (.seq (.block Impl.AesGcmSiv.X86_64.cmp) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore))))))))
      fun _ _ => True := by
  have r₁ := (keys_rel v L hR hDW hn fun t₁ t₂ h => ⟨⟨(hP _ _ h).1.bufs.one, (hP _ _ h).1.nonce⟩,
      ⟨(hP _ _ h).2.bufs.one, (hP _ _ h).2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n) (F₂ := StK K W SP R N A D al n)
    fun t₁ t₂ h => ⟨keys_st v L hR (hP _ _ h).1, keys_st v L hR (hP _ _ h).2⟩
  have r₂ := (crypt_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n t₁ ∧
      StK K W SP R N A D al n t₂) fun t₁ t₂ h =>
      ⟨⟨h.2.1.1.bufs.one, h.2.1.1.bufs.data⟩, ⟨h.2.2.1.bufs.one, h.2.2.1.bufs.data⟩⟩).wp
    (F₁ := StK K W SP R N A D al n) (F₂ := StK K W SP R N A D al n)
    fun t₁ t₂ h => ⟨crypt_st v L hR h.2.1, crypt_st v L hR h.2.2⟩
  have r₃ := (polyval_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n t₁ ∧
      StK K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := St K W SP R N A D al n) (F₂ := St K W SP R N A D al n)
    fun t₁ t₂ h => ⟨polyval_st v L h.2.1, polyval_st v L h.2.2⟩
  have r₄ := (tag_rel v L hR hDW hn (o := t2O) (by decide) (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n t₁ ∧
      St K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := St K W SP R N A D al n) (F₂ := St K W SP R N A D al n)
    fun t₁ t₂ h => ⟨tag_st v L hR (by decide) h.2.1, tag_st v L hR (by decide) h.2.2⟩
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n t₁ ∧ St K W SP R N A D al n t₂) hDW hn
    (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) cmp_check).wp
    (F₁ := StO K W SP R N A D al n) (F₂ := StO K W SP R N A D al n)
    fun t₁ t₂ h => ⟨cmp_st L h.2.1, cmp_st L h.2.2⟩
  have r₆ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ StO K W SP R N A D al n t₁ ∧ StO K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) mask_check).wp
    (F₁ := St K W SP R N A D al n) (F₂ := St K W SP R N A D al n)
    fun t₁ t₂ h => ⟨mask_st h.2.1, mask_st h.2.2⟩
  have r₇ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n t₁ ∧ St K W SP R N A D al n t₂) hDW hn
    (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) fin_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ r₇)))))

/-- `vg_aes_gcm_siv_open`, in two runs with the same public arguments. -/
theorem open_rel (v : GcmImpl) {s₀ s₀' : State} (hp : onePre s₀) (hp' : onePre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees) fun _ _ => True := by
  have Ar := args_of hp
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 1 (by decide)) (argW_in hp) (argW_in hp')
    (entry_st_self hp) (entry_st_pub hp' hq)) ?_
  exact openBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.aad.lt Ar.data.lt
    fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesGcmSiv.X86_64
