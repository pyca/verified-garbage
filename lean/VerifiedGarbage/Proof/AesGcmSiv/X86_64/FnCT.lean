import VerifiedGarbage.Proof.AesGcmSiv.X86_64.PolyvalCT
import VerifiedGarbage.Proof.Framework.X86_64.Narrow

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are constant time

Untrusted: everything here is checked by Lean. The entry, which loads `W`
from the stack first, passes the taint analysis from the public arguments
(`entry_rel`); between the pieces each run has the public arguments, its
buffers and the tag's address on the stack (`St`), which every piece keeps
(by correctness), and the pieces are related from it (`keys_rel`,
`polyval_rel`, `tag_rel`, `crypt_rel`, and the taint analysis for the
comparison, the mask and the restore). The copies of the tag load its
address from the stack first, the same in both runs, and the taint analysis
checks the rest (`rel_loadT`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its pieces before the copy
of the tag do not, and run the same from its states with `tag` only readable
(`rel_narrow`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl in_off)

/-- The address of the tag `T`, at `SP + 16`, where the run may read it,
apart from what the pieces write, and the tag, which it may read. -/
structure ArgT (W SP D : Addr) (n : Nat) (T : Addr) (s : State) : Prop where
  val : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T
  rd : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8
  w : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩
  d : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩
  tb : TagBuf W SP D n T
  trd : Covers [⟨T, 16⟩] (s.rd ++ s.wr)

theorem ArgT.mut {W SP D T : Addr} {n : Nat} {s s' : State} (h : ArgT W SP D n T s)
    (hf : Frame (mutR W SP D n) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgT W SP D n T s' :=
  ⟨by rw [argT_kept (hf.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩) h.w h.d, h.val],
    by rw [hrd, hwr]; exact h.rd, h.w, h.d, h.tb, by rw [hrd, hwr]; exact h.trd⟩

/-- A run between the pieces: the public arguments, the buffers and the
tag's address. -/
structure St (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop where
  bufs : Bufs K W SP R N A D al n t
  nonce : Buf K W SP t N 12
  argT : ArgT W SP D n T t

theorem St.frame {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t t' : State}
    (h : St K W SP R N A D al n T t) (E : Env K W SP t') {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) (hm : Frame (mutR W SP D n) t.mem t'.mem)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    St K W SP R N A D al n T t' :=
  ⟨⟨⟨E, h.bufs.one.sl.of_frame hf hd, hwr.trans h.bufs.one.wr⟩, h.bufs.aad.of_eq hrd hwr, h.bufs.data.of_eq hrd hwr⟩,
    h.nonce.of_eq hrd hwr, h.argT.mut hm hrd hwr⟩

/-- `St`, and the keys' results that POLYVAL needs. -/
def StK (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  St K W SP R N A D al n T t ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) : WP isa (keys v.callees) t (StK K W SP R N A D al n T) :=
  WP.mono (keys_ok v L hR h.bufs.one.env h.bufs.one.sl h.nonce h.bufs.data.w) fun _ Ky =>
    ⟨h.frame Ky.env Ky.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Ky.frame.sub (keyR_mutW W SP)).sub (mutW_mut W SP D n)) Ky.rd Ky.wr,
      Ky.hkey, Ky.acc⟩

theorem polyval_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : StK K W SP R N A D al n T t) : WP isa (polyval v.callees) t (St K W SP R N A D al n T) :=
  WP.mono (polyval_ok v L h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.aad h.1.bufs.data h.1.nonce h.2.1 h.2.2)
    fun _ Po => h.1.frame Po.env Po.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n)) Po.rd Po.wr

theorem tag_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {o : Nat} (ho : o = 0 ∨ o = 128) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (tag v.callees o) t (St K W SP R N A D al n T) :=
  WP.mono (tag_ok v L hR h.bufs.one.env h.bufs.one.sl ho) fun _ Tg => h.frame Tg.env Tg.frame (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by omega)) (by decide) (by omega)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) ((Tg.frame.sub (tagR_mutW W SP (by omega))).sub (mutW_mut W SP D n))
    Tg.rd Tg.wr

theorem crypt_st0 (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) : WP isa (crypt v.callees) t (St K W SP R N A D al n T) :=
  WP.mono (crypt_ok v L hR h.bufs.one.env h.bufs.one.sl h.bufs.data
    (by rw [h.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp))) fun _ Cr =>
    h.frame Cr.env Cr.frame (slots_cryR L h.bufs.data) (Cr.frame.sub (cryR_mut W SP D n)) Cr.rd Cr.wr

theorem crypt_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : StK K W SP R N A D al n T t) : WP isa (crypt v.callees) t (StK K W SP R N A D al n T) := by
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
  refine ⟨h.1.frame Cr.env Cr.frame (slots_cryR L h.1.bufs.data) (Cr.frame.sub (cryR_mut W SP D n)) Cr.rd Cr.wr,
    ?_, ?_⟩
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.1,
      Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)]
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.2]

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 24))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by srun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 24))]) hc).isSome =
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

/-- What the entry leaves, for the arguments: the environment, the slots, the
same permissions, and the address of the tag still at `SP + 16`. -/
theorem entry_post {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s fun s₁ => Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
      InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8 := by
  obtain ⟨s₁, run₁, E₁, S₁, _, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  have hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    exact h
  refine WP.of_runBlock ⟨s₁, run₁, E₁, S₁, rd₁, wr₁, ?_, by rw [rd₁, wr₁]; exact hTr⟩
  rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact argT_disj (n := n) Ar.argsW Ar.argsD _ List.mem_cons_self) (by decide), hT]

theorem argW_in {s : State} {K W SP N A D : Addr} {R al n : Nat} (Ar : Args s K W SP N A D R al n)
    (hsp : s.gpr .rsp = SP) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
  rw [add_ofNat_assoc] at h
  rw [hsp]; exact h

theorem pub_regs {s₀ s₀' : State} (hq : onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-! ## The tag's address -/

/-- What the copies of the tag need of a run: `r15` and `rsp` hold `W` and
`SP`, and the address of the tag `T` is at `SP + 16`, where the run may read
it. -/
def TagIn (W SP T : Addr) (s : State) : Prop :=
  s.gpr .r15 = W ∧ s.gpr .rsp = SP ∧ s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8

theorem St.tagIn {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {σ s : State}
    (h : St K W SP R N A D al n T σ) (hg : σ.gpr = s.gpr) (hm : σ.mem = s.mem)
    (hc : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) : TagIn W SP T s :=
  ⟨by rw [← hg]; exact h.bufs.one.env.r15, by rw [← hg]; exact h.bufs.one.env.rsp, by rw [← hm]; exact h.argT.val,
    hc _ _ h.argT.rd⟩

/-- `mov rcx, [rsp + 16]`: the tag's address in `rcx`. -/
theorem loadT_ok {W SP T : Addr} {s : State} (h : TagIn W SP T s) :
    WP isa (.block [.mov .rcx (.mem (at_ .rsp 16))]) s fun s' =>
      s'.gpr .rcx = T ∧ s'.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s'.gpr r = s.gpr r := by
  obtain ⟨h15, hsp, hT, hr⟩ := h
  refine WP.of_runBlock ⟨_, by srun [hsp, hr], ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, hT]
  · simp only [gpr_setReg, ite_false, reduceCtorEq, h15]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem loadT_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (at_ .rsp 16))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- `mov rcx, [rsp + 16]` and then `c`, which the taint analysis checks with
`rcx` and `r15` public, in two runs with the same `W`, `SP` and tag
address. -/
theorem rel_loadT {W SP T : Addr} {P : State → State → Prop} {l : List Instr}
    (hP : ∀ s₁ s₂, P s₁ s₂ → TagIn W SP T s₁ ∧ TagIn W SP T s₂)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block l) hc).isSome = true) :
    RelCT isa P (.block (([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ l)) fun _ _ => True := by
  have a := (rel_taintR (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      obtain ⟨⟨-, a₁, -⟩, ⟨-, a₂, -⟩⟩ := hP _ _ h
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) loadT_check).wp
    (F₁ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    (F₂ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    fun _ _ h => ⟨WP.mono (loadT_ok (hP _ _ h).1) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩,
      WP.mono (loadT_ok (hP _ _ h).2) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩⟩
  exact RelCT.block_append (M := isa) (RelCT.seq a (rel_taintR [.rcx, .r15] (fun _ _ h r hr => by
    obtain ⟨-, ⟨c₁, w₁, -⟩, ⟨c₂, w₂, -⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [c₁, c₂]
    · rw [w₁, w₂]) hc))

/-! ## `seal` -/

/-- `s` with the tag read only, and the data and `W` its writable regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, 16⟩]) [⟨D, n⟩, ⟨W, 3816⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- What the entry of `seal` leaves: with the tag read only, a run after the
entry. -/
def SealIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (s : State) : Prop :=
  s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩] ∧ St K W SP R N A D al n T (narrowT D n T W s)

theorem sealIn_of {s s₁ : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hwr : s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩])
    (h : Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧ InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8) :
    SealIn K W SP R N A D al n T s₁ := by
  obtain ⟨E, S, rd, wr, hT, hTr⟩ := h
  have hwr₁ : s₁.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩] := by rw [wr]; exact hwr
  have hc : Covers (s₁.rd ++ s₁.wr) ((narrowT D n T W s₁).rd ++ (narrowT D n T W s₁).wr) := by
    rw [hwr₁]; exact covers_narrowT _ _ _ _
  have hb : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → Buf K W SP (narrowT D n T W s₁) P len := fun hP =>
    { hP.of_eq rd wr with rd := (hP.of_eq rd wr).rd.trans hc }
  exact ⟨hwr₁, ⟨⟨⟨E.r13, E.r15, E.rsp, E.perm.k.trans hc, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩, S, rfl⟩, hb Ar.aad, hb Ar.data⟩, hb Ar.nonce,
    ⟨hT, hc _ _ hTr, Ar.argsW, Ar.argsD, Tb, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩⟩

theorem entry_seal {s : State} (hp : sealPre s) :
    WP isa (.block entry) s (SealIn (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (arg s 0).toNat (arg s 1)) :=
  WP.mono (entry_post (args_of_seal hp).1.1 rfl (ofNat_toNat64 _).symm rfl rfl rfl
      (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl)
    fun _ h => sealIn_of (args_of_seal hp).1.1 (args_of_seal hp).1.2 hp.2.1 h

/-- The second run, with the first's public arguments. -/
theorem entry_seal_pub {s₀ s₀' : State} (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_seal hp'

/-- `seal` after its entry, up to the copy of the tag. -/
abbrev sealFront (v : GcmImpl) : Prog isa :=
  .seq (.seq (.seq (keys v.callees) (polyval v.callees)) (tag v.callees tagO)) (crypt v.callees)

theorem sealFront_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (sealFront v) t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (keys_st v L hR h) fun _ h => polyval_st v L h))
    fun _ h => tag_st v L hR (by decide) h)) fun _ h => crypt_st0 v L hR h)

/-- `sealFront`, in two runs. -/
theorem sealFront_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64)
    (hn' : n < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (sealFront v) fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ := by
  have r₁ := (keys_rel v L hR hDW hn fun t₁ t₂ h => ⟨⟨(hP _ _ h).1.bufs.one, (hP _ _ h).1.nonce⟩,
      ⟨(hP _ _ h).2.bufs.one, (hP _ _ h).2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨keys_st v L hR (hP _ _ h).1, keys_st v L hR (hP _ _ h).2⟩
  have r₂ := (polyval_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨polyval_st v L h.2.1, polyval_st v L h.2.2⟩
  have r₃ := (tag_rel v L hR hDW hn (o := tagO) (by decide) (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨tag_st v L hR (by decide) h.2.1, tag_st v L hR (by decide) h.2.2⟩
  have r₄ := (crypt_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.bufs.data⟩, ⟨h.2.2.bufs.one, h.2.2.bufs.data⟩⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨crypt_st0 v L hR h.2.1, crypt_st0 v L hR h.2.2⟩
  exact (RelCT.seq (RelCT.seq (RelCT.seq r₁ r₂) r₃) r₄).mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩

theorem tagOut_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block (tagOut.tail ++ restore)) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- `vg_aes_gcm_siv_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : GcmImpl) {s₀ s₀' : State} (hp : sealPre s₀) (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees) fun _ _ => True := by
  have Ar := (args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_seal hp').1.1 rfl) (entry_seal hp) (entry_seal_pub hp' hq)) ?_
  refine RelCT.assoc (RelCT.assoc (RelCT.assoc ?_))
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := sealFront v)
    (P := fun s₁ s₂ => True ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₁ ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₂)
    [⟨arg s₀ 1, 16⟩] [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩]
    (sealFront_rel v L Ar.rounds Ar.data.w hn Ar.aad.lt Ar.data.lt
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 1, 16⟩, ⟨arg s₀ 2, 3816⟩] →
          Covers ([⟨arg s₀ 1, 16⟩] ++ [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩]) s.wr ∧
          Covers [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := sealFront_st v L Ar.rounds p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := sealFront_st v L Ar.rounds p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (rel_loadT (l := tagOut.tail ++ restore) (fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.tagIn g₁ h₁ c₁, m₂.tagIn g₂ h₂ c₂⟩) tagOut_check)

/-! ## `open` -/

theorem entry_st {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hwr : s.wr = [⟨D, n⟩, ⟨W, 3816⟩]) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s (St K W SP R N A D al n T) :=
  WP.mono (entry_post Ar hsp hn hT hW hdi hsi hdx hcx hr8 hr9) fun _ ⟨E₁, S₁, rd₁, wr₁, hT₁, hTa₁⟩ =>
    ⟨⟨⟨E₁, S₁, wr₁.trans hwr⟩, Ar.aad.of_eq rd₁ wr₁, Ar.data.of_eq rd₁ wr₁⟩, Ar.nonce.of_eq rd₁ wr₁,
      ⟨hT₁, hTa₁, Ar.argsW, Ar.argsD, Tb, by rw [rd₁, wr₁]; exact hTr⟩⟩

theorem entry_open {s : State} (hp : openPre s) :
    WP isa (.block entry) s (St (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (arg s 0).toNat (arg s 1)) :=
  entry_st (args_of_open hp).1.1 (args_of_open hp).1.2 (args_of_open hp).2 hp.2.1 rfl (ofNat_toNat64 _).symm rfl rfl
    rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl

/-- The second run, with the first's public arguments. -/
theorem entry_open_pub {s₀ s₀' : State} (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (St (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_open hp'

theorem recv_st {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (.block recv) t (St K W SP R N A D al n T) := by
  obtain ⟨t', run', fR, -, hg', hrd', hwr'⟩ := recv_ok h.bufs.one.env h.argT.val h.argT.rd
    (h.argT.tb.buf h.argT.trd)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fR (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using L.w_w (a := 200) (n := 48) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide))
    (fR.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, by simp, Region.sub_prefix (by decide)⟩)
    hrd' hwr'⟩

theorem recv_split : recv = ([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ recv.tail := rfl

theorem recv_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block recv.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ hc, (taint.check (sivT []) (.block Impl.AesGcmSiv.X86_64.cmp) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ hc, (taint.check (sivT []) mask hc).isSome = true := ⟨_, by taint_decide⟩

theorem fin_check : ∃ hc, (taint.check (sivT [])
    (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `St`, with `ok` at `W + 192` either 1 or 0. -/
def StO (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  St K W SP R N A D al n T t ∧
    (t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 ∨ t.mem.readW (W + BitVec.ofNat 64 192) 64 = 0#64)

theorem cmp_st {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (.block Impl.AesGcmSiv.X86_64.cmp) t (StO K W SP R N A D al n T) := by
  obtain ⟨t', run', hm', hg', hrd', hwr'⟩ := cmp_ok h.bufs.one.env
  have fO : Frame [wO W] t.mem t'.mem := by
    rw [hm']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩) hrd' hwr', ?_⟩
  rw [hm', Mem.readW_writeW_self64]
  split
  · exact .inl rfl
  · exact .inr rfl

theorem mask_st {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : StO K W SP R N A D al n T t) : WP isa mask t (St K W SP R N A D al n T) := by
  have hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 then 1#64 else 0#64 := by
    rcases h.2 with h' | h' <;> rw [h'] <;> decide
  refine WP.mono (mask_ok h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)) hok) fun _ Mk =>
    h.1.frame Mk.env Mk.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact (h.1.bufs.data.w.sub_right (Lay.wSub (by decide))).symm)
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
      Mk.rd Mk.wr

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (.seq (.block recv) (.seq (keys v.callees) (.seq (crypt v.callees) (.seq (polyval v.callees)
      (.seq (tag v.callees bO) (.seq (.block Impl.AesGcmSiv.X86_64.cmp) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))))
      fun _ _ => True := by
  have r₀ := (rel_loadT (l := recv.tail) (fun t₁ t₂ h =>
      ⟨(hP _ _ h).1.tagIn rfl rfl (Covers.refl _), (hP _ _ h).2.tagIn rfl rfl (Covers.refl _)⟩) recv_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨by rw [← recv_split]; exact recv_st L (hP _ _ h).1, by rw [← recv_split]; exact recv_st L (hP _ _ h).2⟩
  have r₁ := (keys_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.nonce⟩, ⟨h.2.2.bufs.one, h.2.2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨keys_st v L hR h.2.1, keys_st v L hR h.2.2⟩
  have r₂ := (crypt_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) fun t₁ t₂ h =>
      ⟨⟨h.2.1.1.bufs.one, h.2.1.1.bufs.data⟩, ⟨h.2.2.1.bufs.one, h.2.2.1.bufs.data⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨crypt_st v L hR h.2.1, crypt_st v L hR h.2.2⟩
  have r₃ := (polyval_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨polyval_st v L h.2.1, polyval_st v L h.2.2⟩
  have r₄ := (tag_rel v L hR hDW hn (o := bO) (by decide) (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨tag_st v L hR (by decide) h.2.1, tag_st v L hR (by decide) h.2.2⟩
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) cmp_check).wp
    (F₁ := StO K W SP R N A D al n T) (F₂ := StO K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨cmp_st L h.2.1, cmp_st L h.2.2⟩
  have r₆ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ StO K W SP R N A D al n T t₁ ∧ StO K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) mask_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨mask_st h.2.1, mask_st h.2.2⟩
  have r₇ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) fin_check
  rw [recv_split]
  exact RelCT.seq r₀ (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ r₇))))))

/-- `vg_aes_gcm_siv_open`, in two runs with the same public arguments. -/
theorem open_rel (v : GcmImpl) {s₀ s₀' : State} (hp : openPre s₀) (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees) fun _ _ => True := by
  have Ar := (args_of_open hp).1.1
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_open hp').1.1 rfl) (entry_open hp) (entry_open_pub hp' hq)) ?_
  exact openBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.aad.lt Ar.data.lt
    fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesGcmSiv.X86_64
