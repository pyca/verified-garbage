import VerifiedGarbage.Proof.AesSiv.AArch64.Ctr
import VerifiedGarbage.Proof.AesSiv.AArch64.Finish
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-SIV on AArch64: CTR is constant time

Every block's pointer and length are public (`x22`, `x23`), so the code
around the call of `vg_aes_ctr32` passes the taint analysis, and the call's
arguments are the same in both runs (`ctr_rel` of `CmacAes.AArch64`). Both
runs leave the loop after the same block, the last one (`ctr_tail`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (CallPre ctr_call ctr_rel agree_of k0)
open VG.Proof.CmacAes.Stream.AArch64 (copyMem_frame eval_zero)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem cr_agree {s₀' a b : State} {i : Nat} (hq : s₀.sp = s₀'.sp) (ha : CR s₀ C D P W R L i a)
    (hb : CR s₀' C D P W R L i b) :
    taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) a b := by
  refine agree_of (by rw [ha.sp, hb.sp, hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [ha.x19, hb.x19]
  · rw [ha.x20, hb.x20]
  · rw [ha.x21, hb.x21]
  · rw [ha.x22, hb.x22]
  · rw [ha.x23, hb.x23]

theorem ctrPre_wp (h : Env s₀ C D P W R L) {i : Nat} {s : State} (hr : CR s₀ C D P W R L i s) :
    WP isa (.block ctrPre) s fun t => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀ C D P W R L i t := by
  have hwW := h.wW
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, g₁, m₁, sp₁, rd₁, wr₁⟩ :=
    ctrPre_ok h hr.x19 hr.x20 hr.x21 hr.rd hr.wr
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide), Proof.Cmac.zero2_bytes]
  have hr₁ := hr.keep (fun r hr _ => g₁ r hr) sp₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h.cargs hr₁.rd hr₁.wr x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ hz, hr₁⟩

/-- A block is constant time. -/
theorem body_rel (v : Proof.Aes.AArch64.Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L)
    (h' : Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (i : Nat) :
    RelCT isa (fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) (ctrBody v.callee)
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) (.block ctrPre)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.seq ctrMin (.seq xorBytes (.seq (.block ctrPost) ctrLeft))) hc).isSome = true := ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) _
    (fun a b hab => cr_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀ C D P W R L i t)
    (F₂ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀' C D P W R L i t)
    fun a b hab => ⟨ctrPre_wp h hab.1, ctrPre_wp h' hab.2⟩
  have r₂ := (ctr_rel v (P := fun (a b : State) => (CallPre a (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀ C D P W R L i a) ∧
      CallPre b (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ CR s₀' C D P W R L i b)
    fun a b hab => ⟨hab.1.1, hab.2.1, by rw [hab.1.2.sp, hab.2.2.sp, hq]⟩).wp
    (F₁ := CR s₀ C D P W R L i) (F₂ := CR s₀' C D P W R L i)
    fun a b hab => ⟨WP.mono (ctr_call v hab.1.1) fun _ p => hab.1.2.keep p.saved p.sp p.rd p.wr,
      WP.mono (ctr_call v hab.2.1) fun _ p => hab.2.2.keep p.saved p.sp p.rd p.wr⟩
  have r₃ := RelCT.taint (A := taint) (P := fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) _
    (fun a b hab => cr_agree hq hab.1 hab.2) hB
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq r₃)

/-- Block `i` of a run. -/
def CI (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  ∃ m₀ q x, CInv s₀ C D P W R L m₀ q x i s

/-- After the last block: the registers. -/
structure CE (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What a block leaves, for the loop: the last block, or the next one. -/
def BPost (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  (L - 16 * i ≤ 16 ∧ s.gpr .x23 = 0 ∧ CE s₀ C D P W R L s) ∨
    (16 < L - 16 * i ∧ s.gpr .x23 ≠ 0 ∧ CI s₀ C D P W R L (i + 1) s)

theorem body_wp (v : Proof.Aes.AArch64.Ctr32Impl) (h : Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {i : Nat} {s : State}
    (hs : CI s₀ C D P W R L i s) :
    WP isa (ctrBody v.callee) s (BPost s₀ C D P W R L i) := by
  obtain ⟨m₀, q, x, hi⟩ := hs
  refine ctr_head v h hcp hi fun t₃ hh => WP.mono (ctr_tail h hPw hi hh) fun t ht => ?_
  rcases ht with ⟨hc, hz, hd⟩ | ⟨hc, hz, hi'⟩
  · exact Or.inl ⟨hc, hz, hd.x19, hd.x20, hd.x21, hd.x26, hd.x27, hd.sp, hd.rd, hd.wr⟩
  · exact Or.inr ⟨hc, hz, m₀, q, x, hi'⟩

theorem CI.cr {i : Nat} {s : State} (hs : CI s₀ C D P W R L i s) : CR s₀ C D P W R L i s :=
  let ⟨_, _, _, hi⟩ := hs; hi.cr

theorem eval_x23 (s : State) : isa.eval (.nonzero .x .x23) s = some (s.gpr .x23 != 0) := by
  show some (s.read .x .x23 != 0) = _
  rw [State.read, BitVec.setWidth_eq]

theorem loop_rel (v : Proof.Aes.AArch64.Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L)
    (h' : Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) (n : Nat) :
    RelCT isa (fun a b => ∃ i, n = L - 16 * i ∧ CI s₀ C D P W R L i a ∧ CI s₀' C D P W R L i b)
      (.loop (ctrBody v.callee) (.nonzero .x .x23)) fun a b => CE s₀ C D P W R L a ∧ CE s₀' C D P W R L b := by
  refine RelCT.loop (M := isa) (fun (k : Nat) (a b : State) => ∃ i, k = L - 16 * i ∧ CI s₀ C D P W R L i a ∧
    CI s₀' C D P W R L i b) (fun k => ?_) n
  refine RelCT.exists_ fun i => ?_
  by_cases hk : k = L - 16 * i
  swap
  · exact RelCT.of_false fun a b hab => hk hab.1
  refine (((body_rel v h h' hq i).mono (fun a b hab => ⟨hab.2.1.cr, hab.2.2.cr⟩) fun _ _ h => h).wp
    (F₁ := BPost s₀ C D P W R L i) (F₂ := BPost s₀' C D P W R L i)
    fun a b hab => ⟨body_wp v h hcp hPw hab.2.1, body_wp v h' hcp hPw' hab.2.2⟩).mono
    (fun _ _ h => h) fun a b ⟨_, ha, hb⟩ => ?_
  rw [eval_x23, eval_x23]
  rcases ha with ⟨hc, hz, he⟩ | ⟨hc, hz, hci⟩ <;> rcases hb with ⟨hc', hz', he'⟩ | ⟨hc', hz', hci'⟩
  · exact ⟨by rw [hz, hz'], fun _ => ⟨he, he'⟩, fun e => by simp [hz] at e⟩
  · omega
  · omega
  · exact ⟨by rw [hci.cr.x23, hci'.cr.x23], fun e => (hz (by simpa using e)).elim, fun _ =>
      ⟨L - 16 * (i + 1), by have := hci.cr; omega, i + 1, rfl, hci, hci'⟩⟩

/-- What `ctr` needs of a run: the registers, the data in `x26` and `x27`,
and a counter `Q`. -/
structure CtrPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : Regs s₀ C D P W R L s
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  cnt : ∃ (hi lo : BitVec 64) (q : List Byte), s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q

theorem CtrPre.ci {s : State} (hs : CtrPre s₀ C D P W R L s) (hL : 0 < L) : CI s₀ C D P W R L 0 s := by
  obtain ⟨hi₀, lo₀, q, hhi, hlo, hq⟩ := hs.cnt
  exact ⟨s.mem, q, Spec.Aes.bytesAt s.mem P L, ⟨⟨hs.regs.x19, hs.regs.x20, hs.regs.x21,
    by rw [hs.regs.x22, Nat.mul_zero, k0], by rw [hs.regs.x23, Nat.mul_zero, Nat.sub_zero], hs.x26, hs.x27,
    hs.regs.sp, hs.regs.rd, hs.regs.wr⟩, by omega,
    ⟨hi₀, lo₀, hhi, hlo, by rw [hq]; exact (BitVec.add_zero _).symm⟩, by rw [Nat.mul_zero, ctrPart_zero],
    Frame.refl _ _⟩⟩

theorem CtrPre.ce {s : State} (hs : CtrPre s₀ C D P W R L s) : CE s₀ C D P W R L s :=
  ⟨hs.regs.x19, hs.regs.x20, hs.regs.x21, hs.x26, hs.x27, hs.regs.sp, hs.regs.rd, hs.regs.wr⟩

theorem ctr_rel' (v : Proof.Aes.AArch64.Ctr32Impl) {s₀' : State} (h : Env s₀ C D P W R L)
    (h' : Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => CtrPre s₀ C D P W R L a ∧ CtrPre s₀' C D P W R L b) (ctr v.callee)
      fun a b => (Regs s₀ C D P W R L a ∧ a.gpr .x26 = P ∧ a.gpr .x27 = BitVec.ofNat 64 L) ∧
        Regs s₀' C D P W R L b ∧ b.gpr .x26 = P ∧ b.gpr .x27 = BitVec.ofNat 64 L := by
  have hlt := h.lt
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x26, .x27])
      (.block [mov .x22 .x26, mov .x23 .x27]) hc).isSome = true := ⟨_, by taint_decide⟩
  have ev {σ s : State} (hs : CtrPre σ C D P W R L s) : isa.eval (.zero .x .x23) s = some (decide (L = 0)) :=
    eval_zero hlt hs.regs.x23
  have i := RelCT.ite (M := isa) (c := .zero .x .x23)
    (P := fun a b => CtrPre s₀ C D P W R L a ∧ CtrPre s₀' C D P W R L b)
    (Q := fun a b => CE s₀ C D P W R L a ∧ CE s₀' C D P W R L b)
    (fun a b hab => by rw [ev hab.1, ev hab.2])
    (RelCT.block_nil fun a b hab => ⟨hab.1.1.ce, hab.1.2.ce⟩)
    ((loop_rel v h h' hq hcp hPw hPw' (L - 16 * 0)).mono (fun a b hab => by
      have hL : 0 < L := by
        have e := hab.2; rw [ev hab.1.1] at e
        simp at e; omega
      exact ⟨0, rfl, hab.1.1.ci hL, hab.1.2.ci hL⟩) fun _ _ h => h)
  have we {σ s : State} (hs : CE σ C D P W R L s) :
      WP isa (.block [mov .x22 .x26, mov .x23 .x27]) s fun t =>
        Regs σ C D P W R L t ∧ t.gpr .x26 = P ∧ t.gpr .x27 = BitVec.ofNat 64 L := by
    have hd := hs
    obtain ⟨t, run, x22, x23, g, sp, _, rd, wr⟩ := ctrEnd_ok hd.x26 hd.x27
    exact WP.of_runBlock ⟨t, run, ⟨by rw [g _ (by decide) (by decide), hd.x19], by rw [g _ (by decide) (by decide),
      hd.x20], by rw [g _ (by decide) (by decide), hd.x21], x22, x23, by rw [sp, hd.sp], by rw [rd, hd.rd],
      by rw [wr, hd.wr]⟩, by rw [g _ (by decide) (by decide), hd.x26], by rw [g _ (by decide) (by decide), hd.x27]⟩
  have hx (σ : State) (s : State) (hs : CE σ C D P W R L s) : s.gpr .x26 = P ∧ s.gpr .x27 = BitVec.ofNat 64 L ∧
      s.sp = σ.sp := by
    exact ⟨hs.x26, hs.x27, hs.sp⟩
  have e := (RelCT.taint (A := taint) (P := fun a b => CE s₀ C D P W R L a ∧ CE s₀' C D P W R L b) _
    (fun a b hab => by
      obtain ⟨a26, a27, asp⟩ := hx _ _ hab.1
      obtain ⟨b26, b27, bsp⟩ := hx _ _ hab.2
      refine agree_of (by rw [asp, bsp, hq]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a26, b26]
      · rw [a27, b27]) hB).wp
    (F₁ := fun (t : State) => Regs s₀ C D P W R L t ∧ t.gpr .x26 = P ∧ t.gpr .x27 = BitVec.ofNat 64 L)
    (F₂ := fun (t : State) => Regs s₀' C D P W R L t ∧ t.gpr .x26 = P ∧ t.gpr .x27 = BitVec.ofNat 64 L)
    fun a b hab => ⟨we hab.1, we hab.2⟩
  exact i.seq (e.mono (fun _ _ h => h) fun _ _ h => h.2)

end VG.Proof.AesSiv.AArch64
