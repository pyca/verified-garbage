module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Open
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Open
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ok
meta import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_open` with the interleaved loop is constant time

Untrusted: everything here is checked by Lean. As for `open`
(`FnCT.lean`), two runs with the same public arguments are related piece by
piece: `stitched`'s straight blocks and the interleaved loop pass the taint
analysis from the registers that agree (`dec_check`), and its calls are
related as `crypt`'s and `polyval`'s are (`blksFrom_rel`, `tail_rel`,
`absorb_rel`, `lens_rel`); what each run keeps between the pieces (`Bufs`)
follows from their correctness.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl toNat_ofNat_of_lt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-! ## What each run keeps -/

/-- `Bufs`, after code that writes apart from the slots and keeps the permissions. -/
theorem Bufs.frame {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t t' : State}
    (h : Bufs K W SP R N A D al n t) (E : Env K W SP t') {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    Bufs K W SP R N A D al n t' :=
  ⟨⟨E, h.one.sl.of_frame hf hd, hwr.trans h.one.wr⟩, h.aad.of_eq hrd hwr, h.data.of_eq hrd hwr⟩

theorem Bufs.dw {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) : Covers [⟨D, n⟩] t.wr := by
  rw [h.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)

/-- Counter mode with the first `k` bytes done, done again, is the input. -/
theorem ctrPart_ctrPart (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (k : Nat) :
    GcmSiv.ctrPart ciph icb (GcmSiv.ctrPart ciph icb x k) k = x := by
  refine GcmSiv.ext_getD (by simp [GcmSiv.length_ctrPart]) fun p hp => ?_
  simp only [GcmSiv.length_ctrPart] at hp
  rw [GcmSiv.getD_ctrPart _ _ _ _ (by simp [GcmSiv.length_ctrPart, hp]), GcmSiv.getD_ctrPart _ _ _ _ hp]
  split <;> simp [BitVec.xor_assoc]

/-- A counter block at `W + 96` is block `j₀` of some initial counter block. -/
theorem CtrSt.any (W : Addr) (m : Mem) (j₀ : Nat) :
    CtrSt W (Proof.Cmac.le4 (m.readW (W + BitVec.ofNat 64 96) 32 - BitVec.ofNat 32 j₀) ++
      bytesAt m (W + BitVec.ofNat 64 100) 12) j₀ m := by
  refine ⟨?_, by rw [List.drop_left' (Proof.Cmac.length_le4 _)]⟩
  rw [List.take_left' (Proof.Cmac.length_le4 _), GcmSiv.leNat_le4, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.sub_add_cancel]

/-- Counter mode on the data from block `j₀` keeps `Bufs`, whatever the data
and the counter block. -/
theorem cryptRest_bufs (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat} {t : State} (h : Bufs K W SP R N A D al n t) {j₀ : Nat}
    (hj₀ : 16 * j₀ ≤ n) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j₀))
    (hbp : t.gpr .rbp = BitVec.ofNat 64 (n - 16 * j₀)) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.cryptRest v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) t
      (Bufs K W SP R N A D al n) :=
  WP.mono (cryptRest_ok v eb wide L hR h.one.env h.one.sl h.data h.dw
    (icb := Proof.Cmac.le4 (t.mem.readW (W + BitVec.ofNat 64 96) 32 - BitVec.ofNat 32 j₀) ++
      bytesAt t.mem (W + BitVec.ofNat 64 100) 12)
    (x := GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Proof.Cmac.le4 (t.mem.readW (W + BitVec.ofNat 64 96) 32 - BitVec.ofNat 32 j₀) ++
        bytesAt t.mem (W + BitVec.ofNat 64 100) 12) (bytesAt t.mem D n) (16 * j₀))
    (by rw [GcmSiv.length_ctrPart, Proof.Cmac.bytesAt_length]) hj₀ h12 hbp (CtrSt.any W t.mem j₀)
    (by rw [ctrPart_ctrPart]) rfl) fun _ P => h.frame P.env P.frame (slots_cryR L h.data) P.rd P.wr

/-- The registers the loop takes. -/
structure ArgsAt (W D : Addr) (R n : Nat) (t : State) : Prop where
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 248
  rsi : t.gpr .rsi = BitVec.ofNat 64 R
  rdx : t.gpr .rdx = W + BitVec.ofNat 64 96
  rcx : t.gpr .rcx = W + BitVec.ofNat 64 80
  r8 : t.gpr .r8 = W + BitVec.ofNat 64 64
  r11 : t.gpr .r11 = W + BitVec.ofNat 64 1768
  r12 : t.gpr .r12 = D
  r9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))

/-- The interleaved loop keeps `Bufs`. -/
theorem dec_bufs {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    (h256 : 256 ≤ n) {t : State} (h : Bufs K W SP R N A D al n t ∧ ArgsAt W D R n t) :
    WP isa Impl.AesGcmSiv.X86_64Stitch.dec t (Bufs K W SP R N A D al n) := by
  obtain ⟨hB, G⟩ := h
  have hn := hB.data.lt
  have hp := spre_of L hR hB.one.env hB.data hB.dw h256 G.rdi G.rsi G.rdx G.rcx G.r8 G.r11 G.r12 G.r9
  have hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [G.r9, toNat_ofNat_of_lt (by omega)]
  refine WP.mono (Stitch.dec_ok hp (by rw [hnb]; omega)) fun t' Dp => ?_
  have Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 1768, 256⟩] t.mem t'.mem := by
    have h := Dp.frame
    simp only [Stitch.cR, Stitch.yR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.yp, Stitch.dp, Stitch.pp, hnb, G.rdx,
      G.rcx, G.r12, G.r11] at h
    exact h
  refine hB.frame (hB.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Dp.gpr _ (by decide) (by decide) (by decide) (by decide)) Dp.rd Dp.wr)
    Fd (fun q hq => ?_) Dp.rd Dp.wr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact (hB.data.w.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide)) |>.symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- `stitched`'s head keeps `Bufs`, and gives `absorb` the additional data. -/
theorem sHead_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))]) t fun t₁ =>
      AbsIn K W SP R N A D al n A al t₁ ∧ Bufs K W SP R N A D al n t₁ := by
  obtain ⟨t₁, run₁, hm₁, h12₁, hbp₁, hg₁, hrd₁, hwr₁⟩ := sHead_ok h.one.env h.one.sl
  have E₁ : Env K W SP t₁ := h.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have B₁ : Bufs K W SP R N A D al n t₁ := h.frame E₁ (by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _)
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    hrd₁ hwr₁
  exact WP.of_runBlock ⟨t₁, run₁, ⟨B₁.one, B₁.aad, h12₁, hbp₁⟩, B₁⟩

theorem sHead_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sArgs_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) :
    WP isa (.block sArgs) t fun t₁ => Bufs K W SP R N A D al n t₁ ∧ ArgsAt W D R n t₁ := by
  obtain ⟨t₁, run₁, hm₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r11₁, r12₁, r9₁, hg₁, hrd₁, hwr₁⟩ :=
    sArgs_ok h.one.env h.one.sl h.data.lt
  have E₁ : Env K W SP t₁ := h.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨t₁, run₁, h.frame E₁ (by rw [hm₁]; exact Frame.refl [] _) (by simp) hrd₁ hwr₁,
    ⟨rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r11₁, r12₁, r9₁⟩⟩

theorem sArgs_check : ∃ hc, (taint.check (sivT []) (.block sArgs) hc).isSome = true := ⟨_, by taint_decide⟩

theorem dec_check : ∃ hc, (taint.check (sivT [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9])
    Impl.AesGcmSiv.X86_64Stitch.dec hc).isSome = true := ⟨_, by taint_decide⟩

theorem rest_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) :
    WP isa (.block Impl.AesGcmSiv.X86_64Stitch.rest) t fun t₁ => Bufs K W SP R N A D al n t₁ ∧
      t₁.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 256) := by
  obtain ⟨t₁, run₁, hm₁, h12₁, hbp₁, hg₁, hrd₁, hwr₁⟩ := rest_ok h.one.env h.one.sl h.data.lt
  have E₁ : Env K W SP t₁ := h.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨t₁, run₁, h.frame E₁ (by rw [hm₁]; exact Frame.refl [] _) (by simp) hrd₁ hwr₁,
    h12₁, hbp₁⟩

theorem rest_check : ∃ hc, (taint.check (sivT []) (.block Impl.AesGcmSiv.X86_64Stitch.rest) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## Counter mode on the rest of the data -/

/-- The whole blocks of counter mode from block `j₀`, in two runs. -/
theorem blksFrom_rel (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n b j₀ : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hn : n ≤ 2 ^ 64) (hb : 16 * b ≤ n) (hj₀ : j₀ < b) :
    RelCT isa (fun t₁ t₂ => CInv K W SP R N A D al n b j₀ t₁ ∧ CInv K W SP R N A D al n b j₀ t₂)
      (.loop (cryptChunk ⟨eb.enc.name, eb.enc.code⟩ wide) .ne)
      fun t₁ t₂ => CInv K W SP R N A D al n b b t₁ ∧ CInv K W SP R N A D al n b b t₂ := by
  refine (RelCT.loop (fun m t₁ t₂ => ∃ j, m = b - j ∧ j < b ∧ CInv K W SP R N A D al n b j t₁ ∧
      CInv K W SP R N A D al n b j t₂) (fun m => ?_) (b - j₀)).mono (fun t₁ t₂ h => ⟨j₀, rfl, hj₀, h⟩)
      fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hj : j < b
  · by_cases hm : m = b - j
    · subst hm
      refine (ctrChunk_rel eb wide L hR hDW hn hb hj).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [eval_ne z₁] at hc
        have he : j + min 64 (b - j) = b := by simp at hc; omega
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [eval_ne z₁] at hc
        have he : b - (j + min 64 (b - j)) ≠ 0 := by simpa using hc
        exact ⟨b - (j + min 64 (b - j)), by omega, j + min 64 (b - j), rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hj h.2.1

/-- A run before counter mode from block `j₀`. -/
structure RestIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n j₀ : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  buf : Buf K W SP t D n
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j₀)
  rbp : t.gpr .rbp = BitVec.ofNat 64 (n - 16 * j₀)

theorem split_cinv {K W SP : Addr} {R : Nat} {N A D : Addr} {al n j₀ : Nat} (hj₀ : 16 * j₀ ≤ n) {t : State}
    (I : RestIn K W SP R N A D al n j₀ t) :
    WP isa (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) t
      fun t₁ => CInv K W SP R N A D al n (n / 16) j₀ t₁ ∧ t₁.zf = some (decide ((n - 16 * j₀) / 16 = 0)) := by
  have hn := I.buf.lt
  obtain ⟨t₁, run₁, hbx₁, hbp₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ := split16_ok (m := n - 16 * j₀) (by omega) I.rbp
  refine WP.of_runBlock ⟨t₁, run₁, ⟨⟨I.one.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁, by rw [hm₁]; exact I.one.sl,
    hwr₁.trans I.one.wr⟩, I.buf.of_eq hrd₁ hwr₁, by rw [hg₁ _ (by decide) (by decide), I.r12],
    by rw [hbx₁]; congr 1; omega, by rw [hbp₁]; congr 1; omega⟩, hzf₁⟩

/-- Counter mode from block `j₀`, in two runs. -/
theorem cryptRest_rel (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n j₀ : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hn : n ≤ 2 ^ 64) (hj₀ : 16 * j₀ ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → RestIn K W SP R N A D al n j₀ t₁ ∧ RestIn K W SP R N A D al n j₀ t₂) :
    RelCT isa P (Impl.AesGcmSiv.X86_64Stitch.cryptRest v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      fun _ _ => True := by
  have r₁ := (rel_taintC [.r12, .rbp] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [(hP _ _ h).1.r12, (hP _ _ h).2.r12]
      · rw [(hP _ _ h).1.rbp, (hP _ _ h).2.rbp]⟩) absHead_check).wp
    (F₁ := fun (t₁ : State) => CInv K W SP R N A D al n (n / 16) j₀ t₁ ∧
      t₁.zf = some (decide ((n - 16 * j₀) / 16 = 0)))
    (F₂ := fun (t₁ : State) => CInv K W SP R N A D al n (n / 16) j₀ t₁ ∧
      t₁.zf = some (decide ((n - 16 * j₀) / 16 = 0)))
    fun t₁ t₂ h => ⟨split_cinv hj₀ (hP _ _ h).1, split_cinv hj₀ (hP _ _ h).2⟩
  have r₂ : RelCT isa (fun t₁ t₂ => True ∧ (CInv K W SP R N A D al n (n / 16) j₀ t₁ ∧
        t₁.zf = some (decide ((n - 16 * j₀) / 16 = 0))) ∧ (CInv K W SP R N A D al n (n / 16) j₀ t₂ ∧
        t₂.zf = some (decide ((n - 16 * j₀) / 16 = 0))))
      (.ite .e (.block []) (.loop (cryptChunk ⟨eb.enc.name, eb.enc.code⟩ wide) .ne))
      fun t₁ t₂ => CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧ CInv K W SP R N A D al n (n / 16) (n / 16) t₂ := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) ?_ ?_
    · refine RelCT.block_nil fun t₁ t₂ h => ?_
      have h0 : (n - 16 * j₀) / 16 = 0 := by have := h.2; rw [eval_e h.1.2.1.2] at this; simpa using this
      have a := h.1.2.1.1
      have b := h.1.2.2.1
      rw [show j₀ = n / 16 by omega] at a b
      exact ⟨a, b⟩
    · by_cases h0 : (n - 16 * j₀) / 16 = 0
      · refine RelCT.of_false fun t₁ t₂ h => ?_
        have := h.2
        rw [eval_e h.1.2.1.2] at this
        simp [h0] at this
      · exact (blksFrom_rel eb wide L hR hDW hn (b := n / 16) (by omega) (by omega)).mono
          (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
  have r₃ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧
      CInv K W SP R N A D al n (n / 16) (n / 16) t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) test_check).wp
    (F₁ := fun (t : State) => CInv K W SP R N A D al n (n / 16) (n / 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    (F₂ := fun (t : State) => CInv K W SP R N A D al n (n / 16) (n / 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    fun t₁ t₂ h => ⟨test_cinv h.1, test_cinv h.2⟩
  have r₄ : RelCT isa (fun t₁ t₂ => True ∧ (CInv K W SP R N A D al n (n / 16) (n / 16) t₁ ∧
        t₁.zf = some (decide (n % 16 = 0))) ∧ (CInv K W SP R N A D al n (n / 16) (n / 16) t₂ ∧
        t₂.zf = some (decide (n % 16 = 0))))
      (.ite .e (.block []) (cryptTail v.callees)) fun _ _ => True :=
    RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) (RelCT.block_nil fun _ _ _ => trivial)
      ((tail_rel v L hR hDW hn).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ _ => trivial)
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

/-! ## `stitched` -/

theorem lens_bufs (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64) {t : State} (h : Bufs K W SP R N A D al n t) :
    WP isa (lens v.callees) t (Bufs K W SP R N A D al n) :=
  WP.mono (lens_ok v L h.one.env h.one.sl.alen h.one.sl.len hal hn') fun _ P => h.of_eq P.env P.frame L P.rd P.wr

theorem ArgsAt.both {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t₁ t₂ : State}
    (h₁ : Bufs K W SP R N A D al n t₁ ∧ ArgsAt W D R n t₁) (h₂ : Bufs K W SP R N A D al n t₂ ∧ ArgsAt W D R n t₂) :
    Both K W SP R N A D al n [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9] t₁ t₂ :=
  ⟨h₁.1.one, h₂.1.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.rdi, h₂.2.rdi]
    · rw [h₁.2.rsi, h₂.2.rsi]
    · rw [h₁.2.rdx, h₂.2.rdx]
    · rw [h₁.2.rcx, h₂.2.rcx]
    · rw [h₁.2.r8, h₂.2.r8]
    · rw [h₁.2.r11, h₂.2.r11]
    · rw [h₁.2.r12, h₂.2.r12]
    · rw [h₁.2.r9, h₂.2.r9]⟩

/-- `stitched`, in two runs with the same public arguments. -/
theorem stitched_rel (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64) (h256 : 256 ≤ n) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂) :
    RelCT isa P (Impl.AesGcmSiv.X86_64Stitch.stitched v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    sHead_check).wp
    (F₁ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨sHead_wp L (hP _ _ h).1, sHead_wp L (hP _ _ h).2⟩
  have r₂ := (absorb_rel v wide L hDW hn (Q := A) (nb := al) (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n A al t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n A al t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v wide L h.2.1, absorb_bufs v wide L h.2.2⟩
  have r₃ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) sArgs_check).wp
    (F₁ := fun (t : State) => Bufs K W SP R N A D al n t ∧ ArgsAt W D R n t)
    (F₂ := fun (t : State) => Bufs K W SP R N A D al n t ∧ ArgsAt W D R n t)
    fun t₁ t₂ h => ⟨sArgs_wp h.2.1, sArgs_wp h.2.2⟩
  have r₄ := (rel_taintC [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9] (P := fun t₁ t₂ => True ∧
      (Bufs K W SP R N A D al n t₁ ∧ ArgsAt W D R n t₁) ∧ (Bufs K W SP R N A D al n t₂ ∧ ArgsAt W D R n t₂))
    hDW hn (fun t₁ t₂ h => ArgsAt.both h.2.1 h.2.2) dec_check).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨dec_bufs L hR h256 h.2.1, dec_bufs L hR h256 h.2.2⟩
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) rest_check).wp
    (F₁ := fun (t : State) => Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256))
    (F₂ := fun (t : State) => Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256))
    fun t₁ t₂ h => ⟨rest_wp h.2.1, rest_wp h.2.2⟩
  have restIn : ∀ {t : State}, (Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256)) →
      RestIn K W SP R N A D al n (16 * (n / 256)) t := fun h =>
    ⟨h.1.one, h.1.data, by rw [h.2.1, show 256 * (n / 256) = 16 * (16 * (n / 256)) by omega],
      by rw [h.2.2, show n % 256 = n - 16 * (16 * (n / 256)) by omega]⟩
  have r₆ := (cryptRest_rel v eb wide L hR hDW hn (j₀ := 16 * (n / 256)) (by omega) (P := fun t₁ t₂ => True ∧
      (Bufs K W SP R N A D al n t₁ ∧ t₁.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧
        t₁.gpr .rbp = BitVec.ofNat 64 (n % 256)) ∧
      (Bufs K W SP R N A D al n t₂ ∧ t₂.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧
        t₂.gpr .rbp = BitVec.ofNat 64 (n % 256)))
    fun t₁ t₂ h => ⟨restIn h.2.1, restIn h.2.2⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨cryptRest_bufs v eb wide L hR h.2.1.1 (by omega) (restIn h.2.1).r12 (restIn h.2.1).rbp,
      cryptRest_bufs v eb wide L hR h.2.2.1 (by omega) (restIn h.2.2).r12 (restIn h.2.2).rbp⟩
  have absIn : ∀ {t : State}, (Bufs K W SP R N A D al n t ∧
      t.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t.gpr .rbp = BitVec.ofNat 64 (n % 256)) →
      AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t ∧
        Bufs K W SP R N A D al n t := fun h =>
    ⟨⟨h.1.one, h.1.data.slice (by omega), h.2.1, h.2.2⟩, h.1⟩
  have r₇ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) rest_check).wp
    (F₁ := fun (t : State) =>
      AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) =>
      AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨WP.mono (rest_wp h.2.1) fun _ h => absIn h, WP.mono (rest_wp h.2.2) fun _ h => absIn h⟩
  have r₈ := (absorb_rel v wide L hDW hn (Q := D + BitVec.ofNat 64 (256 * (n / 256))) (nb := n % 256)
    (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v wide L h.2.1, absorb_bufs v wide L h.2.2⟩
  have r₉ := (lens_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧
      Bufs K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨lens_bufs v L hal hn' h.2.1, lens_bufs v L hal hn' h.2.2⟩
  have r₁₀ := rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) tagIn_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ (RelCT.seq r₇
    (RelCT.seq r₈ (RelCT.seq r₉ r₁₀))))))))


/-! ## `vg_aes_gcm_siv_open` -/

theorem lenCmp_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .cmp .rax (imm 256)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem lenCmp_stk {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : StK K W SP R N A D al n T t) :
    WP isa (.block [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .cmp .rax (imm 256)]) t fun t' =>
      StK K W SP R N A D al n T t' ∧ t'.cf = some (decide (n < 256)) := by
  obtain ⟨t₁, run₁, hcf₁, hg₁, hm₁, hrd₁, hwr₁⟩ := lenCmp_ok h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data.lt
  refine WP.of_runBlock ⟨t₁, run₁, ⟨h.1.frame (h.1.bufs.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁) (by rw [hm₁]; exact Frame.refl [] _)
    (by simp) (by rw [hm₁]; exact Frame.refl _ _) hrd₁ hwr₁, by rw [hm₁]; exact h.2.1, by rw [hm₁]; exact h.2.2⟩,
    hcf₁⟩

/-- Deciphering and the tag input, either way, keep `St`. -/
theorem mid_st (v : GcmImpl) (eb : BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 14) {N A D T : Addr} {al n : Nat} (hND : (⟨N, 12⟩ : Region).Disjoint ⟨D, n⟩)
    (hAD : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩) {t : State}
    (h : StK K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256))) :
    WP isa (.ite .b (.seq (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (polyval v.callees wide))
      (Impl.AesGcmSiv.X86_64Stitch.stitched v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)) t
      (St K W SP R N A D al n T) := by
  obtain ⟨h, hcf⟩ := h
  refine WP.ite (decide (n < 256)) (eval_b hcf) (fun _ => ?_) (fun hf => ?_)
  · exact WP.seq (WP.mono (crypt_st v eb wide L hR h) fun _ h' => polyval_st v wide L h')
  · exact WP.mono (stitched_ok v eb wide L hR h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.aad h.1.bufs.data h.1.nonce
      h.1.bufs.dw hND hAD h.2.1 h.2.2 (by simpa using hf)) fun _ Md =>
      h.1.frame Md.env Md.frame (mid_disj L h.1.bufs.data.w (.inr ⟨by decide, by decide⟩))
        (Md.frame.sub (mid_mut W SP D n)) Md.rd Md.wr

theorem openSBody_rel (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hND : (⟨N, 12⟩ : Region).Disjoint ⟨D, n⟩) (hAD : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩)
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (.seq (.block recv) (.seq (keys v.callees ⟨eb.enc.name, eb.enc.code⟩)
      (.seq (.block [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .cmp .rax (imm 256)])
      (.seq (.ite .b (.seq (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (polyval v.callees wide))
        (Impl.AesGcmSiv.X86_64Stitch.stitched v.callees ⟨eb.enc.name, eb.enc.code⟩ wide))
      (.seq (tag v.callees bO) (.seq (.block Impl.AesGcmSiv.X86_64.cmp) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))))
      fun _ _ => True := by
  have r₀ := (rel_loadT (l := recv.tail) (fun t₁ t₂ h =>
      ⟨(hP _ _ h).1.tagIn rfl rfl (Covers.refl _), (hP _ _ h).2.tagIn rfl rfl (Covers.refl _)⟩) recv_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨by rw [← recv_split]; exact recv_st L (hP _ _ h).1, by rw [← recv_split]; exact recv_st L (hP _ _ h).2⟩
  have r₁ := (keys_rel v eb L hR hDW hn (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.nonce⟩, ⟨h.2.2.bufs.one, h.2.2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨keys_st v eb L hR h.2.1, keys_st v eb L hR h.2.2⟩
  have r₂ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩)
    lenCmp_check).wp
    (F₁ := fun (t : State) => StK K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    (F₂ := fun (t : State) => StK K W SP R N A D al n T t ∧ t.cf = some (decide (n < 256)))
    fun t₁ t₂ h => ⟨lenCmp_stk h.2.1, lenCmp_stk h.2.2⟩
  have i₃ : RelCT isa (fun t₁ t₂ => True ∧ (StK K W SP R N A D al n T t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
        (StK K W SP R N A D al n T t₂ ∧ t₂.cf = some (decide (n < 256))))
      (.ite .b (.seq (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (polyval v.callees wide))
        (Impl.AesGcmSiv.X86_64Stitch.stitched v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_b h.2.1.2, eval_b h.2.2.2]) ?_ ?_
    · have c₁ := (crypt_rel v eb wide L hR hDW hn (P := fun t₁ t₂ => (True ∧
          (StK K W SP R N A D al n T t₁ ∧ t₁.cf = some (decide (n < 256))) ∧
          (StK K W SP R N A D al n T t₂ ∧ t₂.cf = some (decide (n < 256)))) ∧ isa.eval .b t₁ = some true)
        fun t₁ t₂ h => ⟨⟨h.1.2.1.1.1.bufs.one, h.1.2.1.1.1.bufs.data⟩,
          ⟨h.1.2.2.1.1.bufs.one, h.1.2.2.1.1.bufs.data⟩⟩).wp
        (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
        fun t₁ t₂ h => ⟨crypt_st v eb wide L hR h.1.2.1.1, crypt_st v eb wide L hR h.1.2.2.1⟩
      exact RelCT.seq c₁ (polyval_rel v wide L hDW hn hal hn' fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩)
    · by_cases hn256 : 256 ≤ n
      · exact stitched_rel v eb wide L hR hDW hn hal hn' hn256 fun t₁ t₂ h =>
          ⟨h.1.2.1.1.1.bufs, h.1.2.2.1.1.bufs⟩
      · refine RelCT.of_false fun _ _ h => hn256 ?_
        have := h.2; rw [eval_b h.1.2.1.2] at this; simp at this; omega
  have r₃ := i₃.wp (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨mid_st v eb wide L hR hND hAD h.2.1, mid_st v eb wide L hR hND hAD h.2.2⟩
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
theorem openS_rel (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {s₀ s₀' : State} (hp : openPre s₀) (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcmSiv.X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)
      fun _ _ => True := by
  have Ar := (args_of_open hp).1.1
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_open hp').1.1 rfl) (entry_open hp) (entry_open_pub hp' hq)) ?_
  exact openSBody_rel v eb wide Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.aad.lt Ar.data.lt Ar.nd Ar.ad
    fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesGcmSiv.X86_64
