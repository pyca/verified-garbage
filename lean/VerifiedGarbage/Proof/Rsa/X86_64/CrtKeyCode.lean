import VerifiedGarbage.Proof.Rsa.X86_64.KeyCode
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyMain
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyEntry

/-!
# `vg_rsa_check_crt_key` on x86-64: correctness

`code`, from a state its contract allows, returns `checkCrtKey` of its
inputs as 1 or 0 (`ckCode_correct`), against `ckContract`, which states the
shared contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK sMask exit invalid)

/-! ## The contract on the registers and the stack -/

/-- The key's checks, from the arguments. -/
def ckOf (s : State) : Bool :=
  Spec.Rsa.checkCrtKey (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r9).toNat)

/-- `vg_rsa_check_crt_key(n = rdi, n_len = rsi, e = rdx, e_len = rcx, p = r8,
p_len = r9, q = [rsp + 8], q_len = [rsp + 16], dp = [rsp + 24],
dp_len = [rsp + 32], dq = [rsp + 40], dq_len = [rsp + 48],
qinv = [rsp + 56], qinv_len = [rsp + 64], scratch = [rsp + 72],
scratch_len = [rsp + 80])`. -/
def ckContract : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let p : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dp : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dq : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let qi : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64 ∧
      s.rd = [n, e, p, q, dp, dq, qi, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint p ∧ ret.Disjoint q ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < (s.gpr .rsi).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .rsi).toNat ∧ (stackArg s 3).toNat = (s.gpr .r9).toNat ∧
      (stackArg s 7).toNat = (s.gpr .r9).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 9).toNat
  post s s' := (s'.gpr .rax).setWidth 32 = if ckOf s then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧ stackArg s₁ 8 = stackArg s₂ 8 ∧
      stackArg s₁ 9 = stackArg s₂ 9 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

/-! ## The precondition, as the code uses it -/

/-- What `code` uses of its contract's precondition, for the working space
`B` (stack argument 8) of `Z` bytes. -/
structure CkArgs (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat ≤ 1024
  el1 : 1 ≤ (s.gpr .rcx).toNat
  el2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  pl1 : 1 ≤ (s.gpr .r9).toNat
  pl2 : (s.gpr .r9).toNat < (s.gpr .rsi).toNat
  ql1 : 1 ≤ (stackArg s 1).toNat
  ql2 : (stackArg s 1).toNat < (s.gpr .rsi).toNat
  hZ : 128 * (s.gpr .rsi).toNat ≤ (stackArg s 9).toNat * 8
  hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8)
  ha : ∀ j < 9, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 9, ∀ m', Outside (stackArg s 8) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  nb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .rdi)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  eb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  qb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  dpb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 2)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r9).toNat)
  dqb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 4)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
  qib : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 6)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r9).toNat)
  hret : ∀ b < 8, (stackArg s 9).toNat * 8 ≤ ofs (stackArg s 8) (s.gpr .rsp + BitVec.ofNat 64 b)

theorem ckArgs_of {s : State} (h : ckContract.pre s) : CkArgs s := by
  simp only [ckContract] at h
  sig_split h
  rename_i hsp hrd hwr dns des dps dqs ddps ddqs dqis dsa dRn dRe dRp dRq dRdp dRdq dRqi dRs dRa wN
    wE wP wQ wDp wDq wQi wS hk hel1 hel2 hpl1 hpl2 hql1 hql2 hdpl hqil hdql
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 80⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hel1, hel2, hpl1, hpl2, hql1, hql2, by omega, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 80) (by omega) (by omega))
      rw [← stackArgAddr_add' s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega) (by rw [← hqil]; exact dqis),
    fun b hb => out_scr dRs (contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega))⟩

/-! ## The exits -/

/-- What `code` leaves, from the result `cb` and the saved registers. -/
theorem ckFin {s t₁ t : State} (c : CkArgs s) (h₁ : CkEntryPost s (stackArg s 8) t₁) {cb : Bool}
    (hax : t.gpr .rax = BitVec.ofNat 64 cb.toNat)
    (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = word t₁.mem (stackArg s 8) (8 * i))
    (hsp : t.gpr .rsp = s.gpr .rsp) (hin : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem)
    (hcb : cb = ckOf s) : gprPreserved s t ∧ ckContract.post s t := by
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsv 0 (by decide)).trans (h₁.saved 0 (by decide))
    · exact (hsv 1 (by decide)).trans (h₁.saved 1 (by decide))
    · exact hsp
    · exact (hsv 2 (by decide)).trans (h₁.saved 2 (by decide))
    · exact (hsv 3 (by decide)).trans (h₁.saved 3 (by decide))
    · exact (hsv 4 (by decide)).trans (h₁.saved 4 (by decide))
    · exact (hsv 5 (by decide)).trans (h₁.saved 5 (by decide))
  · rw [hin _ (c.hret b hb)]
  · show (t.gpr .rax).setWidth 32 = if ckOf s then 1 else 0
    rw [hax, setWidth_flag, hcb]

/-! ## The steps -/

/-- `expCheck`, after `entry`. -/
theorem expCk_ok {s t₁ : State} (c : CkArgs s) (h₁ : CkEntryPost s (stackArg s 8) t₁) :
    WP isa Impl.Rsa.X86_64.Checked.expCheck t₁ fun t₂ =>
      t₂.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip (keyE s))) ∧ t₂.mem = t₁.mem ∧
      t₂.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (keyE s))) ∧ Keep [.rax, .r10, .r11] t₁ t₂ := by
  have hZ := c.hZ
  have := c.el2
  have := c.k1
  have := c.k2
  have in₁ : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t₁.mem :=
    InScr.of_outside h₁.out (by omega)
  have eb₁ := c.eb.congrK in₁ h₁.keep
  exact expCheckR_ok (s := t₁) (eb := keyE s) h₁.r8 (by rw [h₁.r9, ofNat_toNat64]) c.el1 (by omega)
    (fun i hi => eb₁.rd i (by rw [bytesAt_length]; exact hi))
    (by have := bytesAt_of_src eb₁; rw [bytesAt_length] at this; exact this.symm)

/-- After `entry` and `expCheck`. -/
structure CkAfterExp (s t₁ t₂ : State) : Prop where
  h₁ : CkEntryPost s (stackArg s 8) t₁
  mem : t₂.mem = t₁.mem
  r11 : t₂.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (keyE s)))
  keep : Keep [.rax, .r10, .r11] t₁ t₂

theorem CkAfterExp.scr {s t₁ t₂ : State} (c : CkArgs s) (h : CkAfterExp s t₁ t₂) :
    Scr t₂ (stackArg s 8) ((stackArg s 9).toNat * 8) := (c.hs.congr h.h₁.keep.2.2).congr h.keep.2.2

theorem CkAfterExp.rdi {s t₁ t₂ : State} (h : CkAfterExp s t₁ t₂) : t₂.gpr .rdi = stackArg s 8 :=
  (h.keep.gpr (by decide)).trans h.h₁.rdi

theorem storesCk_ok {s t₁ t₂ : State} (c : CkArgs s) (h : CkAfterExp s t₁ t₂) :
    WP isa (.block keyStores) t₂ fun t₃ => t₃.gpr .rdx = s.gpr .rdi ∧ t₃.gpr .rcx = s.gpr .rsi ∧
      t₃.mem = t₂.mem.writeW (off (stackArg s 8) (8 * sEv)) (t₂.gpr .r11) ∧ Keep [.rdx, .rcx] t₂ t₃ := by
  have hZ := c.hZ
  have := c.k1
  have hs₂ := h.scr c
  have hEv := hs₂.st (d := 8 * sEv) (by unfold sEv sFn; omega)
  have hN₃ : word (t₂.mem.writeW (off (stackArg s 8) (8 * sEv)) (t₂.gpr .r11)) (stackArg s 8) (8 * sN) =
      s.gpr .rdi := by rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), h.mem, h.h₁.hN]
  have hK₃ : word (t₂.mem.writeW (off (stackArg s 8) (8 * sEv)) (t₂.gpr .r11)) (stackArg s 8) (8 * sK) =
      s.gpr .rsi := by rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), h.mem, h.h₁.hK]
  exact WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧
      t.mem = t₂.mem.writeW (off (stackArg s 8) (8 * sEv)) (t₂.gpr .r11)) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, hEv, hs₂.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₂.ld (d := 8 * sK) (by unfold sK sFn; omega), hN₃, hK₃]) rfl) fun t ⟨⟨a, b, m⟩, k⟩ => ⟨a, b, m, k⟩

/-- After the modulus' check. -/
structure CkAfterInv (s t₁ t₂ t₃ t₄ : State) : Prop where
  e : CkAfterExp s t₁ t₂
  m₃ : t₃.mem = t₂.mem.writeW (off (stackArg s 8) (8 * sEv)) (t₂.gpr .r11)
  k₃ : Keep [.rdx, .rcx] t₂ t₃
  m₄ : t₄.mem = t₃.mem
  k₄ : Keep [.rax, .rbp, .rsi] t₃ t₄

theorem CkAfterInv.inScr {s t₁ t₂ t₃ t₄ : State} (c : CkArgs s) (h : CkAfterInv s t₁ t₂ t₃ t₄) :
    InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t₄.mem := by
  have hZ := c.hZ
  have := c.k1
  rw [h.m₄, h.m₃, h.e.mem]
  exact (InScr.of_outside h.e.h₁.out (by omega)).trans
    (InScr.of_outside (writeW_outside (d := 8 * sEv) _ _ _ (by unfold sEv sFn; omega)) (by unfold sEv sFn; omega))

theorem CkAfterInv.keep {s t₁ t₂ t₃ t₄ : State} (h : CkAfterInv s t₁ t₂ t₃ t₄) :
    Keep [.r11, .rax, .rdi, .r8, .r9, .rax, .r10, .r11, .rdx, .rcx, .rax, .rbp, .rsi] s t₄ :=
  ((h.e.h₁.keep.trans h.e.keep).trans h.k₃).trans h.k₄

theorem CkAfterInv.rdi {s t₁ t₂ t₃ t₄ : State} (h : CkAfterInv s t₁ t₂ t₃ t₄) : t₄.gpr .rdi = stackArg s 8 :=
  (h.k₄.gpr (by decide)).trans ((h.k₃.gpr (by decide)).trans h.e.rdi)

theorem CkAfterInv.scr {s t₁ t₂ t₃ t₄ : State} (c : CkArgs s) (h : CkAfterInv s t₁ t₂ t₃ t₄) :
    Scr t₄ (stackArg s 8) ((stackArg s 9).toNat * 8) := ((h.e.scr c).congr h.k₃.2.2).congr h.k₄.2.2

theorem CkAfterInv.hw {s t₁ t₂ t₃ t₄ : State} (h : CkAfterInv s t₁ t₂ t₃ t₄) {i : Nat} (hi : i < 32)
    (hne : i ≠ sEv) : word t₄.mem (stackArg s 8) (8 * i) = word t₁.mem (stackArg s 8) (8 * i) := by
  rw [h.m₄, h.m₃, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm hne), h.e.mem]

theorem CkAfterInv.saved {s t₁ t₂ t₃ t₄ : State} (h : CkAfterInv s t₁ t₂ t₃ t₄) :
    ∀ i < 6, word t₄.mem (stackArg s 8) (8 * i) = word t₁.mem (stackArg s 8) (8 * i) :=
  fun i hi => h.hw (by omega) (by unfold sEv sFn; omega)

theorem invalidCk_ok {s t₁ t₂ t₃ : State} (c : CkArgs s) (h : CkAfterExp s t₁ t₂) (hdx : t₃.gpr .rdx = s.gpr .rdi)
    (hcx : t₃.gpr .rcx = s.gpr .rsi) (hm₃ : t₃.mem = t₂.mem.writeW (off (stackArg s 8) (8 * sEv)) (t₂.gpr .r11))
    (k₃ : Keep [.rdx, .rcx] t₂ t₃) :
    WP isa (.block invalid) t₃ fun t₄ =>
      t₄.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (keyN s)) (s.gpr .rsi).toNat) ∧
        CkAfterInv s t₁ t₂ t₃ t₄ := by
  have in₃ : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t₃.mem :=
    (CkAfterInv.inScr c ⟨h, hm₃, k₃, rfl, Keep.refl _ _⟩ :)
  have nb₃ := c.nb.congrK in₃ ((h.h₁.keep.trans h.keep).trans k₃)
  exact WP.mono (invalid_ok (s := t₃) (nb := keyN s) hdx (by rw [hcx, ofNat_toNat64]) c.k1 c.k2
    (bytesAt_length _ _ _) (fun i hi => nb₃.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => nb₃.val i _))
    fun t₄ ⟨hz, hm₄, k₄⟩ => ⟨hz, h, hm₃, k₃, hm₄, k₄⟩

/-- `main`'s hypotheses, after the checks of `e` and `n`. -/
theorem CkAfterInv.mainPre {s t₁ t₂ t₃ t₄ : State} (c : CkArgs s) (h : CkAfterInv s t₁ t₂ t₃ t₄)
    (hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (keyE s)) = true)
    (hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (keyN s)) (s.gpr .rsi).toNat = true) :
    MainPre t₄ (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) (s.gpr .r8)
      (s.gpr .r8) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6) (keyN s)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r9).toNat) (Spec.Rsa.os2ip (keyE s)) := by
  have in₄ := h.inScr c
  have kk := h.keep
  have src : ∀ {p : Addr} {bs : List Byte}, Src s (stackArg s 8) ((stackArg s 9).toNat * 8) p bs →
      Src t₄ (stackArg s 8) ((stackArg s 9).toNat * 8) p bs := fun h => h.congrK in₄ kk
  have hlt : Spec.Rsa.os2ip (keyE s) < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv; exact hv.2
  have := c.pl1
  have := c.pl2
  have := c.ql1
  have := c.ql2
  have h₁ := h.e.h₁
  exact
    { scr := h.scr c
      rdi := h.rdi
      zk := c.hZ
      k1 := c.k1
      k2 := c.k2
      nl := bytesAt_length _ _ _
      dl1 := by rw [bytesAt_length]; omega
      dl2 := by rw [bytesAt_length]; omega
      pl1 := by rw [bytesAt_length]; omega
      pl2 := by rw [bytesAt_length]; omega
      ql1 := by rw [bytesAt_length]; omega
      ql2 := by rw [bytesAt_length]; omega
      dpl := by rw [bytesAt_length, bytesAt_length]
      qil := by rw [bytesAt_length, bytesAt_length]
      dql := by rw [bytesAt_length, bytesAt_length]
      hK := by rw [h.hw (i := sK) (by decide) (by decide), h₁.hK, ofNat_toNat64]
      hN := by rw [h.hw (i := sN) (by decide) (by decide), h₁.hN]
      hD := by rw [h.hw (i := sD) (by decide) (by decide), h₁.hD]
      hDl := by rw [h.hw (i := sDlen) (by decide) (by decide), h₁.hDl, bytesAt_length, ofNat_toNat64]
      hP := by rw [h.hw (i := sP) (by decide) (by decide), h₁.hP]
      hPl := by rw [h.hw (i := sPlen) (by decide) (by decide), h₁.hPl, bytesAt_length, ofNat_toNat64]
      hQ := by rw [h.hw (i := sQ) (by decide) (by decide), h₁.hQ]
      hQl := by rw [h.hw (i := sQlen) (by decide) (by decide), h₁.hQl, bytesAt_length, ofNat_toNat64]
      hDP := by rw [h.hw (i := sDP) (by decide) (by decide), h₁.hDP]
      hDQ := by rw [h.hw (i := sDQ) (by decide) (by decide), h₁.hDQ]
      hQI := by rw [h.hw (i := sQI) (by decide) (by decide), h₁.hQI]
      hEv := by
          rw [h.m₄, h.m₃, word_writeW_self, h.e.r11, sat_of_valid hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      srN := src c.nb
      srD := src c.pb
      srP := src c.pb
      srQ := src c.qb
      srDP := src c.dpb
      srDQ := src c.dqb
      srQI := src c.qib
      mv := hm }

/-- `vg_rsa_check_crt_key`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem ckCode_correct (hmx : Impl.Rsa.X86_64.CheckCrtKey.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : ckContract.pre s) :
    ∃ t s', Exec isa Impl.Rsa.X86_64.CheckCrtKey.code s t s' ∧ abiPreserved s s' ∧ ckContract.post s s' := by
  have c := ckArgs_of h
  clear h
  suffices hwp : WP isa Impl.Rsa.X86_64.CheckCrtKey.code s fun s' => gprPreserved s s' ∧ ckContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  have hZ := c.hZ
  have hn := c.hs.nowrap
  have := c.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 8) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  unfold Impl.Rsa.X86_64.CheckCrtKey.code
  refine WP.seq (WP.mono (ckEntry_ok rfl hw c.ha c.hsep) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (expCk_ok c h₁) fun t₂ ⟨hz₂, hm₂, h11₂, k₂⟩ => ?_)
  have e : CkAfterExp s t₁ t₂ := ⟨h₁, hm₂, h11₂, k₂⟩
  have in₁ : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t₁.mem :=
    InScr.of_outside h₁.out (by omega)
  refine WP.ite (!Spec.Rsa.exponentValid (Spec.Rsa.os2ip (keyE s))) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (keyE s)) = false := by simpa using hb
    refine WP.mono (failK_ok (e.scr c) e.rdi (by omega)) fun t ⟨hax, hsv, hm, k⟩ =>
      ckFin c h₁ hax (fun i hi => (hsv i hi).trans (by rw [hm₂])) ((k.gpr (by decide)).trans
        ((h₁.keep.trans k₂).gpr (by decide))) (by rw [hm, hm₂]; exact in₁) ?_
    simp only [ckOf, Spec.Rsa.checkCrtKey, Spec.Rsa.crtKeyValid, hv, Bool.and_false, Bool.false_and]
  · have hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (keyE s)) = true := by simpa using hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (storesCk_ok c e) fun t₃ ⟨hdx₃, hcx₃, hm₃, k₃⟩ => ?_
    refine WP.mono (invalidCk_ok c e hdx₃ hcx₃ hm₃ k₃) fun t₄ ⟨hz₄, h₄⟩ => ?_
    have rsp₄ : t₄.gpr .rsp = s.gpr .rsp := h₄.keep.gpr (by decide)
    refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (keyN s)) (s.gpr .rsi).toNat) (by simp [eval, hz₄])
      (fun hb => ?_) (fun hb => ?_)
    · have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (keyN s)) (s.gpr .rsi).toNat = false := by simpa using hb
      refine WP.mono (failK_ok (h₄.scr c) h₄.rdi (by omega)) fun t ⟨hax, hsv, hmt, k⟩ =>
        ckFin c h₁ hax (fun i hi => (hsv i hi).trans (h₄.saved i hi)) ((k.gpr (by decide)).trans rsp₄)
          (by rw [hmt]; exact h₄.inScr c) ?_
      simp only [ckOf, Spec.Rsa.checkCrtKey, Spec.Rsa.crtKeyValid, bytesAt_length, hm, Bool.false_and]
    · have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (keyN s)) (s.gpr .rsi).toNat = true := by simpa using hb
      refine WP.mono (crtMain_ok (h₄.mainPre c hv hm) hv) fun t ⟨hax, hsv, hin, _, _, kk⟩ =>
        ckFin c h₁ hax (fun i hi => (hsv i hi).trans (h₄.saved i hi)) ((kk.gpr (by decide)).trans rsp₄)
          ((h₄.inScr c).trans hin) ?_
      simp only [ckOf, Spec.Rsa.checkCrtKey, bytesAt_length]

end VG.Proof.Rsa.X86_64.Key
