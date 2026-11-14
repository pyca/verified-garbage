module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecMac
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncPre
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall

/-! ### `RsaPkcs1Enc.X86_64.DecArgs`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the calls, on their own

The arguments of each call of SHA-256's and HMAC's functions, from `Ctx` and
the registers (`initArgsOf`, `updArgsOf`, …), and what each call keeps:
`Ctx` and the frame (`init_cx`, `upd_cx`, …). The proof of constant time
relates two runs call by call with these.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

/-- Data the streaming `update` may read: in the regions the function may
access, apart from HMAC's states and working space and the stack its calls use. -/
structure DataOk (s : State) (da : Addr) (L : Nat) : Prop where
  cov : Covers [⟨da, L⟩] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr))
  dis : ∀ a n, a + n ≤ sMsg → Region.Disjoint ⟨da, L⟩ ⟨scA s a, n⟩
  stk : (below (fb s) 24).Disjoint ⟨da, L⟩
  len : L ≤ 2 ^ 64

/-- Data in `scratch` from `sMsg` on. -/
theorem DataOk.scr {s : State} (hp : DPre s) {a L : Nat} (h1 : sMsg ≤ a) (h2 : a + L ≤ scrBytes) :
    DataOk s (scA s a) L := by
  obtain ⟨hS1, _⟩ := scr_len hp
  refine ⟨Covers.of_sub fun r hr => ⟨scrR s, List.mem_append_right _ (by rw [hp.hwr]; simp [scrR]), a,
      by rw [List.mem_singleton.mp hr]; rfl, by rw [List.mem_singleton.mp hr]; dsimp only [scrR]; omega_using [h2, hS1]⟩,
    fun b n hb => scD (.inr (by omega_using [h1, hb])) h2 (by unfold sMsg scrBytes at *; omega_using [hb]), stkD hp (by decide) h2,
    by unfold scrBytes at h2; omega_using [h2]⟩

/-- The ciphertext. -/
theorem DataOk.c {s : State} (hp : DPre s) : DataOk s (stackArg s 3) (kOf s) := by
  obtain ⟨hS1, _⟩ := scr_len hp
  have hl := hp.hil
  have hk2 := hp.k2
  have hC : (⟨stackArg s 3, kOf s⟩ : Region) = ⟨stackArg s 3, (stackArg s 4).toNat⟩ := by rw [hl]
  refine ⟨Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hC]; exact hp.hrd _ (by simp)),
    fun a n han => ?_, by rw [hC]; exact hp.dKi.sub_left (below_sub s (by decide)), by unfold kOf; omega_using []⟩
  rw [hC]
  exact hp.dis.sub_right (sub_trans (scSub (by unfold sMsg at han; unfold scrBytes; omega_using [han])) (Region.sub_prefix hS1))

theorem updArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {da : Addr} {L : Nat} (hd : DataOk s da L) (hdi : t.gpr .rdi = scA s 0) (hdx : t.gpr .rdx = da)
    (hcx : (t.gpr .rcx).toNat = L) (h8 : t.gpr .r8 = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs (OK v).stream t (scA s 0) da (scA s sWork) L := by
  obtain ⟨-, -, -, -, hSs, -, -, -⟩ := sizes v
  exact
    { rdi := hdi, rdx := hdx, rcx := hcx, r8 := h8
      cd := by rw [hc.rd, hc.wr]; exact hd.cov
      cw := by rw [hSs]; exact Covers.pair (scCov hp hc (by decide)) (scCov hp hc (wbScr v))
      st_sc := by rw [hSs]; exact scD (.inl (by decide)) (by decide) (wbScr v)
      d_st := by rw [hSs]; exact hd.dis 0 96 (by decide)
      d_sc := by exact hd.dis sWork _ (wbFit v)
      stk_st := by rw [below_rsp hc, hSs]; exact stkD hp (by decide) (by decide)
      stk_d := by rw [below_rsp hc]; exact hd.stk.sub_left (VG.X86_64.below_sub (by decide) (by decide))
      stk_sc := by rw [below_rsp hc]; exact stkD hp (by decide) (wbScr v) }

theorem finArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    (hdi : t.gpr .rdi = scA s 0) (hdx : t.gpr .rdx = scA s sDH) (hcx : t.gpr .rcx = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Calls.FinArgs (OK v).stream t (scA s 0) (scA s sDH) (scA s sWork) := by
  obtain ⟨-, -, -, -, hS, hF, -, -⟩ := sizes v
  have cw : Covers [⟨scA s 0, 96⟩, ⟨scA s sDH, 32⟩, ⟨scA s sWork, (OK v).stream.Wb⟩] t.wr :=
    (scCov hp hc (by decide)).cons ((scCov hp hc (by decide)).cons ((scCov hp hc (wbScr v)).cons Covers.nil))
  exact
    { rdi := hdi, rdx := hdx, rcx := hcx
      cw := by rw [hS, hF]; exact cw
      st_o := by rw [hS, hF]; exact scD (.inl (by decide)) (by decide) (by decide)
      st_sc := by rw [hS]; exact scD (.inl (by decide)) (by decide) (wbScr v)
      o_sc := by rw [hF]; exact scD (.inr (wbBelow v (by decide))) (by decide) (wbScr v)
      stk_st := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc, hF]; exact stkD hp (by decide) (by decide)
      stk_sc := by rw [below_rsp hc]; exact stkD hp (by decide) (wbScr v) }

theorem hinitArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes) (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = scA s kOff) (hcx : t.gpr .rcx = BitVec.ofNat 64 32)
    (h8 : t.gpr .r8 = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := HH v) t (scA s 0) (scA s sOuter) (scA s kOff) (scA s sWork) 32 := by
  obtain ⟨hS, -, -, hB, -, -, -, -⟩ := sizes v
  have cw : Covers [⟨scA s 0, 96⟩, ⟨scA s sOuter, 96⟩, ⟨scA s sWork, 8 * (HH v).W⟩] t.wr :=
    (scCov hp hc (by decide)).cons ((scCov hp hc (by decide)).cons ((scCov hp hc (wScr v)).cons Covers.nil))
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := by rw [hcx]; rfl, r8 := h8, klB := by rw [hB]; decide
      cr := Covers.right (scCov hp hc hk2)
      cw := by rw [hS]; exact cw
      i_o := by rw [hS]; exact scD (.inl (by decide)) (by decide) (by decide)
      i_s := by rw [hS]; exact scD (.inl (by decide)) (by decide) (wScr v)
      o_s := by rw [hS]; exact scD (.inl (by decide)) (by decide) (wScr v)
      k_i := by rw [hS]; exact scD (.inr (by unfold sMsg at hk1; omega_using [hk1])) hk2 (by decide)
      k_o := by rw [hS]; exact scD (.inr (by unfold sMsg sOuter at *; omega_using [hk1])) hk2 (by decide)
      k_s := by exact scD (.inr (wBelow v hk1)) hk2 (wScr v)
      stk_i := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_k := by rw [below_rsp hc]; exact stkD hp (by decide) hk2
      stk_s := by rw [below_rsp hc]; exact stkD hp (by decide) (wScr v)
      scnw := by
        have hw := (sizes v).2.1; obtain ⟨h1, h2⟩ := scr_len hp
        simp only [scA, off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold scrBytes at h1; unfold sWork; omega_using [hw, h1, h2] }

theorem hfinArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {dOff : Nat} (hd1 : sMsg ≤ dOff) (hd2 : dOff + 32 ≤ scrBytes) {cnt : Addr} (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = cnt) (hcx : t.gpr .rcx = scA s dOff)
    (h8 : t.gpr .r8 = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := HH v) t (scA s 0) (scA s sOuter) cnt (scA s dOff) (scA s sWork) := by
  obtain ⟨hS, -, hD, -, -, -, -, -⟩ := sizes v
  have cw : Covers [⟨scA s 0, 96⟩, ⟨scA s dOff, 32⟩, ⟨scA s sWork, 8 * (HH v).W⟩] t.wr :=
    (scCov hp hc (by decide)).cons ((scCov hp hc hd2).cons ((scCov hp hc (wScr v)).cons Covers.nil))
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := hcx, r8 := h8
      cr := by rw [hS]; exact Covers.right (scCov hp hc (by decide))
      cw := by rw [hS, hD]; exact cw
      i_u := by rw [hS]; exact scD (.inl (by decide)) (by decide) (by decide)
      i_o := by rw [hS, hD]; exact scD (.inl (by unfold sMsg at hd1; omega_using [hd1])) (by decide) hd2
      i_s := by rw [hS]; exact scD (.inl (by decide)) (by decide) (wScr v)
      u_o := by rw [hS, hD]; exact scD (.inl (by unfold sMsg sOuter at *; omega_using [hd1])) (by decide) hd2
      u_s := by rw [hS]; exact scD (.inl (by decide)) (by decide) (wScr v)
      o_s := by rw [hD]; exact scD (.inr (wBelow v hd1)) hd2 (wScr v)
      stk_i := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_u := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc, hD]; exact stkD hp (by decide) hd2
      stk_s := by rw [below_rsp hc]; exact stkD hp (by decide) (wScr v)
      scnw := by
        have hw := (sizes v).2.1; obtain ⟨h1, h2⟩ := scr_len hp
        simp only [scA, off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold scrBytes at h1; unfold sWork; omega_using [hw, h1, h2] }


/-! ## What each call keeps -/

/-- Regions of `scratch` below `sMsg` or at `d`. -/
theorem scrW {s : State} {lo : List (Nat × Nat)} {a k : Nat} (h : a + k ≤ scrBytes)
    (h' : a + k ≤ sMsg ∨ (a, k) ∈ lo) :
    ∃ a' k', (⟨scA s a, k⟩ : Region) = ⟨scA s a', k'⟩ ∧ a' + k' ≤ scrBytes ∧ (a' + k' ≤ sMsg ∨ (a', k') ∈ lo) :=
  ⟨a, k, rfl, h, h'⟩

/-- A call whose writes are in `scratch` and below the frame. -/
theorem cx_of {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    {ws : List Region} {lo : List (Nat × Nat)} {n : Nat} (hn : n ≤ 8 + privStack) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame (ws ++ [below (fb s) n]) t.mem t'.mem)
    (hw : ∀ r ∈ ws, ∃ a k, r = ⟨scA s a, k⟩ ∧ a + k ≤ scrBytes ∧ (a + k ≤ sMsg ∨ (a, k) ∈ lo)) :
    Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem :=
  ⟨hc.step hp hrd hwr hcs hf fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, k, rfl, hk, -⟩ := hw r hr; exact scS hk
      · rw [List.mem_singleton.mp hr]; exact belowS hp hn,
    frmKeep_of_frame hp hn hf hw⟩

theorem init_cx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    (hdi : t.gpr .rdi = scA s 0) :
    WP isa (.call (HH v).initN (HH v).initC) t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  obtain ⟨-, -, -, -, hS, -, -, -⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Calls.init_call (OK v).stream hdi (by rw [hS]; exact scCov hp hc (by decide))
    (by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)) fun t' a _ => ?_
  have hf := a.frame
  rw [below_rsp hc, hS] at hf
  exact cx_of (lo := []) hp hc (by decide) a.rd a.wr a.cs hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact scrW (by decide) (.inl (by decide))

theorem upd_cx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {da : Addr} {L : Nat} (hd : DataOk s da L) (hdi : t.gpr .rdi = scA s 0) (hdx : t.gpr .rdx = da)
    (hcx : (t.gpr .rcx).toNat = L) (h8 : t.gpr .r8 = scA s sWork) :
    WP isa (.call (HH v).updN (HH v).updC) t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  obtain ⟨-, -, -, -, hS, -, -, -⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Calls.upd_call (OK v).stream (updArgsOf hp hc hd hdi hdx hcx h8) hd.len
    fun t' a _ => ?_
  have hf := a.frame
  rw [below_rsp hc, hS] at hf
  exact cx_of (lo := []) hp hc (by decide) a.rd a.wr a.cs hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW (wbScr v) (.inl (wbFit v))

theorem hinit_cx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes) (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = scA s kOff) (hcx : t.gpr .rcx = BitVec.ofNat 64 32)
    (h8 : t.gpr .r8 = scA s sWork) :
    WP isa (.call (HH v).hmacInitN (HH v).hmacInit) t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  obtain ⟨hS, -, -, -, -, -, -, -⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call (OK v) (hI v) (hIsp v) (hId v)
    (hinitArgsOf hp hc hk1 hk2 hdi hsi hdx hcx h8) fun t' hrd hwr hcs hf _ _ => ?_
  rw [below_rsp hc, hS] at hf
  exact cx_of (lo := []) hp hc (by decide) hrd hwr hcs hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW (wScr v) (.inl (wFit v))

theorem hfin_cx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {dOff : Nat} (hd1 : sMsg ≤ dOff) (hd2 : dOff + 32 ≤ scrBytes) {cnt : Addr} (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = cnt) (hcx : t.gpr .rcx = scA s dOff)
    (h8 : t.gpr .r8 = scA s sWork) :
    WP isa (.call (HH v).hmacFinN (HH v).hmacFin) t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  obtain ⟨hS, -, hD, -, -, -, -, -⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call (OK v) (hF v) (hFsp v) (hFd v)
    (hfinArgsOf hp hc hd1 hd2 hdi hsi hdx hcx h8) fun t' hrd hwr hcs hf _ => ?_
  rw [below_rsp hc, hS, hD] at hf
  exact cx_of (lo := [(dOff, 32)]) hp hc (by decide) hrd hwr hcs hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW hd2 (.inr (List.mem_singleton_self _))
    · exact scrW (wScr v) (.inl (wFit v))

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: two runs

Two runs from entry states that agree on the public data (`decK.pub`: the
pointers and lengths, `n` and `e`) are related piece by piece: each point of
the code is described, in each run, by what correctness says of it from that
run's entry state, which agrees with an anchor `a` on the public data
(`At`). The registers a piece's addresses and branches depend on are
functions of the public data (`pins`); each call's public arguments are too
(`init_two`, `upd_two`, …).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data,
and related to it by `X` (`vg_rsa_pkcs1_decrypt_precomputed`'s further
public data, `DecPCT.lean`). -/
def Sib (X : State → State → Prop) (a s : State) : Prop := (DPre s ∧ decK.pub a s) ∧ X a s

theorem pub_refl (s : State) : decK.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

variable {X : State → State → Prop}

theorem Sib.gpr {a s : State} (h : Sib X a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.1.2.1 r hr).symm

theorem Sib.arg {a s : State} (h : Sib X a s) {i : Nat} (hi : i < 17) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.1.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.n {a s : State} (h : Sib X a s) : nB s = nB a := h.1.2.2.2.1.symm

theorem Sib.e {a s : State} (h : Sib X a s) : eB s = eB a := h.1.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib X a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem Sib.scr {a s : State} (h : Sib X a s) : Dec.sc s = Dec.sc a := h.arg (by decide)

theorem Sib.scr' {a s : State} (h : Sib X a s) (d : Nat) : Dec.scA s d = Dec.scA a d := by
  show off (Dec.sc s) d = off (Dec.sc a) d; rw [h.scr]

theorem Sib.k {a s : State} (h : Sib X a s) : kOf s = kOf a := by
  show (s.gpr .r8).toNat = _; rw [h.gpr (r := .r8) (by decide)]

theorem Sib.p {a s : State} (h : Sib X a s) : DPre s := h.1.1

/-- A point of a run, described by `J` from the run's entry state. -/
def At (X J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib X a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib X a s → f s = f a) {a t₁ t₂ : State} (h₁ : At X J a t₁) (h₂ : At X J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- Registers `J` gives as functions of the public data, at once. -/
theorem pins {J : State → State → Prop} (rs : List (Reg × (State → BitVec 64)))
    (hf : ∀ p ∈ rs, ∀ s t, J s t → t.gpr p.1 = p.2 s) (hs : ∀ p ∈ rs, ∀ a s, Sib X a s → p.2 s = p.2 a) :
    Pins (At X J) (rs.map (·.1)) := fun a t₁ t₂ h₁ h₂ r hr => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact pin p.2 (hf p hp) (hs p hp) h₁ h₂

theorem fb_pin : ∀ a s, Sib X a s → fb s = fb a := fun _ _ h => h.fb
theorem sc_pin : ∀ a s, Sib X a s → sc s = sc a := fun _ _ h => h.scr
theorem scA_pin (d : Nat) : ∀ a s, Sib X a s → scA s d = scA a d := fun _ _ h => h.scr' d
theorem const_pin (v : BitVec 64) : ∀ a s, Sib X a s → (fun _ : State => v) s = (fun _ : State => v) a :=
  fun _ _ _ => rfl
theorem gpr_pin {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    ∀ a s, Sib X a s → s.gpr r = a.gpr r := fun _ _ h => h.gpr hr
theorem arg_pin {i : Nat} (hi : i < 17) : ∀ a s, Sib X a s → stackArg s i = stackArg a i := fun _ _ h => h.arg hi

/-- `Ctx` for some result and `EM`. -/
def Cx (s t : State) : Prop := ∃ R EM, Ctx s R EM t

theorem Cx.rsp {s t : State} (h : Cx s t) : t.gpr .rsp = fb s := let ⟨_, _, hc⟩ := h; hc.rsp

/-- `rsp` in a state with `Cx`. -/
theorem rsp_pin {J : State → State → Prop} (hJ : ∀ s t, J s t → Cx s t) : Pins (At X J) [.rsp] :=
  pins (J := J) [(.rsp, fb)] (by simp only [List.mem_singleton]; rintro p rfl s t h; exact (hJ s t h).rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)

/-! ## The calls -/

variable {v : Compress}


/-- The registers a callee sees, but `rsp`. -/
theorem ce_eq {t₁ t₂ : State} {r : Reg} (hr : r ≠ .rsp) (h : t₁.gpr r = t₂.gpr r) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_gpr _ hr, State.callEntry_gpr _ hr, h]

theorem ce_rsp {t₁ t₂ : State} (h : t₁.gpr .rsp = t₂.gpr .rsp) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr .rsp = (t₂.callEntry.withRegions rd₂ wr₂).gpr .rsp := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, h]

/-- Two runs at a call, each with `Ctx`, the same `rsp` and its arguments. -/
theorem two_ctx {J : State → State → Prop} (hJ : ∀ s t, J s t → Cx s t) {a t₁ t₂ : State} (h₁ : At X J a t₁)
    (h₂ : At X J a t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  rsp_pin hJ a t₁ t₂ h₁ h₂ .rsp (List.mem_singleton_self _)

theorem init_two {J : State → State → Prop} (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0) :
    RelCT isa (Two (At X J)) (.call (HH v).initN (HH v).initC) fun _ _ => True := by
  obtain ⟨-, -, -, -, hS, -, -, -⟩ := sizes v
  refine RelCT.callEx (OK v).stream.init.1 (OK v).stream.init.2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂⟩ := hJ _ _ j₂
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Ctx s R EM t → t.gpr .rdi = scA s 0 →
      (VG.Proof.Pbkdf2.Md.X86_64.Calls.initK (HH v).stream.S (OK v).stream.SH.Repr).pre (t.callEntry.withRegions [] [⟨scA s 0, (HH v).stream.S⟩]) :=
    fun {s t R EM} hp hc hd => by
      refine ⟨rfl, by simp [State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hd], ?_⟩
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hd]
      rw [hS]
      exact (by rw [below_rsp hc]; exact stkD hp (by decide) (by decide) :
        (below (t.gpr .rsp) 16).Disjoint ⟨scA s 0, 96⟩).sub_left (Proof.Pbkdf2.Md.X86_64.Calls.ret_sub t)
  have cv : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Ctx s R EM t →
      Covers [⟨scA s 0, (HH v).stream.S⟩] t.wr := fun hp hc => by rw [hS]; exact scCov hp hc (by decide)
  refine ⟨_, _, _, _, pre S₁.p c₁ d₁, pre S₂.p c₂ d₂, ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr (cv S₁.p c₁), cv S₁.p c₁, VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr (cv S₂.p c₂), cv S₂.p c₂, sp⟩


theorem upd_two {J : State → State → Prop} {da : State → Addr} {L : State → Nat} {si : State → BitVec 64}
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = si s ∧ t.gpr .rdx = da s ∧
      (t.gpr .rcx).toNat = L s ∧ t.gpr .r8 = scA s sWork)
    (hd : ∀ s, DPre s → DataOk s (da s) (L s)) (hda : ∀ a s, Sib X a s → da s = da a)
    (hL : ∀ a s, Sib X a s → L s = L a) (hsi : ∀ a s, Sib X a s → si s = si a) :
    RelCT isa (Two (At X J)) (.call (HH v).updN (HH v).updC) fun _ _ => True := by
  refine RelCT.callEx (OK v).stream.upd.1 (OK v).stream.upd.2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁, r₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂, r₂⟩ := hJ _ _ j₂
  have A₁ := updArgsOf (v := v) S₁.p c₁ (hd _ S₁.p) d₁ x₁ k₁ r₁
  have A₂ := updArgsOf (v := v) S₂.p c₂ (hd _ S₂.p) d₂ x₂ k₂ r₂
  refine ⟨_, _, _, _, A₁.pre (OK v).stream, A₂.pre (OK v).stream, ?_, A₁.covers (OK v).stream, A₁.cw,
    A₂.covers (OK v).stream, A₂.cw, sp⟩
  have cx : t₁.gpr .rcx = t₂.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [k₁, k₂, hL _ _ S₁, hL _ _ S₂])
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, hsi _ _ S₁, hsi _ _ S₂]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, hda _ _ S₁, hda _ _ S₂]) _ _ _ _, ce_eq (by decide) cx _ _ _ _,
    ce_eq (by decide) (by rw [r₁, r₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩

theorem fin_two {J : State → State → Prop}
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = s.gpr .r8 ∧ t.gpr .rdx = scA s sDH ∧
      t.gpr .rcx = scA s sWork) :
    RelCT isa (Two (At X J)) (.call (HH v).finN (HH v).finC) fun _ _ => True := by
  refine RelCT.callEx (OK v).stream.fin.1 (OK v).stream.fin.2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂⟩ := hJ _ _ j₂
  have A₁ := finArgsOf (v := v) S₁.p c₁ d₁ x₁ k₁
  have A₂ := finArgsOf (v := v) S₂.p c₂ d₂ x₂ k₂
  refine ⟨_, _, _, _, A₁.pre (OK v).stream, A₂.pre (OK v).stream, ?_,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr A₁.cw, A₁.cw, VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr A₂.cw, A₂.cw,
    sp⟩
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, S₁.gpr (r := .r8) (by decide), S₂.gpr (r := .r8) (by decide)]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, S₁.scr' sDH, S₂.scr' sDH]) _ _ _ _,
    ce_eq (by decide) (by rw [k₁, k₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩

theorem hinit_two {J : State → State → Prop} {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes)
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = scA s sOuter ∧ t.gpr .rdx = scA s kOff ∧
      t.gpr .rcx = BitVec.ofNat 64 32 ∧ t.gpr .r8 = scA s sWork) :
    RelCT isa (Two (At X J)) (.call (HH v).hmacInitN (HH v).hmacInit) fun _ _ => True := by
  refine RelCT.callEx (hI v).1 (hI v).2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁, r₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂, r₂⟩ := hJ _ _ j₂
  have A₁ := hinitArgsOf (v := v) S₁.p c₁ hk1 hk2 d₁ i₁ x₁ k₁ r₁
  have A₂ := hinitArgsOf (v := v) S₂.p c₂ hk1 hk2 d₂ i₂ x₂ k₂ r₂
  refine ⟨_, _, _, _, A₁.pre (OK v), A₂.pre (OK v), ?_,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw, sp⟩
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, S₁.scr' sOuter, S₂.scr' sOuter]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, S₁.scr' kOff, S₂.scr' kOff]) _ _ _ _,
    ce_eq (by decide) (by rw [k₁, k₂]) _ _ _ _,
    ce_eq (by decide) (by rw [r₁, r₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩

theorem hfin_two {J : State → State → Prop} {dOff : State → Nat} {cnt : State → Addr}
    (hd1 : ∀ s, sMsg ≤ dOff s) (hd2 : ∀ s, dOff s + 32 ≤ scrBytes)
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = scA s sOuter ∧ t.gpr .rdx = cnt s ∧
      t.gpr .rcx = scA s (dOff s) ∧ t.gpr .r8 = scA s sWork)
    (hdO : ∀ a s, Sib X a s → dOff s = dOff a) (hcnt : ∀ a s, Sib X a s → cnt s = cnt a) :
    RelCT isa (Two (At X J)) (.call (HH v).hmacFinN (HH v).hmacFin) fun _ _ => True := by
  refine RelCT.callEx (hF v).1 (hF v).2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁, r₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂, r₂⟩ := hJ _ _ j₂
  have A₁ := hfinArgsOf (v := v) S₁.p c₁ (hd1 s₁) (hd2 s₁) d₁ i₁ x₁ k₁ r₁
  have A₂ := hfinArgsOf (v := v) S₂.p c₂ (hd1 s₂) (hd2 s₂) d₂ i₂ x₂ k₂ r₂
  refine ⟨_, _, _, _, A₁.pre (OK v), A₂.pre (OK v), ?_,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw, sp⟩
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, S₁.scr' sOuter, S₂.scr' sOuter]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, hcnt _ _ S₁, hcnt _ _ S₂]) _ _ _ _,
    ce_eq (by decide) (by rw [k₁, k₂, hdO _ _ S₁, hdO _ _ S₂, S₁.scr', S₂.scr']) _ _ _ _,
    ce_eq (by decide) (by rw [r₁, r₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩


/-! ## Pieces -/

/-- A piece the taint analysis checks from registers `J` fixes, with what
correctness gives after it. -/
theorem two_blk {J J' : State → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins (At X J) rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s t, DPre s → J s t → WP isa c t (J' s)) : RelCT isa (Two (At X J)) c (Two (At X J')) :=
  two_piece rs hpin h fun _ _ ⟨s, S, j⟩ => WP.mono (hw _ _ S.p j) fun _ j' => ⟨s, S, j'⟩

/-- A piece related in two runs, with what correctness gives after it. -/
theorem two_then {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (At X J)) c fun _ _ => True)
    (hw : ∀ s t, DPre s → J s t → WP isa c t (J' s)) : RelCT isa (Two (At X J)) c (Two (At X J')) :=
  two_post hct fun _ _ ⟨s, S, j⟩ => WP.mono (hw _ _ S.p j) fun _ j' => ⟨s, S, j'⟩

/-- Weakening what is known. -/
theorem two_weak {J J' : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ s t, J s t → J' s t) (hct : RelCT isa (Two (At X J')) c Q) : RelCT isa (Two (At X J)) c Q :=
  hct.mono (fun _ _ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ⟨a, ⟨s₁, S₁, h _ _ j₁⟩, ⟨s₂, S₂, h _ _ j₂⟩⟩) fun _ _ q => q

/-- Relations that are unions. -/
theorem relCT_union {β : Type} {P : β → State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ b, RelCT isa (P b) c Q) : RelCT isa (fun s₁ s₂ => ∃ b, P b s₁ s₂) c Q :=
  fun _ _ _ _ _ _ ⟨b, hp⟩ e₁ e₂ => h b _ _ _ _ _ _ hp e₁ e₂

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
