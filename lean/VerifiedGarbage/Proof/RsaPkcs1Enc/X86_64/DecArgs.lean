import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the calls, on their own

The arguments of each call of SHA-256's and HMAC's functions, from `Ctx` and
the registers (`initArgsOf`, `updArgsOf`, …), and what each call keeps:
`Ctx` and the frame (`init_cx`, `upd_cx`, …). The proof of constant time
relates two runs call by call with these.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
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
      by rw [List.mem_singleton.mp hr]; rfl, by rw [List.mem_singleton.mp hr]; dsimp only [scrR]; omega⟩,
    fun b n hb => scD (.inr (by omega)) h2 (by unfold sMsg scrBytes at *; omega), stkD hp (by decide) h2,
    by unfold scrBytes at h2; omega⟩

/-- The ciphertext. -/
theorem DataOk.c {s : State} (hp : DPre s) : DataOk s (stackArg s 3) (kOf s) := by
  obtain ⟨hS1, _⟩ := scr_len hp
  have hl := hp.hil
  have hk2 := hp.k2
  have hC : (⟨stackArg s 3, kOf s⟩ : Region) = ⟨stackArg s 3, (stackArg s 4).toNat⟩ := by rw [hl]
  refine ⟨Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hC, hp.hrd]; simp),
    fun a n han => ?_, by rw [hC]; exact hp.dKi.sub_left (below_sub s (by decide)), by unfold kOf; omega⟩
  rw [hC]
  exact hp.dis.sub_right (sub_trans (scSub (by unfold sMsg at han; unfold scrBytes; omega)) (Region.sub_prefix hS1))

theorem updArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {da : Addr} {L : Nat} (hd : DataOk s da L) (hdi : t.gpr .rdi = scA s 0) (hdx : t.gpr .rdx = da)
    (hcx : (t.gpr .rcx).toNat = L) (h8 : t.gpr .r8 = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs (OK v).stream t (scA s 0) da (scA s sWork) L := by
  obtain ⟨-, -, -, -, hSs, -, -, hWb⟩ := sizes v
  exact
    { rdi := hdi, rdx := hdx, rcx := hcx, r8 := h8
      cd := by rw [hc.rd, hc.wr]; exact hd.cov
      cw := by rw [hSs, hWb]; exact Covers.pair (scCov hp hc (by decide)) (scCov hp hc (by decide))
      st_sc := by rw [hSs, hWb]; exact scD (.inl (by decide)) (by decide) (by decide)
      d_st := by rw [hSs]; exact hd.dis 0 96 (by decide)
      d_sc := by rw [hWb]; exact hd.dis sWork 608 (by decide)
      stk_st := by rw [below_rsp hc, hSs]; exact stkD hp (by decide) (by decide)
      stk_d := by rw [below_rsp hc]; exact hd.stk.sub_left (VG.X86_64.below_sub (by decide) (by decide))
      stk_sc := by rw [below_rsp hc, hWb]; exact stkD hp (by decide) (by decide) }

theorem finArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    (hdi : t.gpr .rdi = scA s 0) (hdx : t.gpr .rdx = scA s sDH) (hcx : t.gpr .rcx = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Calls.FinArgs (OK v).stream t (scA s 0) (scA s sDH) (scA s sWork) := by
  obtain ⟨-, -, -, -, hS, hF, -, hWb⟩ := sizes v
  have cw : Covers [⟨scA s 0, 96⟩, ⟨scA s sDH, 32⟩, ⟨scA s sWork, 608⟩] t.wr :=
    (scCov hp hc (by decide)).cons ((scCov hp hc (by decide)).cons ((scCov hp hc (by decide)).cons Covers.nil))
  exact
    { rdi := hdi, rdx := hdx, rcx := hcx
      cw := by rw [hS, hF, hWb]; exact cw
      st_o := by rw [hS, hF]; exact scD (.inl (by decide)) (by decide) (by decide)
      st_sc := by rw [hS, hWb]; exact scD (.inl (by decide)) (by decide) (by decide)
      o_sc := by rw [hF, hWb]; exact scD (.inr (by decide)) (by decide) (by decide)
      stk_st := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc, hF]; exact stkD hp (by decide) (by decide)
      stk_sc := by rw [below_rsp hc, hWb]; exact stkD hp (by decide) (by decide) }

theorem hinitArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes) (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = scA s kOff) (hcx : t.gpr .rcx = BitVec.ofNat 64 32)
    (h8 : t.gpr .r8 = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := HH v) t (scA s 0) (scA s sOuter) (scA s kOff) (scA s sWork) 32 := by
  obtain ⟨hS, hW, -, hB, -, -, -, -⟩ := sizes v
  have cw : Covers [⟨scA s 0, 96⟩, ⟨scA s sOuter, 96⟩, ⟨scA s sWork, 832⟩] t.wr :=
    (scCov hp hc (by decide)).cons ((scCov hp hc (by decide)).cons ((scCov hp hc (by decide)).cons Covers.nil))
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := by rw [hcx]; rfl, r8 := h8, klB := by rw [hB]; decide
      cr := Covers.right (scCov hp hc hk2)
      cw := by rw [hS, hW]; exact cw
      i_o := by rw [hS]; exact scD (.inl (by decide)) (by decide) (by decide)
      i_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      o_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      k_i := by rw [hS]; exact scD (.inr (by unfold sMsg at hk1; omega)) hk2 (by decide)
      k_o := by rw [hS]; exact scD (.inr (by unfold sMsg sOuter at *; omega)) hk2 (by decide)
      k_s := by rw [hW]; exact scD (.inr (by unfold sMsg sWork at *; omega)) hk2 (by decide)
      stk_i := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_k := by rw [below_rsp hc]; exact stkD hp (by decide) hk2
      stk_s := by rw [below_rsp hc, hW]; exact stkD hp (by decide) (by decide)
      scnw := by
        rw [hW]; obtain ⟨h1, h2⟩ := scr_len hp
        simp only [scA, off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold scrBytes at h1; unfold sWork; omega }

theorem hfinArgsOf {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {dOff : Nat} (hd1 : sMsg ≤ dOff) (hd2 : dOff + 32 ≤ scrBytes) {cnt : Addr} (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = cnt) (hcx : t.gpr .rcx = scA s dOff)
    (h8 : t.gpr .r8 = scA s sWork) :
    Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := HH v) t (scA s 0) (scA s sOuter) cnt (scA s dOff) (scA s sWork) := by
  obtain ⟨hS, hW, hD, -, -, -, -, -⟩ := sizes v
  have cw : Covers [⟨scA s 0, 96⟩, ⟨scA s dOff, 32⟩, ⟨scA s sWork, 832⟩] t.wr :=
    (scCov hp hc (by decide)).cons ((scCov hp hc hd2).cons ((scCov hp hc (by decide)).cons Covers.nil))
  exact
    { rdi := hdi, rsi := hsi, rdx := hdx, rcx := hcx, r8 := h8
      cr := by rw [hS]; exact Covers.right (scCov hp hc (by decide))
      cw := by rw [hS, hD, hW]; exact cw
      i_u := by rw [hS]; exact scD (.inl (by decide)) (by decide) (by decide)
      i_o := by rw [hS, hD]; exact scD (.inl (by unfold sMsg at hd1; omega)) (by decide) hd2
      i_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      u_o := by rw [hS, hD]; exact scD (.inl (by unfold sMsg sOuter at *; omega)) (by decide) hd2
      u_s := by rw [hS, hW]; exact scD (.inl (by decide)) (by decide) (by decide)
      o_s := by rw [hD, hW]; exact scD (.inr (by unfold sMsg sWork at *; omega)) hd2 (by decide)
      stk_i := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_u := by rw [below_rsp hc, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc, hD]; exact stkD hp (by decide) hd2
      stk_s := by rw [below_rsp hc, hW]; exact stkD hp (by decide) (by decide)
      scnw := by
        rw [hW]; obtain ⟨h1, h2⟩ := scr_len hp
        simp only [scA, off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold scrBytes at h1; unfold sWork; omega }


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
  obtain ⟨-, -, -, -, hS, -, -, hWb⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Calls.upd_call (OK v).stream (updArgsOf hp hc hd hdi hdx hcx h8) hd.len
    fun t' a _ => ?_
  have hf := a.frame
  rw [below_rsp hc, hS, hWb] at hf
  exact cx_of (lo := []) hp hc (by decide) a.rd a.wr a.cs hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW (by decide) (.inl (by decide))

theorem fin_cx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    (hdi : t.gpr .rdi = scA s 0) (hdx : t.gpr .rdx = scA s sDH) (hcx : t.gpr .rcx = scA s sWork) :
    WP isa (.call (HH v).finN (HH v).finC) t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  obtain ⟨-, -, -, -, hS, hF, -, hWb⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Calls.fin_call (OK v).stream (finArgsOf hp hc hdi hdx hcx) fun t' a _ => ?_
  have hf := a.frame
  rw [below_rsp hc, hS, hF, hWb] at hf
  exact cx_of (lo := [(sDH, 32)]) hp hc (by decide) a.rd a.wr a.cs hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW (by decide) (.inr (List.mem_singleton_self _))
    · exact scrW (by decide) (.inl (by decide))

theorem hinit_cx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes) (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = scA s kOff) (hcx : t.gpr .rcx = BitVec.ofNat 64 32)
    (h8 : t.gpr .r8 = scA s sWork) :
    WP isa (.call (HH v).hmacInitN (HH v).hmacInit) t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  obtain ⟨hS, hW, -, -, -, -, -, -⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call (OK v) (hI v) (hIsp v) (hId v)
    (hinitArgsOf hp hc hk1 hk2 hdi hsi hdx hcx h8) fun t' hrd hwr hcs hf _ _ => ?_
  rw [below_rsp hc, hS, hW] at hf
  exact cx_of (lo := []) hp hc (by decide) hrd hwr hcs hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW (by decide) (.inl (by decide))

theorem hfin_cx {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {dOff : Nat} (hd1 : sMsg ≤ dOff) (hd2 : dOff + 32 ≤ scrBytes) {cnt : Addr} (hdi : t.gpr .rdi = scA s 0)
    (hsi : t.gpr .rsi = scA s sOuter) (hdx : t.gpr .rdx = cnt) (hcx : t.gpr .rcx = scA s dOff)
    (h8 : t.gpr .r8 = scA s sWork) :
    WP isa (.call (HH v).hmacFinN (HH v).hmacFin) t fun t' => Ctx s R EM t' ∧ FrmKeep s t.mem t'.mem := by
  obtain ⟨hS, hW, hD, -, -, -, -, -⟩ := sizes v
  refine Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call (OK v) (hF v) (hFsp v) (hFd v)
    (hfinArgsOf hp hc hd1 hd2 hdi hsi hdx hcx h8) fun t' hrd hwr hcs hf _ => ?_
  rw [below_rsp hc, hS, hD, hW] at hf
  exact cx_of (lo := [(dOff, 32)]) hp hc (by decide) hrd hwr hcs hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scrW (by decide) (.inl (by decide))
    · exact scrW hd2 (.inr (List.mem_singleton_self _))
    · exact scrW (by decide) (.inl (by decide))

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
