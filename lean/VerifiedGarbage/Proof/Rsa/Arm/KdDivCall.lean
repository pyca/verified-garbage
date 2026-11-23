module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyDivCall
public import VerifiedGarbage.Proof.Rsa.Arm.KdDiv
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Rsa.Arm.InverseCall
import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Rsa.Arm.KeyDivCall
meta import VerifiedGarbage.Proof.Rsa.Arm.KdDiv
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Rsa.Arm.InverseCall
meta import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # The key checks' division on ARMv7 with its steps a call (`KeyDiv.divWC`)

`divWCG_ok` is `divWG_ok` for `divWC`, whose steps (`tail`) are a call of
`tailFn`, which keeps the return address in the header word `sT`: the
invariant of the steps (`DivSt`) holds again from the state after that store
(`DivSt.restart`), as it reads no header word but those of the division.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd)

theorem divW_eq_tail {a r m t nm u : Nat} {top qo : Option Nat} :
    divW a r m t nm u top qo = .seq (prep a r m nm top) (VG.Impl.Rsa.Arm.KeyDiv.tail r m t nm u qo) := rfl

/-- The steps, from the invariant at `j ≥ 1`: the loop (`loop_ok`), then the last step (`stepD_ok`). -/
theorem tail_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat} {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) (hj1 : 1 ≤ j) (hr : r < N) (hm : m < N) (ht : t < N)
    (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r)
    (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0)
    (hu0 : u ≠ 0) (hdw : 3 ≤ w / 2) (hq : QArr N r m t nm u qo := by trivial) :
    WP isa (VG.Impl.Rsa.Arm.KeyDiv.tail r m t nm u qo) x fun x' => Ws x' B Z w N ∧ Prepped x' B w m nm z M ∧
      slot x'.mem B sJ = (BitVec.ofNat 32 (4 * 0) - 4).toNat ∧
      val32 x'.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * 0) + 2 ^ (32 * 0) * (X / 2 ^ (32 * 0) % M) ∧
      Keep B w ([r, t, u] ++ qList qo) [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] s0.mem x'.mem ∧
      QV B w X M 0 x'.mem qo ∧ Rest divRegs s0 x' := by
  rw [VG.Impl.Rsa.Arm.KeyDiv.tail, WP.seq_iff]
  exact WP.mono (loop_ok I hj1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw hq)
    fun _ I1 => stepD_ok I1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw hq

/-- The invariant again from a state that differs from one where it holds only in the header
word `sT`. -/
theorem DivSt.restart {s0 x y : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat} {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) (hw : Ws y B Z w N) {v : BitVec 32}
    (hy : y.mem = x.mem.writeW (off (State.addr B) VG.Impl.Rsa.Arm.Keys.sT) v)
    (hr : r < N) (hm : m < N) (hnm : nm < N) (hq : QArr N r m t nm u qo) :
    DivSt y y B Z w N r m t nm u z M X j qo := by
  have K : Keep B w [] [VG.Impl.Rsa.Arm.Keys.sT] x.mem y.mem := by
    rw [hy]; exact keep_write _ _ (by decide) (by decide)
  have := I.ws.wle
  have N0 : 0 < N := by omega_using [hr]
  have sl : ∀ e, e + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr → (e + 4 ≤ 112 ∨ 116 ≤ e) →
      slot y.mem B e = slot x.mem B e := fun e he hd => Keep.slot K he (by
        simp only [List.mem_singleton, forall_eq, VG.Impl.Rsa.Arm.Keys.sT]; omega_using [hd])
  have va : ∀ {k L : Nat}, k < N → L ≤ w + 2 →
      val32 y.mem (State.addr B) (arr w k) L = val32 x.mem (State.addr B) (arr w k) L :=
    fun hk hL => VG.Proof.Rsa.Arm.Inv.Keep.nk K hL (by simp) (by decide) (I.ws.fit64 hk)
  have p := I.pre
  refine ⟨hw, ⟨?_, ?_, p.hz, ?_, p.hMP, ?_, ?_, ?_, ?_, ?_⟩, ?_, I.hj, ?_, Keep.refl _ _ _ _ _, ?_,
    Rest.refl _ _⟩
  · rw [sl 16 (by decide) (by decide)]; exact p.c16
  · rw [va hm (by omega_using [])]; exact p.hM
  · rw [sl sP (by decide) (by decide)]; exact p.hP
  · rw [sl sD (by decide) (by decide), sl sD1 (by decide) (by decide)]; exact p.hD
  · rw [sl sD (by decide) (by decide)]; exact p.hDn
  · rw [sl sV (by decide) (by decide), sl sD (by decide) (by decide)]; exact p.hV
  · rw [va N0 (by omega_using [])]; exact p.z0
  · rw [va hnm (by omega_using [])]; exact p.hnm
  · rw [sl sJ (by decide) (by decide)]; exact I.J
  · rw [va hr (by omega_using [])]; exact I.val
  · cases qo with
    | none => trivial
    | some q => exact (va hq.1 (by omega_using [])).trans I.quo

/-- Calls change only `r12` and `lr`, both among the division's registers. -/
theorem rest_callEntry_div (s : State) : Rest divRegs s s.callEntry := by
  have hsub : ∀ r ∈ linkRegs, r ∈ divRegs := by decide
  exact ⟨fun r hr => State.callEntry_gpr s fun hl => hr (hsub r hl), rfl, rfl, rfl⟩

/-- A call of `tailFn` from the invariant at `j ≥ 1`: the steps, and `sT` written. -/
theorem tailFn_call_ok {n : String} {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat}
    {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) (hj1 : 1 ≤ j) (hr : r < N) (hm : m < N) (ht : t < N)
    (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r)
    (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0)
    (hu0 : u ≠ 0) (hdw : 3 ≤ w / 2) (hq : QArr N r m t nm u qo := by trivial) :
    WP isa (.call n (tailFn r m t nm u qo)) x fun y => Ws y B Z w N ∧
      val32 y.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * 0) + 2 ^ (32 * 0) * (X / 2 ^ (32 * 0) % M) ∧
      Keep B w ([r, t, u] ++ qList qo)
        [VG.Impl.Rsa.Arm.Keys.sT, sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] x.mem y.mem ∧
      QV B w X M 0 y.mem qo ∧ Rest divRegs x y := by
  have r0 := rest_callEntry_div x
  have hx : Ws x.callEntry B Z w N := I.ws.rest r0
  refine WP.call_lrKept ?_
  rw [tailFn, WP.seq_iff]
  refine wp_strSlot hx (by decide) fun s1 m1 => WP.block_nil_iff.mpr ?_
  have h1 : Ws s1 B Z w N := hx.of_mupd m1
  have K1 : Keep B w [] [VG.Impl.Rsa.Arm.Keys.sT] x.mem s1.mem := by
    rw [m1.mem, State.callEntry_mem]; exact keep_write _ _ (by decide) (by decide)
  have I1 := I.restart h1 (v := x.callEntry.gpr .lr) (by rw [m1.mem, State.callEntry_mem]) hr hm hnm hq
  rw [WP.seq_iff]
  refine WP.mono (tail_ok I1 hj1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw hq)
    fun x2 ⟨W2, _, _, V2, K2, Q2, R2⟩ => ?_
  refine wp_ldrSlot W2 (by decide) fun t3 u3 => WP.block_nil_iff.mpr ?_
  have sl : slot x2.mem B VG.Impl.Rsa.Arm.Keys.sT = slot s1.mem B VG.Impl.Rsa.Arm.Keys.sT :=
    Keep.slot K2 (by decide) (by decide)
  refine ⟨?_, W2.of_upd u3 (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [u3.gpr]
    refine BitVec.eq_of_toNat_eq ?_
    have e := sl
    rw [m1.mem, slot_write_self] at e
    exact e
  · rw [u3.mem]; exact V2
  · rw [u3.mem]
    exact Keep.trans (Keep.mono K1 (by simp) (by decide)) (Keep.mono K2 (fun _ h => h) (by decide))
  · rw [u3.mem]; exact Q2
  · exact r0.trans ((m1.rest _).trans (R2.trans (u3.rest (by decide))))

/-! ## The division -/

theorem divWCG_ok (name : String) {s : State} {B : BitVec 32} {Z w N a r m t nm u : Nat} (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat} (hM : num s.mem B w m = M)
    (hMl : M < 2 ^ (32 * (w / 2))) (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)))
    (hz : num s.mem B w 0 = 0) {top : Option Nat} (htop : TopOk top w (num s.mem B w a))
    {qo : Option Nat} (hq : QArr N r m t nm u qo) (hq0 : QZ s.mem B w qo) :
    WP isa (divWC name a r m t nm u top qo) s fun v => Ws v B Z w N ∧ num v.mem B w r = num s.mem B w a % M ∧
      w32 v.mem (State.addr B) (arr w r + 4 * w) = 0 ∧ Keep B w ([r, t, u, nm] ++ qList qo) (VG.Impl.Rsa.Arm.Keys.sT :: divSlots) s.mem v.mem ∧
      QV B w (num s.mem B w a) M 0 v.mem qo ∧ Rest divRegs s v := by
  have := h.wle
  obtain gm := h.fit64 hm
  obtain g0 := h.fit64 (j := 0) (by omega_using [ha])
  obtain gn := h.fit64 hnm
  simp only [S] at gm g0 gn
  obtain hM0 : 0 < M := by
    rw [← hM]; simp only [num]
    rw [show w = (w / 2 - 1) + 1 + (w - w / 2) by omega_using [hw6], val32_append, val32_succ]
    have := Nat.mul_le_mul_left (2 ^ (32 * (w / 2 - 1))) hT0
    have := Nat.two_pow_pos (32 * (w / 2 - 1))
    obtain e : w / 2 - 1 + 1 + (w - w / 2) = w := by omega_using [hw6]
    rw [e] at *
    omega_arith
  rw [divWC, WP.seq_iff]
  refine WP.mono (prepQ_ok t u h ha hr hm hnm hN hra hmr hnm' hnr hr0 hn0 hw6 h16 hM hMl hT0 hz htop hq hq0)
    fun x0 ⟨⟨z0, I0q⟩, K, R⟩ => ?_
  obtain hj1 := (htop.facts (by simp only [num]; exact val32_lt _ _ _ _) (by omega_using [hw6])).1
  refine WP.mono (tailFn_call_ok I0q hj1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0
    (by omega_using [hw6]) hq) fun x2 ⟨W2, V2, K2, Q2, R2⟩ => ?_
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.div_one, Nat.one_mul, Nat.zero_add] at V2
  rw [val32_succ] at V2
  obtain hlt := val32_lt x2.mem (State.addr B) (arr w r) w
  obtain hXM : num s.mem B w a % M < 2 ^ (32 * w) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hM0) (Nat.le_of_lt (Nat.lt_of_lt_of_le hMl
      (Nat.pow_le_pow_right (by decide) (by omega_using []))))
  generalize 2 ^ (32 * w) = P at hlt hXM V2
  obtain hw0 : w32 x2.mem (State.addr B) (arr w r + 4 * w) = 0 := by
    rcases Nat.eq_zero_or_pos (w32 x2.mem (State.addr B) (arr w r + 4 * w)) with e | e
    · exact e
    · have := Nat.le_mul_of_pos_right P e; omega_using [hXM, V2, this]
  refine ⟨W2, ?_, hw0, ?_, Q2, ?_⟩
  · simp only [num]; rw [hw0, Nat.mul_zero, Nat.add_zero] at V2; exact V2
  · refine (K.mono (js' := [r, t, u, nm] ++ qList qo) (fun j hj => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega_using [hr, ht, hnm, hu, hra, hrt, hru, htu, hmr, hmt, hmu, hnr, htn, hnu, hnm', hr0, ht0, hu0, hn0, hj]))).trans
      (K2.mono (fun j hj => ?_))
    rcases List.mem_append.mp hj with hj | hj
    · exact List.mem_append_left _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega_using [hr, ht, hnm, hu, hra, hrt, hru, htu, hmr, hmt, hmu, hnr, htn, hnu, hnm', hr0, ht0, hu0, hn0, hj])
    · exact List.mem_append_right _ hj
  · exact R.trans R2

theorem divWC_ok (name : String) {s : State} {B : BitVec 32} {Z w N a r m t nm u : Nat} (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat} (hM : num s.mem B w m = M)
    (hMl : M < 2 ^ (32 * (w / 2))) (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)))
    (hz : num s.mem B w 0 = 0) {top : Option Nat} (htop : TopOk top w (num s.mem B w a) := by trivial) :
    WP isa (divWC name a r m t nm u top) s fun v => Ws v B Z w N ∧ num v.mem B w r = num s.mem B w a % M ∧
      w32 v.mem (State.addr B) (arr w r + 4 * w) = 0 ∧ Keep B w [r, t, u, nm] (VG.Impl.Rsa.Arm.Keys.sT :: divSlots) s.mem v.mem ∧
      Rest divRegs s v :=
  WP.mono (divWCG_ok name h ha hr hm ht hnm hu hN hra hrt hru htu hmr hmt hmu hnr htn hnu hnm' hr0 ht0 hu0 hn0 hw6 h16
    hM hMl hT0 hz htop (qo := none) trivial trivial) fun _ ⟨W, V, Z', K, _, R⟩ =>
      ⟨W, V, Z', K.mono (by simp [qList]), R⟩
/-! ## Constant time -/

theorem strT_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8])
    (.block [.str .lr .r8 VG.Impl.Rsa.Arm.Keys.sT]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem ldrT_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8])
    (.block [.ldr .lr .r8 VG.Impl.Rsa.Arm.Keys.sT]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem r8_regs {s t : State} {B : BitVec 32} {Z w N : Nat} (h₁ : Ws s B Z w N) (h₂ : Ws t B Z w N) :
    ∀ r ∈ [Reg.r8], s.gpr r = t.gpr r := by
  simp only [List.mem_singleton, forall_eq]; rw [h₁.r8, h₂.r8]

/-- The invariant in the state a call enters its callee in. -/
theorem DivSt.callEntry {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat} {qo : Option Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j qo) : DivSt s0 x.callEntry B Z w N r m t nm u z M X j qo :=
  ⟨I.ws.rest (rest_callEntry_div x), I.pre.of_mem rfl, I.J, I.hj, I.val, I.keep, I.quo,
    I.rest.trans (rest_callEntry_div x)⟩

/-- `divWC name a r m t nm u top qo` is constant time. -/
theorem divWCG_ct (name : String) {B : BitVec 32} {Z w N a r m t nm u : Nat} {top qo : Option Nat}
    (T : DivTaint a r m t nm u top qo) (hq : QArr N r m t nm u qo) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) :
    RelCT isa (fun s t' => (DivPre B Z w N m s a top ∧ QZ s.mem B w qo) ∧ (DivPre B Z w N m t' a top ∧
      QZ t'.mem B w qo)) (divWC name a r m t nm u top qo) fun _ _ => True := by
  have hdw : 3 ≤ w / 2 := by omega_using [hw6]
  refine (RelCT.exists_ (P := fun (p : State × State) s t' => (s = p.1 ∧ DivPre B Z w N m p.1 a top ∧
    QZ p.1.mem B w qo) ∧ (t' = p.2 ∧ DivPre B Z w N m p.2 a top ∧ QZ p.2.mem B w qo)) fun p => ?_).mono
    (fun s t' h => ⟨(s, t'), ⟨rfl, h.1⟩, rfl, h.2⟩) fun _ _ h => h
  obtain ⟨σ₁, σ₂⟩ := p
  let Inv (σ : State) (n : Nat) (y : State) : Prop :=
    ∃ x0 z, DivSt x0 y B Z w N r m t nm u z (num σ.mem B w m) (num σ.mem B w a) n qo
  rw [divWC]
  -- The preparation.
  by_cases hT : TopOk top w (num σ₁.mem B w a)
  swap
  · exact RelCT.of_false fun s t' h => hT h.1.2.1.2.2.2.2.2
  have hj1 := (hT.facts (by simp only [num]; exact val32_lt _ _ _ _) (by omega_using [hw6])).1
  have fP : ∀ σ s, (s = σ ∧ DivPre B Z w N m σ a top ∧ QZ σ.mem B w qo) →
      WP isa (prep a r m nm top) s (Inv σ (jStart top w)) := by
    rintro σ s ⟨rfl, ⟨W, c16, hMl, hT0, z0, htop⟩, hq0⟩
    exact WP.mono (prepQ_ok t u W ha hr hm hnm hN hra hmr hnm' hnr hr0 hn0 hw6 c16 rfl hMl hT0 z0 htop hq hq0)
      fun x0 ⟨⟨z, I0⟩, _, _⟩ => ⟨x0, z, I0⟩
  refine RelCT.seq (piece [.r7, .r8, .r9] T.prep (fun s t' h₁ h₂ => by rw [h₁.1, h₂.1]; exact ws_regs' h₁.2.1.1 h₂.2.1.1)
    (fP σ₁) (fP σ₂)) ?_
  -- The call.
  refine RelCT.call_of (P' := fun s t' => Inv σ₁ (jStart top w) s ∧ Inv σ₂ (jStart top w) t') ?_
    fun s t' ⟨⟨x0, z, h₁⟩, ⟨x0', z', h₂⟩⟩ => ⟨⟨x0, z, h₁.callEntry⟩, ⟨x0', z', h₂.callEntry⟩⟩
  rw [tailFn]
  -- `lr` into `sT`, from which the invariant holds again.
  have fS : ∀ σ s, Inv σ (jStart top w) s →
      WP isa (.block [.str .lr .r8 VG.Impl.Rsa.Arm.Keys.sT]) s (Inv σ (jStart top w)) := by
    rintro σ s ⟨x0, z, I⟩
    exact wp_strSlot I.ws (by decide) fun s1 m1 => WP.block_nil_iff.mpr
      ⟨s1, z, I.restart (I.ws.of_mupd m1) m1.mem hr hm hnm hq⟩
  refine RelCT.seq (piece [.r8] strT_taint (fun s t' ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => r8_regs h₁.ws h₂.ws)
    (fS σ₁) (fS σ₂)) ?_
  -- The steps, with `Ws` after them in each run.
  have fT : ∀ σ s, Inv σ (jStart top w) s → WP isa (VG.Impl.Rsa.Arm.KeyDiv.tail r m t nm u qo) s
      fun y => Ws y B Z w N := by
    rintro σ s ⟨x0, z, I⟩
    exact WP.mono (tail_ok I hj1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw hq)
      fun _ h => h.1
  refine RelCT.seq (((tail_ct T hq hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw σ₁ σ₂
    hj1).wp (F₁ := fun y => Ws y B Z w N) (F₂ := fun y => Ws y B Z w N)
    fun s t' h => ⟨fT σ₁ s h.1, fT σ₂ t' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  -- `lr` from `sT`.
  exact (piece (Q₁ := fun _ => True) (Q₂ := fun _ => True) [.r8] ldrT_taint
    (fun s t' h₁ h₂ => r8_regs h₁ h₂)
    (fun s h => wp_ldrSlot h (by decide) fun _ _ => WP.block_nil_iff.mpr trivial)
    (fun s h => wp_ldrSlot h (by decide) fun _ _ => WP.block_nil_iff.mpr trivial)).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-- `divWC name a r m t nm u` is constant time. -/
theorem divWC_ct (name : String) {B : BitVec 32} {Z w N a r m t nm u : Nat} {top : Option Nat}
    (T : DivTaint a r m t nm u top) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) :
    RelCT isa (fun s t' => DivPre B Z w N m s a top ∧ DivPre B Z w N m t' a top) (divWC name a r m t nm u top)
      fun _ _ => True :=
  (divWCG_ct name (qo := none) T trivial ha hr hm ht hnm hu hN hra hrt hru htu hmr hmt hmu hnr htn hnu hnm' hr0
    ht0 hu0 hn0 hw6).mono (fun _ _ h => ⟨⟨h.1, trivial⟩, h.2, trivial⟩) fun _ _ h => h

end VG.Proof.Rsa.Arm.KeyDiv

