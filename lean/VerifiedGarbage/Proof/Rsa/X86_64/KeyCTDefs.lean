import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# `vg_rsa_check_key` on x86-64: constant time, the context

Two runs agree on the public data (`KPub`: the working space, `w`, the
private values' pointers and lengths) but not on the values. Between the
pieces of `main`, both are in the checks' context (`KK`), each for its own
entry state. A piece loads the bases it needs from the header (checked by
the taint analysis from `rdi`), then runs from the registers that
correctness pins (`hdr_ct`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

/-- The public data of the checks. -/
structure KPub where
  B : Addr
  Z : Nat
  w : Nat
  pd : Addr
  pp : Addr
  pq : Addr
  pdp : Addr
  pdq : Addr
  pqi : Addr
  dl : Nat
  pl : Nat
  ql : Nat

/-- What the checks read of the entry state `s`: the private values'
pointers and lengths in the header, and their bytes. -/
structure KS (p : KPub) (s : State) : Prop where
  hD : word s.mem p.B (8 * sD) = p.pd
  hDl : word s.mem p.B (8 * sDlen) = BitVec.ofNat 64 p.dl
  hP : word s.mem p.B (8 * sP) = p.pp
  hPl : word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl
  hQ : word s.mem p.B (8 * sQ) = p.pq
  hQl : word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql
  hDP : word s.mem p.B (8 * sDP) = p.pdp
  hDQ : word s.mem p.B (8 * sDQ) = p.pdq
  hQI : word s.mem p.B (8 * sQI) = p.pqi
  srD : ∃ bs, Src s p.B p.Z p.pd bs ∧ bs.length = p.dl
  srP : ∃ bs, Src s p.B p.Z p.pp bs ∧ bs.length = p.pl
  srQ : ∃ bs, Src s p.B p.Z p.pq bs ∧ bs.length = p.ql
  srDP : ∃ bs, Src s p.B p.Z p.pdp bs ∧ bs.length = p.pl
  srDQ : ∃ bs, Src s p.B p.Z p.pdq bs ∧ bs.length = p.ql
  srQI : ∃ bs, Src s p.B p.Z p.pqi bs ∧ bs.length = p.pl
  dl1 : 1 ≤ p.dl
  dl2 : p.dl ≤ 8 * p.w
  pl1 : 1 ≤ p.pl
  pl2 : p.pl ≤ 8 * p.w
  ql1 : 1 ≤ p.ql
  ql2 : p.ql ≤ 8 * p.w

/-- In the checks' context, from some entry state. -/
def KK (p : KPub) (t : State) : Prop := ∃ s minv N, KCtx s t p.B p.Z p.w minv N ∧ KS p s

theorem KK.goodW {p : KPub} {t : State} (h : KK p t) : GoodW ⟨p.B, p.Z, p.w⟩ t :=
  let ⟨_, minv, _, c, _⟩ := h; ⟨minv, c.good, c.hZ⟩

theorem KK.rdi {p : KPub} {t : State} (h : KK p t) : t.gpr .rdi = p.B :=
  let ⟨_, _, _, c, _⟩ := h; c.good.rdi

theorem pins_kk : Pins KK [.rdi] :=
  pins_of (fun p _ => p.B) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.rdi

theorem KK.hl {p : KPub} {t : State} (h : KK p t) : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8 := by
  obtain ⟨_, _, _, c, _⟩ := h
  have hn := c.good.scr.nowrap
  have hZ := c.hZ
  intro i hi
  exact c.good.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega)

theorem KK.hdr {p : KPub} {t : State} (h : KK p t) : ∃ minv, Hdr t.mem p.B p.w minv :=
  let ⟨_, minv, _, c, _⟩ := h; ⟨minv, c.good.hdr⟩

theorem KK.w {p : KPub} {t : State} (h : KK p t) : 1 ≤ p.w ∧ p.w < 2 ^ 28 :=
  let ⟨_, _, _, c, _⟩ := h; ⟨c.w1, c.w2⟩

/-- `KK` with the same memory and `rdi`. -/
theorem KK.keep {p : KPub} {t t' : State} (h : KK p t) (hm : t'.mem = t.mem) (k : Keep mmRegs t t') : KK p t' := by
  obtain ⟨s, minv, N, c, hs⟩ := h
  exact ⟨s, minv, N, c.arr (js := []) (fun x _ => congrFun hm x) (fun _ h => absurd h List.not_mem_nil) List.not_mem_nil
    List.not_mem_nil k, hs⟩

/-- A list of registers and their values, as pins. -/
def RegsAre (vs : List (Reg × BitVec 64)) (t : State) : Prop := ∀ x ∈ vs, t.gpr x.1 = x.2

theorem regsAre_cons {r : Reg} {v : BitVec 64} {vs : List (Reg × BitVec 64)} {t : State} (h : t.gpr r = v)
    (hs : RegsAre vs t) : RegsAre ((r, v) :: vs) t := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h
  · exact hs x hx

theorem regsAre_nil {t : State} : RegsAre [] t := fun _ h => absurd h List.not_mem_nil

theorem pins_regs {α : Type} (vs : α → List (Reg × BitVec 64)) {rs : List Reg} (hrs : ∀ a, (vs a).map Prod.fst = rs) :
    Pins (fun a t => RegsAre (vs a) t) rs := by
  intro a s₁ s₂ h₁ h₂ r hr
  rw [← hrs a] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  exact (h₁ x hx).trans (h₂ x hx).symm

/-- Header loads from `rdi`, then `body` from the registers they pin. -/
theorem hdr_ct {α : Type} {Φ : α → State → Prop} (hpin : Pins Φ [.rdi]) {L : List Instr} {body : Prog isa}
    {rs : List Reg} (vs : α → List (Reg × BitVec 64)) (hrs : ∀ a, (vs a).map Prod.fst = rs)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block L) hc₁).isSome = true)
    (hB : (taint.check (Taint.ofRegs rs) body hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block L) s (RegsAre (vs a))) :
    RelCT isa (Two Φ) (.seq (.block L) body) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := fun a t => RegsAre (vs a) t) [.rdi] hpin hT hw) (two_taint rs (pins_regs vs hrs) hB)

/-- A piece constant time from `KK` that keeps it. -/
theorem kk_ct {c : Prog isa} (hct : RelCT isa (Two KK) c fun _ _ => True) (hw : ∀ p s, KK p s → WP isa c s (KK p)) :
    RelCT isa (Two KK) c (Two KK) :=
  two_post hct hw

/-! ## Clearing an array -/

theorem zeroArrK_ok {p : KPub} {s : State} (h : KK p s) {j : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne) :
    WP isa (VG.Impl.Rsa.X86_64.Crt.zeroArr j) s fun t => KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w := by
  obtain ⟨s₀, minv, N, c, hs⟩ := h
  have hn := c.good.scr.nowrap
  have hZ := c.hZ
  have := c.w1
  have := c.w2
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    c.good.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega)
  unfold VG.Impl.Rsa.X86_64.Crt.zeroArr
  refine WP.seq (WP.mono (WP.keep [.r8, .r12] (Q := fun t => t.gpr .r8 = off p.B (slot p.w j) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, c.good.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sW (by decide),
      c.good.hdr.harr j hj, c.good.hdr.hw]) rfl) fun s₁ ⟨⟨h8, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroAccLoop_ok (c.good.scr.congr k₁.2.2) h8 h12 (by omega) (by omega)
    (Nat.le_trans (slot_le hj) hZ)) fun t ⟨_, ho, k⟩ => ⟨⟨s₀, minv, N, c.arr
      (Arrays.of_outside (List.mem_singleton_self j) (by rw [hm₁] at ho; exact ho) (Nat.le_refl _) (Nat.le_refl _))
      (by simpa using hj) (by simpa using Ne.symm hjN) (by simpa using Ne.symm hj1) ((k₁.trans k).mono (by decide)),
      hs⟩, (k.gpr (by decide)).trans h12⟩

theorem zeroArrK_ct {j : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc).isSome = true) :
    RelCT isa (Two KK) (VG.Impl.Rsa.X86_64.Crt.zeroArr j) (Two fun p t => KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w) :=
  two_post (two_map (fun p : KPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h.goodW) (zeroArr_ct hj hT))
    fun _ _ h => zeroArrK_ok h hj hjN hj1

end VG.Proof.Rsa.X86_64.Key
