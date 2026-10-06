import VerifiedGarbage.Proof.Rsa.AArch64.CkCode
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain

/-!
# `vg_rsa_check_key` on AArch64: constant time, the pieces of `main`

`GK p`: what holds between the pieces of `main`, for the public data `p`
(the working space, the pointers and lengths, `n` and `e`); each piece
leaks the same in two runs from `GK p` and leaves `GK p`, its registers
pinned after `ws` (`ws_ct`), after the clearing of an array, or after the
block that loads a pointer and a length.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The public data of `vg_rsa_check_key`: the working space, the pointers
and lengths, `n`, `e` and the writable regions. -/
structure CkP where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pl : Nat
  ql : Nat
  pN : Addr
  pE : Addr
  pD : Addr
  pP : Addr
  pQ : Addr
  pDp : Addr
  pDq : Addr
  pQi : Addr
  nb : List Byte
  eb : List Byte
  W : List Region
  deriving Inhabited

/-- The public part of the inputs. -/
def CkIn.pub (I : CkIn) : CkP :=
  ⟨I.B, I.Z, I.k, I.el, I.dl, I.pl, I.ql, I.pN, I.pE, I.pD, I.pP, I.pQ, I.pDp, I.pDq, I.pQi, I.nb, I.eb, I.W⟩

/-- Between the pieces of `main`. -/
def GK (p : CkP) (s : State) : Prop :=
  ∃ (I : CkIn) (m₀ : Mem) (c : Bool), I.pub = p ∧ CkS I m₀ s ∧ CkLens I ∧ mword s.mem I.B = mask c

theorem GK.ws {p : CkP} {s : State} (h : GK p s) : Ws s p.B p.Z (wW p.k) := by
  obtain ⟨I, m₀, c, rfl, h, -⟩ := h
  exact h.ws

theorem pins_GK : Pins GK [.x0] := pins_ws CkP.B CkP.Z (fun p => wW p.k) fun _ _ h => h.ws

/-- `GK` after a piece that changes only array `j`'s first `n` bytes. -/
theorem GK.arr {p : CkP} {s t : State} (h : GK p s) {j n : Nat} (hj : j < 16) (hn : n ≤ 8 * (wW p.k + 2))
    (o : Outside p.B (slot (wW p.k) j) n s.mem t.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GK p t := by
  obtain ⟨I, m₀, c, rfl, h, L, hm⟩ := h
  exact ⟨I, m₀, c, rfl, h.arr hj hn o k hr, L, (mword_arr o).trans hm⟩

/-- `GK` after a piece that changes no memory. -/
theorem GK.same {p : CkP} {s t : State} (h : GK p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GK p t := by
  obtain ⟨I, m₀, c, rfl, h, L, hmw⟩ := h
  exact ⟨I, m₀, c, rfl, h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr, L,
    by rw [hm]; exact hmw⟩

/-- `GK` after a store to the mask. -/
theorem GK.mask {p : CkP} {s t : State} (h : GK p s) {v : BitVec 64} {c : Bool} (hv : v = mask c)
    (hm : t.mem = s.mem.writeW (off p.B (8 * Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : GK p t := by
  obtain ⟨I, m₀, c', rfl, h, L, -⟩ := h
  obtain ⟨ht, hmt, -⟩ := h.mask hm k hr
  exact ⟨I, m₀, c, rfl, ht, L, hmt.trans hv⟩

/-- `GK` after a store of a word to array `j`. -/
theorem GK.word {p : CkP} {s t : State} (h : GK p s) {j : Nat} (hj : j < 16) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off p.B (slot (wW p.k) j)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GK p t := by
  have hw := h.ws
  have o := writeW_outside s.mem p.B v (d := slot (wW p.k) j) (by have := hw.sl hj; have := hw.scr.nowrap; omega)
  rw [← hm] at o
  exact h.arr hj (by omega) o k hr

/-! ## The pieces -/

theorem zeroA_ckct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc).isSome = true) :
    RelCT isa (Two GK) (zeroA j) (Two GK) := by
  have e : zeroA j = .seq (.block (ws ++ (base j .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  rw [e]
  exact ws_ct CkP.B CkP.Z (fun p => wW p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, _, _, _, k⟩ => h.arr hj (Nat.le_refl _) o k (by decide)

theorem divmod_ckct {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aRem .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep aA aRem aM aT) (.nonzero .x .x6))) hc₂).isSome = true) :
    RelCT isa (Two GK) (divmod aA aRem aM aT) (Two GK) := by
  have e : divmod aA aRem aM aT = .seq (zeroA aRem) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep aA aRem aM aT) (.nonzero .x .x6))) := rfl
  rw [e]
  refine pin_seq [.x0, .x12, .x11] (fun p => wsVal p.B (wW p.k))
    ((zeroA_ckct (by decide) ht₁).mono (fun _ _ h => h) fun _ _ _ => trivial) (fun _ _ h => ?_) ht₂ fun _ _ h => ?_
  · exact WP.mono (zeroA_ok h.ws (j := aRem) (by decide)) fun _ ⟨_, _, h12, h11, _, k⟩ =>
      wsVal_of ((k.gpr .x0 (by decide)).trans h.ws.x0) h12 h11
  · rw [← e]
    obtain ⟨I, m₀, c, rfl, hs, L, hm⟩ := id h
    exact WP.mono (ckDivmod_ok hs) fun _ ⟨ht, mt, _⟩ => ⟨I, m₀, c, rfl, ht, L, mt.trans hm⟩

theorem eqA_ckct {a b : Nat} (ha : a < 16) (hb : b < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base a .x16 ++ base b .x17)) (countLoop .x14 xorBody))) hc).isSome = true) :
    RelCT isa (Two GK) (seqs (eqA a b)) (Two GK) :=
  ws_ct CkP.B CkP.Z (fun p => wW p.k) (fun _ _ h => h.ws) ht fun _ _ h =>
    WP.mono (eqA_ok h.ws ha hb) fun _ ⟨_, hm, _, _, k⟩ => h.same hm k (by decide)

theorem andZero_ckct : RelCT isa (Two GK) (.block andZero) (Two GK) :=
  two_piece [.x0] pins_GK (by taint_decide) fun _ s h => by
    obtain ⟨I, m₀, c, rfl, h', L, hmw⟩ := id h
    exact WP.mono (andZero_ok (z := s.gpr .x9 = 0) h'.ws hmw Iff.rfl) fun _ ⟨⟨hm, _⟩, k⟩ =>
      h.mask rfl hm k (by decide)

theorem setOneA_ckct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block ((setOneA j).drop 2)) hc).isSome = true) :
    RelCT isa (Two GK) (.block (setOneA j)) (Two GK) := by
  have e := ws_drop (l := setOneA j) (by simp [setOneA, ws])
  rw [e]
  exact ws_block_ct CkP.B CkP.Z (fun p => wW p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (setOneA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

theorem decA_ckct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block ((decA j).drop 2)) hc).isSome = true) :
    RelCT isa (Two GK) (.block (decA j)) (Two GK) := by
  have e := ws_drop (l := decA j) (by simp [decA, ws])
  rw [e]
  exact ws_block_ct CkP.B CkP.Z (fun p => wW p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (decA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

/-- `GK`, with the arrays of `js` below `2^(64 w)`. -/
def GKb (js : List Nat) (p : CkP) (s : State) : Prop :=
  GK p s ∧ ∀ j ∈ js, wv s.mem p.B (slot (wW p.k) j) (wW p.k) < 2 ^ (64 * wk p.k)

theorem pins_GKb (js : List Nat) : Pins (GKb js) [.x0] := fun a s₁ s₂ h₁ h₂ => pins_GK a s₁ s₂ h₁.1 h₂.1

theorem GKb.ws {js : List Nat} {p : CkP} {s : State} (h : GKb js p s) : Ws s p.B p.Z (wW p.k) := h.1.ws

theorem GKb.mono {js js' : List Nat} (h : ∀ j ∈ js', j ∈ js) {p : CkP} {s : State} (hb : GKb js p s) :
    GKb js' p s := ⟨hb.1, fun j hj => hb.2 j (h j hj)⟩

theorem loadA_ckct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) {js : List Nat}
    (hjs : ∀ i ∈ js, i ≠ j ∧ i < 16) (ptr : CkP → Addr) (len : CkP → Nat)
    (hA : ∀ p s, GK p s → word s.mem p.B (8 * sPtr) = ptr p ∧ word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ p.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (GKb js)) (seqs (loadA j sPtr sLen)) (Two (GKb (j :: js))) := by
  refine RelCT.assoc (pin_seq [.x0, .x8, .x1, .x2] (fun p => ioVal p.B (off p.B (slot (wW p.k) j)) (ptr p) (len p))
    (RelCT.seq ((zeroA_ckct hj ht₁).mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) fun _ _ h => h)
      (two_taint [.x0] pins_GK ht₂)) (fun p s h => ?_) ht₃ fun p s h => ?_)
  · refine WP.seq (WP.mono (zeroA_ok h.ws hj) fun t ⟨_, o, _, _, _, k⟩ => ?_)
    have ht := h.1.arr hj (Nat.le_refl _) o k (by decide)
    obtain ⟨hp, hl, -⟩ := hA p t ht
    exact loadBlk_ok ht.ws hP hL hp hl
  · obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlk⟩ := hA p s h.1
    have hn := h.ws.scr.nowrap
    have hZ := h.ws.hZ
    exact WP.assoc' (WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hbl hl1 (by simp only [wW, wk]; omega))
      fun _ ⟨hv, o, _, _, k⟩ => ⟨h.1.arr hj (Nat.le_refl _) o k (by decide), fun i hi => by
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [hv]; exact lt_w (by rw [hbl]; exact hlk)
        · obtain ⟨hij, hi16⟩ := hjs i hi
          rw [outside_arr o (Nat.le_refl _) hij (by omega) hi16 hZ hn]; exact h.2 i hi⟩)

theorem ltA_ckct {a b : Nat} (ha : a < 16) (hb : b < 16) {js : List Nat} (hjs : ∀ j ∈ js, j < 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7])
      (.seq (.block (base a .x16 ++ base b .x17)) (.seq cmpLoop (.block (borrowMask ++
        [ldh .x3 Public.sMask, .logic .and .x .x15 .x15 .x3, sth .x15 Public.sMask]))))) hc).isSome = true) :
    RelCT isa (Two (GKb js)) (seqs (ltA a b)) (Two (GKb js)) :=
  ws_ct CkP.B CkP.Z (fun p => wW p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    obtain ⟨⟨I, m₀, c, rfl, h', L, hmw⟩, hbd⟩ := id h
    exact WP.mono (ltA_ok h'.ws ha hb hmw) fun t ⟨hm, k⟩ => by
      obtain ⟨ht, hmt, hv⟩ := h'.mask hm k (by decide)
      refine ⟨⟨I, m₀, _, rfl, ht, L, hmt⟩, fun j hj => ?_⟩
      dsimp only [CkIn.pub] at hbd ⊢
      rw [hv j (hjs j hj)]; exact hbd j hj

/-- A piece in two parts, the first to `Θ` and the second leaking the same
from it, with the whole's correctness carried across. -/
theorem ct_carry {α : Type} {Φ Θ Ψ : α → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True) (hw₁ : ∀ a s, Φ a s → WP isa c₁ s (Θ a))
    (h₂ : RelCT isa (Two fun a t => Θ a t ∧ WP isa c₂ t (Ψ a)) c₂ fun _ _ => True)
    (hw : ∀ a s, Φ a s → WP isa (.seq c₁ c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq c₁ c₂) (Two Ψ) :=
  RelCT.seq (two_post h₁ fun a s h => WP.and (hw₁ a s h) (WP.seq_iff.mp (hw a s h)))
    (two_post h₂ fun _ _ h => h.2)

/-- `zeroA j` keeps the bounds of the other arrays. -/
theorem zeroA_okb {j : Nat} (hj : j < 16) {js : List Nat} (hjs : ∀ i ∈ js, i ≠ j ∧ i < 16) {p : CkP} {s : State}
    (h : GKb js p s) : WP isa (zeroA j) s (GKb js p) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  exact WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, _, _, _, k⟩ => ⟨h.1.arr hj (Nat.le_refl _) o k (by decide),
    fun i hi => by
      obtain ⟨hij, hi16⟩ := hjs i hi
      rw [outside_arr o (Nat.le_refl _) hij (by omega) hi16 hZ hn]; exact h.2 i hi⟩

theorem mulE_ckct {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aA .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aE .x1 ++ base aX .x9 ++ base aA .x8 ++
      [ld .x1 .x1] ++ VG.Impl.Rsa.AArch64.CheckKey.narrow ++ [movi .x7 0])) mulAddRow) hc₂).isSome = true) :
    RelCT isa (Two (GKb [aX])) (seqs mulE) (Two GK) := by
  have e : seqs mulE = .seq (zeroA aA) (.seq (.block (ws ++ (base aE .x1 ++ base aX .x9 ++ base aA .x8 ++
      [ld .x1 .x1] ++ VG.Impl.Rsa.AArch64.CheckKey.narrow ++ [movi .x7 0]))) mulAddRow) := by
    simp only [mulE, seqs, List.append_assoc]
  rw [e]
  refine ct_carry (Θ := GKb [aX]) (Ψ := GK)
    ((zeroA_ckct (by decide) ht₁).mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) fun _ _ _ => trivial)
    (fun _ _ h => zeroA_okb (by decide) (by decide) h)
    ((ws_ct (Ψ := fun _ _ => True) CkP.B CkP.Z (fun p => wW p.k) (fun _ _ h => h.1.ws) ht₂ fun _ _ h =>
      WP.mono h.2 fun _ _ => trivial).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => ?_
  rw [← e]
  obtain ⟨⟨I, m₀, c, rfl, h', L, hmw⟩, hb⟩ := h
  exact WP.mono (mulE_ok h'.ws L.w1 rfl (hb aX (by simp))) fun _ ⟨_, o, k⟩ =>
    GK.arr ⟨I, m₀, c, rfl, h', L, hmw⟩ (by decide) (Nat.le_refl _) o k (by decide)

theorem mulXR_ckct {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aA .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aX .x5 ++ base aR .x9 ++ base aA .x8 ++
      [mov .x11 .x5] ++ VG.Impl.Rsa.AArch64.CheckKey.narrow ++ [mov .x13 .x12, movi .x7 0])) VG.Impl.Rsa.AArch64.Crt.mulRows) hc₂).isSome = true) :
    RelCT isa (Two (GKb [aX, aR])) (seqs mulXR) (Two GK) := by
  have e : seqs mulXR = .seq (zeroA aA) (.seq (.block (ws ++ (base aX .x5 ++ base aR .x9 ++ base aA .x8 ++
      [mov .x11 .x5] ++ VG.Impl.Rsa.AArch64.CheckKey.narrow ++ [mov .x13 .x12, movi .x7 0]))) VG.Impl.Rsa.AArch64.Crt.mulRows) := by
    simp only [mulXR, seqs, List.append_assoc]
  rw [e]
  refine ct_carry (Θ := GKb [aX, aR]) (Ψ := GK)
    ((zeroA_ckct (by decide) ht₁).mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) fun _ _ _ => trivial)
    (fun _ _ h => zeroA_okb (by decide) (by decide) h)
    ((ws_ct (Ψ := fun _ _ => True) CkP.B CkP.Z (fun p => wW p.k) (fun _ _ h => h.1.ws) ht₂ fun _ _ h =>
      WP.mono h.2 fun _ _ => trivial).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => ?_
  rw [← e]
  obtain ⟨⟨I, m₀, c, rfl, h', L, hmw⟩, hb⟩ := h
  exact WP.mono (mulXR_ok h'.ws L.w1 rfl (hb aX (by simp)) rfl (hb aR (by simp))) fun _ ⟨_, o, k⟩ =>
    GK.arr ⟨I, m₀, c, rfl, h', L, hmw⟩ (by decide) (Nat.le_refl _) o k (by decide)

end VG.Proof.Rsa.AArch64
