import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase

/-!
# `vg_rsa_crt_values` on AArch64: constant time, the pieces of `main`

`GA p`: what holds between the pieces of `main`'s arithmetic, for the
public data `p` (the working space, the pointers and lengths, `n`); each
piece leaks the same in two runs from `GA p` and leaves `GA p` (`zeroA_ct`,
…), its registers pinned after `ws` (`ws_ct`), after the clearing of an
array (`divmod_ct`) or, for the loads, after the block that loads the
pointer and the length (`loadA_ct`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

/-- The public data of `vg_rsa_crt_values`: the working space, the
pointers and lengths, `n` and the writable regions. -/
structure CvP where
  B : Addr
  Z : Nat
  k : Nat
  pl : Nat
  ql : Nat
  dl : Nat
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pN : Addr
  pP : Addr
  pQ : Addr
  pD : Addr
  nb : List Byte
  W : List Region
  deriving Inhabited

/-- The public part of the inputs. -/
def CvIn.pub (I : CvIn) : CvP :=
  ⟨I.B, I.Z, I.k, I.pl, I.ql, I.dl, I.pDp, I.pDq, I.pQi, I.pN, I.pP, I.pQ, I.pD, I.nb, I.W⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure CvOuts (I : CvIn) : Prop where
  qi : ∀ i < I.pl, InRegions I.W (I.pQi + BitVec.ofNat 64 i) 1
  dp : ∀ i < I.pl, InRegions I.W (I.pDp + BitVec.ofNat 64 i) 1
  dq : ∀ i < I.ql, InRegions I.W (I.pDq + BitVec.ofNat 64 i) 1
  sqi : ∀ i < I.pl, I.Z ≤ ofs I.B (I.pQi + BitVec.ofNat 64 i)
  sdp : ∀ i < I.pl, I.Z ≤ ofs I.B (I.pDp + BitVec.ofNat 64 i)
  sdq : ∀ i < I.ql, I.Z ≤ ofs I.B (I.pDq + BitVec.ofNat 64 i)
  a1 : Apart I.pQi I.pl I.pDp I.pl
  a2 : Apart I.pQi I.pl I.pDq I.ql
  a3 : Apart I.pDp I.pl I.pDq I.ql

/-- Between the pieces of `main`'s arithmetic. -/
def GA (p : CvP) (s : State) : Prop :=
  ∃ (I : CvIn) (m₀ : Mem) (c : Bool), I.pub = p ∧ CvS I m₀ s ∧ CvLens I ∧ CvOuts I ∧ mword s.mem I.B = mask c

theorem GA.ws {p : CvP} {s : State} (h : GA p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, m₀, c, rfl, h, -⟩ := h
  exact h.ws

/-- The mask, after a piece that changes only an array. -/
theorem mword_out {m m' : Mem} {B : Addr} {w j L : Nat} (o : Outside B (slot w j) L m m') :
    mword m' B = mword m B :=
  o.word (Or.inl (by have := hdr_lt_slot w j (show Public.sMask < 32 by decide); omega))
    (by simp only [Public.sMask, sFn]; omega)

/-- `GA` after a piece that changes only array `j`'s first `n` bytes. -/
theorem GA.arr {p : CvP} {s t : State} (h : GA p s) {j n : Nat} (hj : j < 16) (hn : n ≤ 8 * (wk p.k + 2))
    (o : Outside p.B (slot (wk p.k) j) n s.mem t.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  exact ⟨I, m₀, c, rfl, h.arr hj hn o k hr, L, O, (mword_out o).trans hm⟩

/-- `GA` after a piece that changes only the arrays of `rs`. -/
theorem GA.frm {p : CvP} {s t : State} (h : GA p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hm : ∀ r ∈ rs, ∃ j < 16, r = (slot (wk p.k) j, 8 * (wk p.k + 2)) ∨
      r = (slot (wk p.k) j, 8 * wk p.k))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hmw⟩ := h
  dsimp only [CvIn.pub] at hf hm ⊢
  have hZ := h.ws.hZ
  have hn := h.ws.scr.nowrap
  refine ⟨I, m₀, c, rfl, h.step hf (fun r hr => ?_) (fun r hr => ?_) k hr, L, O, ?_⟩
  · obtain ⟨j, hj, rfl | rfl⟩ := hm r hr
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
  · obtain ⟨j, hj, rfl | rfl⟩ := hm r hr
    · have := h.ws.sl hj; dsimp only; omega
    · have := h.ws.sl hj; dsimp only; omega
  · refine (hf.word_eq (fun r hr => ?_) (by simp only [Public.sMask, sFn]; omega)).trans hmw
    obtain ⟨j, hj, rfl | rfl⟩ := hm r hr
    · have := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide); dsimp only; omega
    · have := hdr_lt_slot (wk I.k) j (show Public.sMask < 32 by decide); dsimp only; omega

/-- `GA` after a piece that changes no memory. -/
theorem GA.same {p : CvP} {s t : State} (h : GA p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hmw⟩ := h
  exact ⟨I, m₀, c, rfl, h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr, L, O,
    by rw [hm]; exact hmw⟩

/-- `GA` after a store to the mask. -/
theorem GA.mask {p : CvP} {s t : State} (h : GA p s) {v : BitVec 64} {c : Bool} (hv : v = mask c)
    (hm : t.mem = s.mem.writeW (off p.B (8 * Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c', rfl, h, L, O, -⟩ := h
  obtain ⟨ht, hmt, -⟩ := h.mask hm k hr
  exact ⟨I, m₀, c, rfl, ht, L, O, hmt.trans hv⟩

/-- `GA` after a store of a word to array `j`. -/
theorem GA.word {p : CvP} {s t : State} (h : GA p s) {j : Nat} (hj : j < 16) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off p.B (slot (wk p.k) j)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : GA p t := by
  have hw := h.ws
  have o := writeW_outside s.mem p.B v (d := slot (wk p.k) j) (by have := hw.sl hj; have := hw.scr.nowrap; omega)
  rw [← hm] at o
  exact h.arr hj (by omega) o k hr

theorem pins_GA : Pins GA [.x0] := pins_ws CvP.B CvP.Z (fun p => wk p.k) fun _ _ h => h.ws

/-! ## The pieces -/

theorem zeroA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc).isSome = true) :
    RelCT isa (Two GA) (zeroA j) (Two GA) := by
  have e : zeroA j = .seq (.block (ws ++ (base j .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  rw [e]
  exact ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, _, _, _, k⟩ => h.arr hj (Nat.le_refl _) o k (by decide)

theorem copyA_ct {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two GA) (copyA o a) (Two GA) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .x16 ++ base o .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (copyA_ok h.ws ho ha hoa) fun _ ⟨_, o', _, _, k⟩ => h.arr ho (by omega) o' k (by decide)

theorem divmod_ct {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base iR .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep iQ iR iD iT) (.nonzero .x .x6))) hc₂).isSome = true) :
    RelCT isa (Two GA) (divmod iQ iR iD iT) (Two GA) := by
  have e : divmod iQ iR iD iT = .seq (zeroA iR) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep iQ iR iD iT) (.nonzero .x .x6))) := rfl
  rw [e]
  refine pin_seq [.x0, .x12, .x11] (fun p => wsVal p.B (wk p.k))
    ((zeroA_ct hR ht₁).mono (fun _ _ h => h) fun _ _ _ => trivial) (fun _ _ h => ?_) ht₂ fun _ _ h => ?_
  · exact WP.mono (zeroA_ok h.ws hR) fun _ ⟨_, _, h12, h11, _, k⟩ =>
      wsVal_of ((k.gpr .x0 (by decide)).trans h.ws.x0) h12 h11
  · rw [← e]
    exact WP.mono (divmod_ok h.ws hQ hR hD hT dQR dQD dQT dRD dRT dDT) fun _ ⟨_, f, k, _⟩ => h.frm f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨iQ, hQ, .inl rfl⟩
      · exact ⟨iR, hR, .inl rfl⟩
      · exact ⟨iT, hT, .inl rfl⟩) k (by decide)

theorem eqA_ct {a b : Nat} (ha : a < 16) (hb : b < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base a .x16 ++ base b .x17)) (countLoop .x14 xorBody))) hc).isSome = true) :
    RelCT isa (Two GA) (seqs (eqA a b)) (Two GA) :=
  ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h =>
    WP.mono (eqA_ok h.ws ha hb) fun _ ⟨_, hm, _, _, k⟩ => h.same hm k (by decide)

theorem andZero_ct : RelCT isa (Two GA) (.block andZero) (Two GA) :=
  two_piece [.x0] pins_GA (by taint_decide) fun _ s h => by
    obtain ⟨I, m₀, c, rfl, h', L, O, hmw⟩ := id h
    exact WP.mono (andZero_ok (z := s.gpr .x9 = 0) h'.ws hmw Iff.rfl) fun _ ⟨⟨hm, _⟩, k⟩ =>
      h.mask rfl hm k (by decide)

/-- A block that starts with `ws`. -/
theorem ws_drop {l : List Instr} (h : l.take 2 = ws) : l = ws ++ l.drop 2 := by
  rw [← h, List.take_append_drop]

theorem andOdd_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block ((andOdd j).drop 2)) hc).isSome = true) :
    RelCT isa (Two GA) (.block (andOdd j)) (Two GA) := by
  have e := ws_drop (l := andOdd j) (by simp [andOdd, ws])
  rw [e]
  exact ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    obtain ⟨I, m₀, c, rfl, h', L, O, hmw⟩ := id h
    exact WP.mono (andOdd_ok h'.ws hj hmw) fun _ ⟨hm, k⟩ => h.mask rfl hm k (by decide)

theorem setOneA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block ((setOneA j).drop 2)) hc).isSome = true) :
    RelCT isa (Two GA) (.block (setOneA j)) (Two GA) := by
  have e := ws_drop (l := setOneA j) (by simp [setOneA, ws])
  rw [e]
  exact ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (setOneA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

theorem decA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block ((decA j).drop 2)) hc).isSome = true) :
    RelCT isa (Two GA) (.block (decA j)) (Two GA) := by
  have e := ws_drop (l := decA j) (by simp [decA, ws])
  rw [e]
  exact ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (decA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

/-- `GA` with `inverse`'s start. -/
def GI (p : CvP) (s : State) : Prop :=
  GA p s ∧ word s.mem p.B (slot (wk p.k) aU + 8 * wk p.k) = 0 ∧
    wv s.mem p.B (slot (wk p.k) aV) (wk p.k) = wv s.mem p.B (slot (wk p.k) aP) (wk p.k) ∧
    wv s.mem p.B (slot (wk p.k) aX₁) (wk p.k) = 1 ∧ wv s.mem p.B (slot (wk p.k) aX₂) (wk p.k) = 0

theorem inverse_ct {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [.lsl .x .x6 .x12 7])
      (.loop (VG.Impl.Rsa.AArch64.Keys.invStep aU aV aX₁ aX₂ aP aT) (.nonzero .x .x6))) hc).isSome = true) :
    RelCT isa (Two GI) (inverse aU aV aX₁ aX₂ aP aT) (Two GA) :=
  ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.1.ws) ht fun _ _ ⟨h, u0, vm, x1, x2⟩ =>
    WP.mono (inverse_ok h.ws (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aP) (iT := aT) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) u0 vm x1 x2) fun _ ⟨_, f, k, _⟩ => h.frm f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact ⟨aU, by decide, .inr rfl⟩
        · exact ⟨aV, by decide, .inr rfl⟩
        · exact ⟨aX₁, by decide, .inr rfl⟩
        · exact ⟨aX₂, by decide, .inr rfl⟩
        · exact ⟨aT, by decide, .inl rfl⟩) k (by decide)

/-! ## The loads -/

/-- The registers `loadBE` and `storeBE` need pinned. -/
def ioVal (B base ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => base
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

/-- The block before `loadBE`: the base of `[j]`, the pointer and the length. -/
theorem loadBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen])) s fun t =>
      ∀ r ∈ [Reg.x0, .x8, .x1, .x2], t.gpr r = ioVal B (off B (slot w j)) ptr len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = ptr ∧ t.gpr .x2 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hp, hl])
        rfl rfl rfl)
      fun t ⟨⟨h1, h2⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h2))

/-- `loadA j sPtr sLen`, from a `GA` with the pointer and the length in the
header slots `sPtr` and `sLen`. -/
theorem loadA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr)
    (len : CvP → Nat)
    (hA : ∀ p s, GA p s → word s.mem p.B (8 * sPtr) = ptr p ∧ word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two GA) (seqs (loadA j sPtr sLen)) (Two GA) := by
  refine RelCT.assoc (pin_seq [.x0, .x8, .x1, .x2] (fun p => ioVal p.B (off p.B (slot (wk p.k) j)) (ptr p) (len p))
    (RelCT.seq (zeroA_ct hj ht₁) (two_taint [.x0] pins_GA ht₂)) (fun p s h => ?_) ht₃ fun p s h => ?_)
  · refine WP.seq (WP.mono (zeroA_ok h.ws hj) fun t ⟨_, o, _, _, _, k⟩ => ?_)
    have ht := h.arr hj (Nat.le_refl _) o k (by decide)
    obtain ⟨hp, hl, -⟩ := hA p t ht
    exact loadBlk_ok ht.ws hP hL hp hl
  · obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA p s h
    exact WP.assoc' (WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hbl hl1 hlw) fun _ ⟨_, o, _, _, k⟩ =>
      h.arr hj (Nat.le_refl _) o k (by decide))

end VG.Proof.Rsa.AArch64
