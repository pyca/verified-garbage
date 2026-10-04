import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase

/-!
# `vg_rsa_crt_values` on x86-64: constant time, the pieces of `main`

`GA p`: what holds between the pieces of `main`'s arithmetic, for the
public data `p` (the working space, the pointers and lengths, `n`); each
piece leaks the same in two runs from `GA p` and leaves `GA p` (`zeroA_ct`,
…), its registers pinned after `ws` (`ws_ct`) or, for the loads, after the
block that loads the pointer and the length (`loadTail_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)
open VG.Impl.Rsa.X86_64 (copyWords)

/-- The public data of `vg_rsa_crt_values`: the working space, the
pointers and lengths, `n`, the writable regions and the stack pointer. -/
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
  sp : Addr

/-- The public part of the inputs. -/
def CvIn.pub (I : CvIn) : CvP :=
  ⟨I.B, I.Z, I.k, I.pl, I.ql, I.dl, I.pDp, I.pDq, I.pQi, I.pN, I.pP, I.pQ, I.pD, I.nb, I.W, I.sp⟩

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
  o.word (Or.inl (by have := hdr_lt_slot w j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
    (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega)

/-- `GA` after a piece that changes only array `j`'s first `n` bytes. -/
theorem GA.arr {p : CvP} {s t : State} (h : GA p s) {j n : Nat} (hj : j < 16) (hn : n ≤ 8 * (wk p.k + 2))
    (o : Outside p.B (slot (wk p.k) j) n s.mem t.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  exact ⟨I, m₀, c, rfl, h.arr hj hn o k hr, L, O, (mword_out o).trans hm⟩

/-- `GA` after a piece that changes only the arrays of `rs`, and `sMo`. -/
theorem GA.frm {p : CvP} {s t : State} (h : GA p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hm : ∀ r ∈ rs, (∃ j < 16, r = (slot (wk p.k) j, 8 * (wk p.k + 2)) ∨
      r = (slot (wk p.k) j, 8 * wk p.k)) ∨ r = (8 * sMo, 8))
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hmw⟩ := h
  dsimp only [CvIn.pub] at hf hm ⊢
  have hZ := h.ws.hZ
  have hn := h.ws.scr.nowrap
  refine ⟨I, m₀, c, rfl, h.step hf (fun r hr => ?_) (fun r hr => ?_) k hr, L, O, ?_⟩
  · rcases hm r hr with ⟨j, hj, rfl | rfl⟩ | rfl
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Or.inr (Or.inr rfl)
  · rcases hm r hr with ⟨j, hj, rfl | rfl⟩ | rfl
    · have := h.ws.sl hj; dsimp only; omega
    · have := h.ws.sl hj; dsimp only; omega
    · have := h.ws.h256; simp only [sMo, sFn]; omega
  · refine (hf.word_eq (fun r hr => ?_) (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega)).trans hmw
    rcases hm r hr with ⟨j, hj, rfl | rfl⟩ | rfl
    · have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); dsimp only; omega
    · have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); dsimp only; omega
    · simp only [Impl.Bignum.X86_64.Public.sMask, sMo, sFn]; omega

/-! ## The pieces -/

theorem zeroA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two GA) (zeroA j) (Two GA) :=
  ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h =>
    WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, k⟩ => h.arr hj (Nat.le_refl _) o k (by decide)

theorem copyA_ct {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two GA) (copyA o a) (Two GA) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (copyA_ok h.ws ho ha hoa) fun _ ⟨_, o', k⟩ => h.arr ho (by omega) o' k (by decide)

theorem divmod_ct {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base iR .r8 ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)]))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne))) hc).isSome = true) :
    RelCT isa (Two GA) (divmod iQ iR iD iT) (Two GA) := by
  have e : divmod iQ iR iD iT = .seq (.block (ws ++ (base iR .r8 ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)])))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne)) := by
    simp only [divmod, divInit, seqs, List.append_assoc]
  rw [e]
  exact ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    have hw := h.ws
    exact WP.mono (divmod_ok hw.scr hw.rdi hw.hw hw.hS (by have := hw.w1; omega) hw.w2 hw.hZ hQ hR hD hT dQR dQD
      dQT dRD dRT dDT) fun _ ⟨_, f, k, _⟩ => h.frm f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inl ⟨iQ, hQ, .inl rfl⟩
        · exact .inl ⟨iR, hR, .inl rfl⟩
        · exact .inl ⟨iT, hT, .inl rfl⟩) k (by decide)

/-- `GA` after a piece that changes no memory. -/
theorem GA.same {p : CvP} {s t : State} (h : GA p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hmw⟩ := h
  exact ⟨I, m₀, c, rfl, h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr, L, O,
    by rw [hm]; exact hmw⟩

/-- `GA` after a store to the mask. -/
theorem GA.mask {p : CvP} {s t : State} (h : GA p s) {v : BitVec 64} {c : Bool} (hv : v = mask c)
    (hm : t.mem = s.mem.writeW (off p.B (8 * Impl.Bignum.X86_64.Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t := by
  obtain ⟨I, m₀, c', rfl, h, L, O, -⟩ := h
  obtain ⟨ht, hmt, -⟩ := h.mask hm k hr
  exact ⟨I, m₀, c, rfl, ht, L, O, hmt.trans hv⟩

theorem pins_GA : Pins GA [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem eqA_ct {a b : Nat} (ha : a < 16) (hb : b < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (wordLoop 0 xorBody)) hc).isSome = true) :
    RelCT isa (Two GA) (seqs (eqA a b)) (Two GA) := by
  have e : seqs (eqA a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 xorBody) := by
    simp only [eqA, seqs, List.append_assoc]
  rw [e]
  exact ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (eqA_ok h.ws ha hb) fun _ ⟨_, hm, k⟩ => h.same hm k (by decide)

theorem andZero_ct : RelCT isa (Two GA) (.block andZero) (Two GA) :=
  two_piece [.rdi] pins_GA (by taint_decide) fun _ s h => by
    obtain ⟨I, m₀, c, rfl, h', L, O, hmw⟩ := id h
    exact WP.mono (andZero_ok (z := s.gpr .rbp = 0) h'.ws hmw Iff.rfl) fun _ ⟨hm, k⟩ =>
      h.mask rfl hm k (by decide)

theorem andOdd_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)),
      .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .alu .and .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sMask)),
      .store (hdr Impl.Bignum.X86_64.Public.sMask) .rdx] : List Instr))) hc).isSome = true) :
    RelCT isa (Two GA) (.block (andOdd j)) (Two GA) := by
  have e : andOdd j = ws ++ (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)),
      .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .alu .and .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sMask)),
      .store (hdr Impl.Bignum.X86_64.Public.sMask) .rdx] : List Instr)) := by
    simp only [andOdd, List.append_assoc]
  rw [e]
  exact ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    obtain ⟨I, m₀, c, rfl, h', L, O, hmw⟩ := id h
    exact WP.mono (andOdd_ok h'.ws hj hmw) fun _ ⟨hm, k⟩ => h.mask rfl hm k (by decide)

/-- `GA` after a store of a word to array `j`. -/
theorem GA.word {p : CvP} {s t : State} (h : GA p s) {j : Nat} (hj : j < 16) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off p.B (slot (wk p.k) j)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t := by
  have hw := h.ws
  have o := writeW_outside s.mem p.B v (d := slot (wk p.k) j) (by have := hw.sl hj; have := hw.scr.nowrap; omega)
  rw [← hm] at o
  exact h.arr hj (by omega) o k hr

theorem setOneA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ ([.mov32 .rax (.imm 1),
      .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two GA) (.block (setOneA j)) (Two GA) := by
  have e : setOneA j = ws ++ (base j .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)) := by
    simp only [setOneA, List.append_assoc]
  rw [e]
  exact ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (setOneA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

theorem decA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)),
      .alu .sub .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two GA) (.block (decA j)) (Two GA) := by
  have e : decA j = ws ++ (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .sub .rax (.imm 1),
      .store (at0 .rbx) .rax] : List Instr)) := by
    simp only [decA, List.append_assoc]
  rw [e]
  exact ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (decA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

/-- `GA` with `inverse`'s start. -/
def GI (p : CvP) (s : State) : Prop :=
  GA p s ∧ Bignum.X86_64.word s.mem p.B (slot (wk p.k) aU + 8 * wk p.k) = 0 ∧
    wv s.mem p.B (slot (wk p.k) aV) (wk p.k) = wv s.mem p.B (slot (wk p.k) aP) (wk p.k) ∧
    wv s.mem p.B (slot (wk p.k) aX₁) (wk p.k) = 1 ∧ wv s.mem p.B (slot (wk p.k) aX₂) (wk p.k) = 0

theorem inverse_ct {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ([.mov .r11 (.reg .r12)] ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)])))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep aU aV aX₁ aX₂ aP aT) .ne)) hc).isSome = true) :
    RelCT isa (Two GI) (inverse aU aV aX₁ aX₂ aP aT) (Two GA) := by
  have e : inverse aU aV aX₁ aX₂ aP aT = .seq (.block (ws ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)]))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep aU aV aX₁ aX₂ aP aT) .ne) := by
    simp only [inverse, invInit, List.append_assoc]
  rw [e]
  exact ws_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.1.ws) ht fun _ _ ⟨h, u0, vm, x1, x2⟩ => by
    rw [← e]
    have hw := h.ws
    exact WP.mono (inverse_ok hw.scr hw.rdi hw.hw hw.hS (by have := hw.w1; omega) hw.w2 hw.hZ
      (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aP) (iT := aT) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      u0 vm x1 x2) fun _ ⟨_, f, k, _⟩ => h.frm f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inl ⟨aU, by decide, .inr rfl⟩
        · exact .inl ⟨aV, by decide, .inr rfl⟩
        · exact .inl ⟨aX₁, by decide, .inr rfl⟩
        · exact .inl ⟨aX₂, by decide, .inr rfl⟩
        · exact .inl ⟨aT, by decide, .inl rfl⟩
        · exact .inr rfl) k (by decide)

/-! ## The loads -/

/-- The block before `loadBE`: the base of `[j]`, the pointer and the length. -/
theorem loadBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : Bignum.X86_64.word s.mem B (8 * sPtr) = ptr)
    (hl : Bignum.X86_64.word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] : List Instr)))
      s fun t => t.gpr .rbx = off B (slot w j) ∧ t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .rdi = B ∧ t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .rsi, .rcx] s t := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hp, hl]) rfl)
      fun t ⟨⟨hsi, hcx, m₄⟩, k₄⟩ => ⟨(k₄.gpr (by decide)).trans hbx, hsi, hcx,
        ((k₂.trans k₃).trans k₄ |>.gpr (by decide)).trans h.rdi, by rw [m₄, m₃, m₂],
        ((k₂.trans k₃).trans k₄).mono (by simp)⟩))

/-- The registers `loadBE` and `storeBE` need pinned. -/
def ioVal (B base ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .rdi => B
  | .rbx => base
  | .rsi => ptr
  | .rcx => BitVec.ofNat 64 len
  | _ => 0

/-- `loadA`'s block and `loadBE`, from a `GA` with the pointer and the
length in the header slots `sPtr` and `sLen`. -/
theorem loadTail_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr)
    (len : CvP → Nat)
    (hA : ∀ p s, GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two GA) (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) loadBE) (Two GA) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (off p.B (slot (wk p.k) j)) (ptr p) (len p)) pins_GA ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact WP.mono (loadBlk_ok h.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA p s h
      have hw := h.ws
      have hn := hw.scr.nowrap
      have sj := hw.sl hj
      have hw2 := hw.w2
      refine WP.seq (WP.mono (loadBlk_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, _, hm, k⟩ => ?_)
      have ht := h.same hm k (by decide)
      have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
      exact WP.mono (loadBE_ok (w := (len p + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega) rfl (by omega)
        (fun i hi => hsrc'.rd i (by omega)) (fun i hi => hsrc'.val i (by omega))
        (fun i hi => Or.inr (by have := hsrc'.out i (by omega); omega))) fun t' ⟨_, o, k'⟩ =>
          ht.arr hj (by omega) o k' (by decide)

end VG.Proof.Rsa.X86_64
