import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Bignum.AArch64.Store

/-!
# RSA private keys on AArch64: the working space and its pieces

`Ws`: the working space `vg_rsa_crt_values` and `vg_rsa_recover_primes` set
up, the header giving `w`, the stride and the bases of arrays 0 to 7, and 16
arrays fitting in it; kept by code that changes only arrays and the header
slot `sMask` (`Ws.congr`). The pieces of the functions that load, clear,
copy and store arrays (`zeroA_ok`, `copyA_ok`, `loadA_ok`, `storeA_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem slot_lt {w j K : Nat} (h : j < K) : slot w j + 8 * (w + 2) ≤ slot w K := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ K by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- The byte range of array `j`. -/
abbrev ar (w j : Nat) : Nat × Nat := (slot w j, 8 * (w + 2))

/-- The working space at `B` of `Z` bytes, for `w`-word numbers. -/
structure Ws (s : State) (B : Addr) (Z w : Nat) : Prop where
  scr : Scr s B Z
  x0 : s.gpr .x0 = B
  hw : word s.mem B (8 * sW) = BitVec.ofNat 64 w
  hS : word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2))
  harr : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot w j)
  hZ : slot w 16 ≤ Z
  w1 : 2 ≤ w
  w2 : w < 2 ^ 24

theorem wv_zero {m : Mem} {B : Addr} {d n : Nat} (h : ∀ k < n, word m B (d + 8 * k) = 0) : wv m B d n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wv, ih fun k hk => h k (by omega), h n (by omega)]; rfl

/-- The ranges the pieces may change: arrays and `sMask`. -/
def Mut (r : Nat × Nat) : Prop := 8 * 32 ≤ r.1 ∨ r = (8 * Public.sMask, 8)

theorem Mut.ofSlot (w j : Nat) (n : Nat) : Mut (slot w j, n) :=
  Or.inl (by unfold slot hdrBytes; omega)

theorem Ws.congr {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, Mut r) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    have hi' : i < 16 ∨ i = 28 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      rcases hm r hr with h | rfl
      · omega
      · simp only [Public.sMask, sFn]; omega)
      (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega)
  exact ⟨h.scr.congr k.wr, (k.gpr .x0 hr).trans h.x0, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩

theorem Ws.good {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    Good s B Z w (word s.mem B (8 * sMinv)) ∧ slot w 8 ≤ Z :=
  ⟨⟨h.scr, h.x0, ⟨h.hw, rfl, h.harr⟩⟩, Nat.le_trans (by unfold slot; omega) h.hZ⟩

theorem Ws.h256 {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) : 8 * 32 ≤ Z := by
  have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega

theorem Ws.sl {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) h.hZ

/-- `ws`, from the working space. -/
theorem Ws.ws_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block ws) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        t.c = s.c) ∧ Keep [.x11, .x12] s t :=
  VG.Proof.Rsa.AArch64.ws_ok h.scr h.x0 h.h256 h.hw h.hS

/-! ## Clearing and copying -/

/-- `zeroA j`: `[j] := 0` (`w + 2` words). -/
theorem zeroA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (zeroA j) s fun t =>
      wv t.mem B (slot w j) (w + 2) = 0 ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x7 = 0 ∧
        Keep [.x11, .x12, .x8, .x7, .x14, .x16] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold zeroA
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ =>
    WP.mono (base_ok j .x8 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h8, m₂, _⟩, k₂⟩ =>
      WP.mono (WP.keep [.x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = s₂.mem) (by brun) (by decide) (by decide)
        (by decide +kernel)) fun s₃ ⟨⟨h7, m₃⟩, k₃⟩ => ?_)))
  have k13 := (k₁.trans k₂).trans k₃
  have e12 : s₃.gpr .x12 = BitVec.ofNat 64 w := ((k₂.trans k₃).gpr .x12 (by decide)).trans h12
  have e11 : s₃.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := ((k₂.trans k₃).gpr .x11 (by decide)).trans h11
  refine WP.mono (zeroAcc_ok (h.scr.congr k13.wr) ((k₃.gpr .x8 (by decide)).trans h8) e12 h7
    (by have := h.w2; omega) (by omega)) fun t ⟨hz, o, k₄⟩ => ?_
  rw [m₃, m₂, m₁] at o
  exact ⟨hz, o, (k₄.gpr .x12 (by decide)).trans e12, (k₄.gpr .x11 (by decide)).trans e11,
    (k₄.gpr .x7 (by decide)).trans h7, (k13.trans k₄).mono (by simp)⟩

/-- Two bases. -/
theorem base2_ok {s : State} {B : Addr} {w : Nat} (i j : Nat) (r₁ r₂ : Reg) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (h₁ : r₁ ≠ .x11 := by decide) (h₂ : r₂ ≠ .x11 := by decide) (h₁₂ : r₂ ≠ r₁ := by decide)
    (hr1 : r₁ ≠ .x0 := by decide)
    (hc₁ : writesOnly [r₁] (.block [.addImm .x r₁ .x0 hdrBytes]) = true := by decide)
    (hv₁ : Code.allInstrs keepsV (.block [.addImm .x r₁ .x0 hdrBytes] : Prog isa) = true := by decide +kernel)
    (hd₁ : writesOnly [r₁] (.block [.add .x r₁ r₁ .x11]) = true := by decide)
    (hw₁ : Code.allInstrs keepsV (.block [.add .x r₁ r₁ .x11] : Prog isa) = true := by decide +kernel)
    (hc₂ : writesOnly [r₂] (.block [.addImm .x r₂ .x0 hdrBytes]) = true := by decide)
    (hv₂ : Code.allInstrs keepsV (.block [.addImm .x r₂ .x0 hdrBytes] : Prog isa) = true := by decide +kernel)
    (hd₂ : writesOnly [r₂] (.block [.add .x r₂ r₂ .x11]) = true := by decide)
    (hw₂ : Code.allInstrs keepsV (.block [.add .x r₂ r₂ .x11] : Prog isa) = true := by decide +kernel) :
    WP isa (.block (base i r₁ ++ base j r₂)) s fun t =>
      (t.gpr r₁ = off B (slot w i) ∧ t.gpr r₂ = off B (slot w j) ∧ t.mem = s.mem ∧ t.c = s.c) ∧
        Keep [r₁, r₂] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (base_ok i r₁ h0 h11 h₁ hc₁ hv₁ hd₁ hw₁) fun t₁ ⟨⟨e₁, m₁, c₁⟩, k₁⟩ => ?_
  have g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr r (by simp [h])
  refine WP.mono (base_ok j r₂ ((g1 _ (Ne.symm hr1)).trans h0) ((g1 _ (Ne.symm h₁)).trans h11) h₂ hc₂ hv₂ hd₂ hw₂)
    fun t ⟨⟨e₂, m₂, c₂⟩, k₂⟩ => ?_
  exact ⟨⟨(k₂.gpr r₁ (by simp [Ne.symm h₁₂])).trans e₁, e₂, m₂.trans m₁, c₂.trans c₁⟩, (k₁.trans k₂).mono (by simp)⟩

/-- `copyA o a`: `[o] := [a]` over `w` words. -/
theorem copyA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w a) w ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        Keep [.x11, .x12, .x3, .x14, .x16, .x17] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have sp := slot_sep (w := w) hoa
  unfold copyA
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, c₁⟩, k₁⟩ =>
    WP.mono (base2_ok a o .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, h17, m₂, c₂⟩, k₂⟩ => ?_))
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have e11 : s₂.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₂.gpr .x11 (by decide)).trans h11
  refine WP.mono (copyWords_ok h16 h17 e12 (by have := h.w1; omega)
    (by have := h.w2; omega) (by omega) (fun i hi => hs₂.ld (by omega)) (fun i hi => hs₂.st (by omega))
    (fun i hi b hb => by rw [ofs_off B (by omega)]; omega)) fun t ⟨hv, _, o', _, _, k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  exact ⟨hv, o', (k₃.gpr .x12 (by decide)).trans e12, (k₃.gpr .x11 (by decide)).trans e11,
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-! ## Bytes -/

/-- `loadA j sPtr sLen`: `[j] := ` the `len` bytes at `p`, most significant
first, over `w` words. -/
theorem loadA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = p) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s B Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      wv t.mem B (slot w j) w = Spec.Rsa.os2ip bs ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        Keep [.x11, .x12, .x8, .x7, .x14, .x16, .x1, .x2, .x3, .x4, .x5, .x6] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [loadA, seqs]
  refine WP.seq (WP.mono (zeroA_ok h hj) fun s₁ ⟨hz, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w j _) k₁ (by decide)
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    o₁.word (Or.inl (by have := hdr_lt_slot w j hi; omega)) (by omega)
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h₁.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = p ∧ t.gpr .x2 = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h₁.x0
          have hs₃ := h₁.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hh sPtr hP, hh sLen hL, hp, hl])
        rfl rfl rfl)
      fun s₄ ⟨⟨h1, h2, m₄⟩, k₄⟩ => ?_)))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.scr.congr k14.wr
  have hsrc₄ : Src s₄ B Z p bs := hsrc.congrK (fun x hx => by
    rw [m₄, m₃, m₂]; exact o₁ x (Or.inr (by omega))) k14
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) hs₄ h1 h2 ((k₄.gpr .x8 (by decide)).trans h8) hlen hl1 (by omega) rfl
    (by omega) (fun i hi => hsrc₄.rd i (by omega)) (fun i hi => hsrc₄.val i (by omega))
    (fun i hi => Or.inr (by have := hsrc₄.out i (by omega); omega))) fun t ⟨hv, o, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at o
  have k25 := (k₃.trans k₄).trans k₅
  refine ⟨?_, fun x hx => by rw [o x (by omega), o₁ x hx], (k25.gpr .x12 (by decide)).trans h12,
    (k25.gpr .x11 (by decide)).trans h11, (k14.trans k₅).mono (by simp)⟩
  -- The words above the loaded ones are still zero.
  have hz' : ∀ q < w + 2, word s₁.mem B (slot w j + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  have e := wv_add t.mem B (slot w j) ((len + 7) / 8) (w - (len + 7) / 8)
  rw [show (len + 7) / 8 + (w - (len + 7) / 8) = w by omega] at e
  rw [e, hv, wv_zero (n := w - (len + 7) / 8) fun q hq => by
      rw [o.word (by omega) (by omega), Nat.add_assoc, ← Nat.mul_add]; exact hz' _ (by omega)]
  simp

/-- `storeA j sPtr sLen sMsk`: the low `⌈len / 8⌉` words of `[j]`, masked by
the slot `sMsk`, as `len` bytes at `out`. -/
theorem storeA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen sMsk len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hM : sMsk < 32)
    (hp : word s.mem B (8 * sPtr) = out) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : word s.mem B (8 * sMsk) = mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen sMsk)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ t.wr = s.wr ∧ t.rd = s.rd ∧
      Keep [.x11, .x12, .x8, .x1, .x9, .x15, .x2, .x3, .x5, .x6] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [storeA, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x9, .x15] (Q := fun t => t.gpr .x1 = out + BitVec.ofNat 64 len ∧
        t.gpr .x9 = BitVec.ofNat 64 len ∧ t.gpr .x15 = mask c ∧ t.mem = s₃.mem) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, hdr_enc hM, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hl₃ sMsk hM, hp, hl, hm])
        rfl rfl rfl)
      fun s₄ ⟨⟨h1, h9, h15, m₄⟩, k₄⟩ => ?_)))
  have k24 := (k₂.trans k₃).trans k₄
  refine WP.mono (storeBE_ok (w := (len + 7) / 8) (h.scr.congr k24.wr) ((k₄.gpr .x8 (by decide)).trans h8) h1 h9 h15
    hl1 (by omega) rfl (by omega) (fun i hi => by rw [k24.wr]; exact hout i hi) hsep)
    fun t ⟨hb, hx, hwr, hrd, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at hb hx
  exact ⟨hb, hx, hwr.trans k24.wr, hrd.trans k24.rd, (k24.trans k₅).mono (by simp)⟩

/-- A number below `2^(64 v)` is its low `v` words. -/
theorem wv_low_of_lt {m : Mem} {B : Addr} {e v w : Nat} (hv : v ≤ w) (h : wv m B e w < 2 ^ (64 * v)) :
    wv m B e v = wv m B e w := by
  have e1 := wv_add m B e v (w - v)
  rw [show v + (w - v) = w by omega] at e1
  have : wv m B (e + 8 * v) (w - v) = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (e + 8 * v) (w - v)) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * wv m B (e + 8 * v) (w - v) := Nat.le_mul_of_pos_right _ h0
      omega
  rw [e1, this]; simp

end VG.Proof.Rsa.AArch64
