import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Store

/-!
# RSA private keys on x86-64: the working space and its pieces

`Ws`: the working space `vg_rsa_crt_values` and `vg_rsa_recover_primes` set
up, the header giving `w`, the stride and the bases of arrays 0 to 7, and 16
arrays fitting in it; kept by code that changes only arrays and the header
slots `sMask` and `sMo` (`Ws.congr`). The pieces of the functions that load,
clear, copy and store arrays (`zeroA_ok`, `copyA_ok`, `loadA_ok`,
`storeA_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The working space at `B` of `Z` bytes, for `w`-word numbers. -/
structure Ws (s : State) (B : Addr) (Z w : Nat) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
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

/-- The ranges the pieces may change: arrays, `sMask` and `sMo`. -/
def Mut (r : Nat × Nat) : Prop := 8 * 32 ≤ r.1 ∨ r = (8 * Impl.Bignum.X86_64.Public.sMask, 8) ∨ r = (8 * sMo, 8)

theorem Mut.ofSlot (w j : Nat) (n : Nat) : Mut (Bignum.slot w j, n) :=
  Or.inl (by unfold Bignum.slot hdrBytes; omega)

theorem Ws.congr {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, Mut r) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs) : Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    have hi' : i < 16 ∨ i = 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      rcases hm r hr with h | rfl | rfl
      · omega
      · simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega
      · simp only [sMo, sFn]; omega) (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide)
                                         have := h.hZ; omega)
  exact ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩

theorem Ws.good {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    Good s B Z w (word s.mem B (8 * sMinv)) ∧ slot w 8 ≤ Z :=
  ⟨⟨h.scr, h.rdi, ⟨h.hw, rfl, h.harr⟩⟩, Nat.le_trans (by unfold slot; omega) h.hZ⟩

theorem Ws.h256 {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) : 8 * 32 ≤ Z := by
  have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega

theorem Ws.sl {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) h.hZ

/-- `ws`, from the working space. -/
theorem Ws.ws_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block ws) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        Keep [.r12, .r9] s t :=
  VG.Proof.Rsa.X86_64.ws_ok h.scr h.rdi h.h256 h.hw h.hS

/-! ## Clearing and copying -/

/-- `zeroA j`: `[j] := 0` (`w + 2` words). -/
theorem zeroA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (zeroA j) s fun t =>
      wv t.mem B (slot w j) (w + 2) = 0 ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        Keep [.r12, .r9, .r8, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold zeroA
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base_ok j (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_))
  refine WP.mono (zeroAccLoop_ok (h.scr.congr (k₁.trans k₂).2.2) h8 ((k₂.gpr (by decide)).trans h12)
    (by have := h.w1; omega) (by have := h.w2; omega) (by omega)) fun t ⟨hz, o, k₃⟩ => ?_
  rw [m₂, m₁] at o
  exact ⟨hz, o, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `copyA o a`: `[o] := [a]` over `w` words. -/
theorem copyA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w a) w ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧
        Keep [.r12, .r9, .rsi, .rbx, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have sp := slot_far (w := w) hoa
  unfold copyA
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok a o (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hsi, hbx, m₂, k₂⟩ => ?_))
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (copyWords_ok hsi hbx ((k₂.gpr (by decide)).trans h12) (by have := h.w1; omega)
    (by have := h.w2; omega) (by omega) (fun i hi => hs₂.ld (by omega)) (fun i hi => hs₂.st (by omega))
    (fun i hi b hb => by rw [ofs_off B (by omega)]; omega)) fun t ⟨hv, _, o', k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  exact ⟨hv, o', ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-! ## Bytes -/

/-- `loadA j sPtr sLen`: `[j] := ` the `len` bytes at `p`, most significant
first, over `w` words. -/
theorem loadA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = p) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s B Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      wv t.mem B (slot w j) w = Spec.Rsa.os2ip bs ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .rsi, .rcx, .rdx, .rbp] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [loadA, seqs]
  refine WP.seq (WP.mono (zeroA_ok h hj) fun s₁ ⟨hz, o₁, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w j _) k₁ (by decide)
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    o₁.word (Or.inl (by have := hdr_lt_slot w j hi; omega)) (by omega)
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = p ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h₁.rdi
          have hs₃ := h₁.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hh sPtr hP, hh sLen hL, hp, hl]) rfl)
      fun s₄ ⟨⟨hsi, hcx, m₄⟩, k₄⟩ => ?_)))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.scr.congr k14.2.2
  have hsrc₄ : Src s₄ B Z p bs := hsrc.congrK (fun x hx => by
    rw [m₄, m₃, m₂]; exact o₁ x (Or.inr (by omega))) k14
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) hs₄ hsi hcx ((k₄.gpr (by decide)).trans hbx) hlen hl1 (by omega) rfl
    (by omega) (fun i hi => hsrc₄.rd i (by omega)) (fun i hi => hsrc₄.val i (by omega))
    (fun i hi => Or.inr (by have := hsrc₄.out i (by omega); omega))) fun t ⟨hv, o, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at o
  refine ⟨?_, fun x hx => by rw [o x (by omega), o₁ x hx], (k14.trans k₅).mono (by simp)⟩
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
      Keep [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [storeA, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ =>
    WP.mono (base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx, .r15] (Q := fun t => t.gpr .rsi = out ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .r15 = mask c ∧ t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hl₃ sMsk hM, hp, hl, hm]) rfl)
      fun s₄ ⟨⟨hsi, hcx, h15, m₄⟩, k₄⟩ => ?_)))
  have k24 := (k₂.trans k₃).trans k₄
  refine WP.mono (storeBE_ok (w := (len + 7) / 8) (h.scr.congr k24.2.2) ((k₄.gpr (by decide)).trans hbx) hsi hcx h15
    hl1 (by omega) rfl (by omega) (fun i hi => by rw [k24.2.2]; exact hout i hi) hsep)
    fun t ⟨hb, hx, hwr, hrd, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at hb hx
  exact ⟨hb, hx, hwr.trans k24.2.2, hrd.trans k24.2.1, (k24.trans k₅).mono (by simp)⟩

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

end VG.Proof.Rsa.X86_64
