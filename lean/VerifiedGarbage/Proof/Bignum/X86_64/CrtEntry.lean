import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Spec.Rsa.Contract
import Mathlib.Data.Int.GCD

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame`. -/
section

/-!
# Multiword arithmetic on x86-64: workspaces within a working space

`vg_rsa_private_crt` keeps three workspaces in its working space, at
offsets of the first one's base `B`. What code in a workspace at `off B o`
changes is stated at its own base (`Arrays`, `Outside`, `Frm`); these
lemmas restate it at `B`, with the ranges moved by `o` (`Frm.rebase`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- The offset from `off B o` of an address at offset `d ≥ o` from `B`, or
an offset at least `2^64 - o` for one below `o`. -/
theorem ofs_rebase (B x : Addr) {o : Nat} (ho : o < 2 ^ 64) :
    (o ≤ VG.Proof.Bignum.X86_64.ofs B x ∧ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off B o) x = VG.Proof.Bignum.X86_64.ofs B x - o) ∨ (VG.Proof.Bignum.X86_64.ofs B x < o ∧ 2 ^ 64 - o ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off B o) x) := by
  simp only [VG.Proof.Bignum.X86_64.ofs, VG.Proof.Bignum.X86_64.off]
  rw [Offset.toNat_sub_add x B ho]
  have := (x - B).isLt
  by_cases h : o ≤ (x - B).toNat
  · left
    refine ⟨h, ?_⟩
    rw [show 2 ^ 64 - o + (x - B).toNat = (x - B).toNat - o + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Ranges at `off B o`, at `B`. -/
def shiftRanges (o : Nat) (rs : List (Nat × Nat)) : List (Nat × Nat) := rs.map fun r => (o + r.1, r.2)

theorem Frm.rebase {B : Addr} {o : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (VG.Proof.Bignum.X86_64.off B o) rs m m')
    (ho : o < 2 ^ 64) (hr : ∀ r ∈ rs, o + r.1 + r.2 ≤ 2 ^ 64) : Frm B (VG.Proof.Bignum.X86_64.shiftRanges o rs) m m' := by
  intro x hx
  apply h x
  intro r hr'
  have hx' := hx (o + r.1, r.2) (List.mem_map.mpr ⟨r, hr', rfl⟩)
  have := hr r hr'
  rcases VG.Proof.Bignum.X86_64.ofs_rebase B x ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at hx'; omega
  · omega

theorem Frm.of_arrays_off {B : Addr} {o w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays (VG.Proof.Bignum.X86_64.off B o) w js m m')
    (ho : o < 2 ^ 64) (hw : ∀ j ∈ js, o + VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ 2 ^ 64) :
    Frm B (VG.Proof.Bignum.X86_64.shiftRanges o (js.map fun j => (VG.Proof.Bignum.X86_64.slot w j, 8 * (w + 2)))) m m' :=
  Frm.rebase (Frm.of_arrays h fun j hj => List.mem_map.mpr ⟨j, hj, rfl⟩) ho fun r hr => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    exact hw j hj

theorem Frm.of_outside_off {B : Addr} {o d n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B o) d n m m')
    (ho : o < 2 ^ 64) (hd : o + d + n ≤ 2 ^ 64) : Frm B [(o + d, n)] m m' :=
  Frm.rebase (rs := [(d, n)]) (Frm.of_outside h (List.mem_singleton.mpr rfl)) ho fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd

/-- Two changes, each within ranges of its own, change only within both. -/
theorem Frm.append {B : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : Frm B rs m₁ m₂)
    (h₂ : Frm B rs' m₂ m₃) : Frm B (rs ++ rs') m₁ m₃ := fun x hx =>
  (h₂ x fun r hr => hx r (List.mem_append_right _ hr)).trans (h₁ x fun r hr => hx r (List.mem_append_left _ hr))

/-- A word of a workspace at `off B o`, at `B`. -/
theorem word_off (m : Mem) (B : Addr) (o d : Nat) : VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) d = VG.Proof.Bignum.X86_64.word m B (o + d) := by
  simp only [VG.Proof.Bignum.X86_64.word, off_off]

theorem wv_off (m : Mem) (B : Addr) (o d k : Nat) : wv m (VG.Proof.Bignum.X86_64.off B o) d k = wv m B (o + d) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wv, wv, ih, VG.Proof.Bignum.X86_64.word_off, Nat.add_assoc]

/-- Below `off B o`: a change within `L` bytes of `off B o` keeps the
words at offsets below `o` from `B`. -/
theorem Frm.word_below {B : Addr} {o L : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (VG.Proof.Bignum.X86_64.off B o) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (hL : o + L ≤ 2 ^ 64) (ho : o < 2 ^ 64) {d : Nat} (hd : d + 8 ≤ o) :
    VG.Proof.Bignum.X86_64.word m' B d = VG.Proof.Bignum.X86_64.word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun r hr' => by
    have := hr r hr'
    rcases VG.Proof.Bignum.X86_64.ofs_rebase B (VG.Proof.Bignum.X86_64.off B d + BitVec.ofNat 64 i) ho with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)] at h1; omega
    · omega).symm).symm

theorem Frm.wv_below {B : Addr} {o L : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (VG.Proof.Bignum.X86_64.off B o) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (hL : o + L ≤ 2 ^ 64) (ho : o < 2 ^ 64) {d k : Nat} (hd : d + 8 * k ≤ o) :
    wv m' B d k = wv m B d k :=
  wv_congr fun i hi => h.word_below hr hL ho (by omega)

/-! ## A prime's workspace -/

/-- The size of the window's table after a prime's arrays: 16 entries of
`8 (w_X + 2)` bytes. -/
def tabBytes (wx : Nat) : Nat := 16 * (8 * (wx + 2))

open VG.Impl.Bignum.X86_64.Public in
/-- A prime's workspace at `off B o` (`wx` words), its base in `rdi`,
after the modulus' at `B` (`w` words) in the working space, its header
linking back to `B`. -/
structure SubCtx (t : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  rdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off B o
  hdr : Hdr t.mem (VG.Proof.Bignum.X86_64.off B o) wx minv
  link : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sLink) = B
  nw : VG.Proof.Bignum.X86_64.word t.mem B (8 * sW) = BitVec.ofNat 64 w
  narr : ∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)
  lo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o
  hi : o + VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx ≤ Z

theorem SubCtx.good {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv) :
    Good t (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx 8) wx minv :=
  ⟨h.scr.sub (by have := h.hi; omega) (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega), h.rdi, h.hdr⟩

/-- The prime's workspace with its table. -/
theorem SubCtx.scrT {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv) :
    VG.Proof.Bignum.X86_64.Scr t (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx) :=
  h.scr.sub (by have := h.hi; omega) (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega)

/-- What changes within the arrays and the functions' own slots of the
prime's workspace (but its link) keeps it. -/
theorem SubCtx.of_frmT {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hf : Frm (VG.Proof.Bignum.X86_64.off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hL : o + (VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx) ≤ 2 ^ 64 := by omega
  have hr' : ∀ r ∈ rs, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx := fun r hr' => (hr r hr').2
  have hh : ∀ i < 17, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega))
      (by have : 8 * 32 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
          omega)
  have hb : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes at hL; omega) (by have := hdr_lt_slot w 8 hi'; have := h.lo; omega)
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), h.lo, h.hi⟩

theorem SubCtx.of_frm {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hf : Frm (VG.Proof.Bignum.X86_64.off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv :=
  h.of_frmT hf (fun r hr' => ⟨(hr r hr').1, by have := (hr r hr').2; omega⟩) hwr hdi

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks`. -/
section

/-!
# `vg_rsa_private_crt` on x86-64: small pieces of the checks

`zeroArr j` clears array `j` (`zeroArr_ok`), `copyArr o a` copies `[a]` to
`[o]` (`copyArr_ok`), `maskArr j` ands `[j]` with the mask in `sMaskX`
(`maskArr_ok`); `eqCheck` ands into `sMask` the mask of `p q = n`
(`eqCheck_ok`), and `qinvCheck`, in `p`'s workspace, that of `qInv < p`
(`qinvCheck_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## Clearing, copying and masking an array -/

/-- `[j] := 0` over `w + 2` words. -/
theorem zeroArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) :
    WP isa (Crt.zeroArr j) s fun t => wv t.mem B (VG.Proof.Bignum.X86_64.slot w j) (w + 2) = 0 ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) (8 * (w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold Crt.zeroArr
  refine WP.seq (WP.mono (WP.keep [.r8, .r12] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sW (by decide),
      hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun s₁ ⟨⟨h8, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroAccLoop_ok (hg.scr.congr k₁.2.2) h8 h12 hw hw' (Nat.le_trans (slot_le hj) hZ))
    fun t ⟨hv, ho, k⟩ => ⟨hv, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩

/-- `[o] := [a]` over `w` words. -/
theorem copyArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {o a : Nat} (ho : o < 8) (ha : a < 8) (hoa : o ≠ a) :
    WP isa (seqs (Crt.copyArr o a)) s fun t => wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w o) (8 * w) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have so := Nat.le_trans (slot_le (w := w) ho) hZ
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sp := slot_sep (w := w) hoa
  unfold Crt.copyArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr o) (by unfold sArr; omega), hl sW (by decide), hg.hdr.harr a ha, hg.hdr.harr o ho,
      hg.hdr.hw]) rfl) fun s₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega) (fun i hi => hs₁.ld (by omega))
    (fun i hi => hs₁.st (by omega)) (fun i hi b hb => by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega))
    fun t ⟨hv, _, ho', k⟩ => ⟨by rw [hv, hm₁], by rw [hm₁] at ho'; exact ho', (k₁.trans k).mono (by decide)⟩

/-- After `j` words of `maskArr`'s loop from `s₀`. -/
structure MaskInv (s₀ : State) (B : Addr) (Z e : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B e (8 * j) s₀.mem t.mem
  done : ∀ i < j, VG.Proof.Bignum.X86_64.word t.mem B (e + 8 * i) = VG.Proof.Bignum.X86_64.word s₀.mem B (e + 8 * i) &&& VG.Proof.Bignum.X86_64.mask c

theorem maskStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {c : Bool}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B e) (h15 : s₀.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : VG.Proof.Bignum.X86_64.MaskInv s₀ B Z e c j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax] :
        List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.MaskInv s₀ B Z e c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B e := (hI.keep.gpr (by decide)).trans hbx
  have t15 : t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hv : VG.Proof.Bignum.X86_64.word t.mem B (e + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (e + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j)) (VG.Proof.Bignum.X86_64.word s₀.mem B (e + 8 * j) &&& VG.Proof.Bignum.X86_64.mask c)) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, t15, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega), hv]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    fun i hi => ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _

/-- `[j] &= sMaskX` over `w` words. -/
theorem maskArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) {c : Bool}
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * Crt.sMaskX) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (seqs (Crt.maskArr j)) s fun t =>
      (∀ i < w, VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w j + 8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w j + 8 * i) &&& VG.Proof.Bignum.X86_64.mask c) ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w j) w = (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w else 0) ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) (8 * w) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sj := Nat.le_trans (slot_le (w := w) hj) hZ
  unfold Crt.maskArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl Crt.sMaskX (by decide),
      hl (sArr j) (by unfold sArr; omega), hl sW (by decide), hm, hg.hdr.harr j hj,
      hg.hdr.hw]) rfl) fun s₁ ⟨⟨h15, h12, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.MaskInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w j) c 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (VG.Proof.Bignum.X86_64.MaskInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w j) c) h0
    (fun i _ hi t hI => VG.Proof.Bignum.X86_64.maskStep_ok hbx h15 h12 (by omega) (by omega) hi hI)) fun t hI => ?_
  have hd := hI.done
  have ho := hI.out
  rw [hm₁] at hd ho
  refine ⟨hd, ?_, ho, (k₁.trans hI.keep).mono (by decide)⟩
  cases c
  · exact (wv_eq_zero_iff _ _ _ _).mpr fun i hi => by rw [hd i hi, mask_false]; exact BitVec.and_zero
  · exact wv_congr fun i hi => by rw [hd i hi, mask_true, BitVec.and_allOnes]

/-! ## `p q = n` -/

/-- Two numbers of `n` words are equal only if their words are. -/
theorem wv_inj {m : Mem} {p : Addr} {d e : Nat} :
    ∀ n, wv m p d n = wv m p e n → ∀ i < n, VG.Proof.Bignum.X86_64.word m p (d + 8 * i) = VG.Proof.Bignum.X86_64.word m p (e + 8 * i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    simp only [wv] at h
    have hd := wv_lt m p d n
    have he := wv_lt m p e n
    have h1 : wv m p d n = wv m p e n := by
      have := congrArg (· % 2 ^ (64 * n)) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at this
      exact this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact VG.Proof.Bignum.X86_64.wv_inj n h1 i hi
    · rw [h1] at h
      exact BitVec.eq_of_toNat_eq (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel h))

theorem split_eq_iff {L H N R : Nat} (hN : N < R) : L + R * H = N ↔ L = N ∧ H = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · rw [Nat.mul_zero, Nat.add_zero] at h; exact ⟨h, rfl⟩
    · have := Nat.le_mul_of_pos_right R hH; omega
  · rintro ⟨rfl, rfl⟩
    rw [Nat.mul_zero, Nat.add_zero]

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := BitVec.or_eq_zero_iff

theorem xor_eq_zero (a b : BitVec 64) : a ^^^ b = 0 ↔ a = b := BitVec.xor_eq_zero_iff

/-- After `j` words of a loop that ORs words into `rbp`, memory unchanged:
`rbp = 0` iff `P j`. -/
structure OrInv (s₀ : State) (B : Addr) (Z : Nat) (P : Nat → Prop) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  val : t.gpr .rbp = 0 ↔ P j

theorem xorStep_ok {s₀ : State} {B : Addr} {Z w eA eN : Nat}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B eA) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : VG.Proof.Bignum.X86_64.OrInv s₀ B Z (fun j => ∀ i < j, VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * i) = VG.Proof.Bignum.X86_64.word s₀.mem B (eN + 8 * i)) j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)),
        .alu .or .rbp (.reg .rax)] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] :
        List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧
        VG.Proof.Bignum.X86_64.OrInv s₀ B Z (fun j => ∀ i < j, VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * i) = VG.Proof.Bignum.X86_64.word s₀.mem B (eN + 8 * i)) (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .rbp = t.gpr .rbp ||| (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j) ^^^ VG.Proof.Bignum.X86_64.word t.mem B (eN + 8 * j))) ?_ rfl)
    fun t₁ ⟨⟨hm, hbp⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega)]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ?_⟩
  rw [(k'.gpr (by decide) : t'.gpr .rbp = t₁.gpr .rbp), hbp, VG.Proof.Bignum.X86_64.or_eq_zero, VG.Proof.Bignum.X86_64.xor_eq_zero,
    hI.val, hI.mem]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    exacts [h1 i hi, h2]
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩

theorem orStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B e) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : VG.Proof.Bignum.X86_64.OrInv s₀ B Z (fun j => A ∧ ∀ i < j, VG.Proof.Bignum.X86_64.word s₀.mem B (e + 8 * i) = 0) j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧
        VG.Proof.Bignum.X86_64.OrInv s₀ B Z (fun j => A ∧ ∀ i < j, VG.Proof.Bignum.X86_64.word s₀.mem B (e + 8 * i) = 0) (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B e := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .rbp = t.gpr .rbp ||| word t.mem B (e + 8 * j)) ?_ rfl)
    fun t₁ ⟨⟨hm, hbp⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega)]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ?_⟩
  rw [(k'.gpr (by decide) : t'.gpr .rbp = t₁.gpr .rbp), hbp, VG.Proof.Bignum.X86_64.or_eq_zero, hI.val, hI.mem]
  constructor
  · rintro ⟨⟨hA, h1⟩, h2⟩
    refine ⟨hA, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    exacts [h1 i hi, h2]
  · rintro ⟨hA, h⟩
    exact ⟨⟨hA, fun i hi => h i (by omega)⟩, h j (by omega)⟩

/-- `cmp rbp, 1; sbb rbp, rbp`: all ones iff `rbp` was zero. -/
theorem decide_lt_one (x : BitVec 64) : decide (x.toNat < (1 : BitVec 64).toNat) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj,
    show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

/-- The mask of `p q = n` (the accumulator's `2 w + 2` words against
`aN`'s `w`), and'ed into `sMask`. -/
theorem eqCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30) :
    WP isa (seqs Crt.eqCheck) s fun t =>
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.word s.mem B (8 * sMask) &&&
        VG.Proof.Bignum.X86_64.mask (decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) (2 * w + 2) = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w)) ∧
      VG.Proof.Bignum.X86_64.Outside B (8 * sMask) 8 s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hA : VG.Proof.Bignum.X86_64.slot w aAcc + 16 * (w + 2) ≤ Z := by
    have := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ; simp only [VG.Proof.Bignum.X86_64.slot, aTmp, aAcc] at this ⊢; omega
  have hN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hS := hdr_lt_slot w aN (show sMask < 32 by decide)
  unfold Crt.eqCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) ∧ t.gpr .rbp = 0 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aAcc) (by decide),
      hl (sArr aN) (by decide), hg.hdr.hw, hg.hdr.harr aAcc (by decide), hg.hdr.harr aN (by decide)]) rfl)
    fun s₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.OrInv s₁ B Z (fun j => ∀ i < j, VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 8 * i) = VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN + 8 * i))
        0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) (by omega) _ h0
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.xorStep_ok hbx h10 h12 (by omega) (by omega) (by omega) hj hI)) fun s₂ hI => ?_)
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have s₂bx : s₂.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) := (hI.keep.gpr (by decide)).trans hbx
  refine WP.seq (WP.mono (WP.keep [.rax, .rbx, .r12] (Q := fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 8 * w) ∧
      t.gpr .r12 = BitVec.ofNat 64 (w + 2) ∧ t.mem = s₂.mem) (by
      xrun [s₂12, s₂bx]
      refine ⟨?_, by rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]⟩
      simp only [VG.Proof.Bignum.X86_64.off, BitVec.ofNat_add_ofNat, BitVec.add_assoc]
      congr 2; omega) rfl)
    fun s₃ ⟨⟨hbx₃, h12₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have h0' : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₃.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₃ t → t.cf = s₃.cf →
      VG.Proof.Bignum.X86_64.OrInv s₃ B Z (fun j => (∀ i < w, VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 8 * i) = VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN + 8 * i)) ∧
        ∀ i < j, VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 8 * w + 8 * i) = 0) 0 t := fun t h14 hm k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₃.gpr .rbp), (k₃.gpr (by decide) : s₃.gpr .rbp = s₂.gpr .rbp),
        hI.val]
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w + 2) (by omega) (by omega) _ h0'
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.orStep_ok hbx₃ h12₃ (by omega) (by omega) hj hI)) fun s₄ hI₂ => ?_)
  have hm₄ : s₄.mem = s.mem := hI₂.mem.trans (hm₃.trans (hI.mem.trans hm₁))
  have hdi₄ : s₄.gpr .rdi = B :=
    ((((k₁.trans hI.keep).trans k₃).trans hI₂.keep).gpr (by decide)).trans hg.rdi
  refine WP.mono (WP.keep [.rbp] (Q := fun t => ∃ b : Bool, b = decide (s₄.gpr .rbp = 0) ∧
      t.mem = s₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) (VG.Proof.Bignum.X86_64.mask b &&& VG.Proof.Bignum.X86_64.word s₄.mem B (8 * sMask)))
    (by
      xrun [State.ea, hdr, hdi₄, hdrOff, hI₂.scr.ld (show 8 * sMask + 8 ≤ Z by omega),
        hI₂.scr.st (show 8 * sMask + 8 ≤ Z by omega)]
      exact ⟨_, VG.Proof.Bignum.X86_64.decide_lt_one _, rfl⟩) rfl) fun t ⟨⟨b, hb, hm⟩, k₄⟩ => ?_
  have hR : b = decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) (2 * w + 2) = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w) := by
    rw [hb, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hI₂.val, hm₃, hI.mem, hm₁,
      show 2 * w + 2 = w + (w + 2) by omega, wv_add, VG.Proof.Bignum.X86_64.split_eq_iff (wv_lt _ _ _ _), wv_eq_zero_iff]
    exact and_congr ⟨fun h => wv_congr2 h, fun h => VG.Proof.Bignum.X86_64.wv_inj w h⟩ Iff.rfl
  refine ⟨?_, ?_, ((((k₁.trans hI.keep).trans k₃).trans hI₂.keep).trans k₄).mono (by decide)⟩
  · rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self, hm₄, BitVec.and_comm, hR]
  · rw [hm, ← hm₄]
    exact VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)

/-! ## `qInv < p` -/

/-- In a workspace at `off B o` linked to `B`: the mask of `qInv < p`
(`[aChunk] < [aN]`), and'ed into the `sMask` of the workspace at `B`. -/
theorem qinvCheck_ok {s : State} {B : Addr} {Z w o : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off B o) (hH : Hdr s.mem (VG.Proof.Bignum.X86_64.off B o) w minv) (hZ : o + VG.Proof.Bignum.X86_64.slot w 8 ≤ Z)
    (hM : 8 * sMask + 8 ≤ o) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hL : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sLink) = B) :
    WP isa (seqs Crt.qinvCheck) s fun t =>
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.word s.mem B (8 * sMask) &&&
        VG.Proof.Bignum.X86_64.mask (decide (wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot w Crt.aChunk) w < wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot w aN) w)) ∧
      VG.Proof.Bignum.X86_64.Outside B (8 * sMask) 8 s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hs' : VG.Proof.Bignum.X86_64.Scr s (VG.Proof.Bignum.X86_64.off B o) (Z - o) := hs.sub (by omega) (by omega)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi =>
    hs'.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hC := slot_le (w := w) (show Crt.aChunk < 8 by decide)
  have hN := slot_le (w := w) (show aN < 8 by decide)
  unfold Crt.qinvCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot w Crt.aChunk) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot w aN) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr Crt.aChunk) (by decide),
      hl (sArr aN) (by decide), hH.hw, hH.harr Crt.aChunk (by decide), hH.harr aN (by decide)]) rfl)
    fun s₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hs'.congr k₁.2.2) hbx h10 h12 hbp hw hw' (by omega) (by omega))
    fun s₂ ⟨hbp₂, hm₂, k₂⟩ => ?_)
  rw [hm₁] at hbp₂
  have k12 := k₁.trans k₂
  have hdi₂ : s₂.gpr .rdi = VG.Proof.Bignum.X86_64.off B o := (k12.gpr (by decide)).trans hdi
  have hs₂ := hs.congr k12.2.2
  have hL₂ : VG.Proof.Bignum.X86_64.word s₂.mem (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sLink) = B := by rw [hm₂, hm₁]; exact hL
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
      t.mem = s₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) (s₂.gpr .rbp &&& VG.Proof.Bignum.X86_64.word s₂.mem B (8 * sMask)))
    (by xrun [State.ea, hdr, Crt.ws, hdi₂, hdrOff, (hs'.congr k12.2.2).ld (d := 8 * Crt.sLink) (by
      have := hdr_lt_slot w 8 (show Crt.sLink < 32 by decide); omega), hL₂,
      hs₂.ld (show 8 * sMask + 8 ≤ Z by omega), hs₂.st (show 8 * sMask + 8 ≤ Z by omega)]) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  refine ⟨?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self, hbp₂, hm₂, hm₁, BitVec.and_comm]
  · rw [hm, hm₂, hm₁]; exact VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubSetup`. -/
section

/-!
# `vg_rsa_public` on x86-64: the setup

From the header that `entry` leaves, `w = ⌈k / 8⌉`, the arrays' bases,
`m` and the input loaded, the mask of `input < m`, `-m⁻¹` and the number 1
(`setup_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-! ## Frames -/

/-- Memory that changes only in the working space. -/
def InScr (B : Addr) (Z : Nat) (m m' : Mem) : Prop := ∀ x, Z ≤ VG.Proof.Bignum.X86_64.ofs B x → m' x = m x

theorem InScr.refl (B : Addr) (Z : Nat) (m : Mem) : VG.Proof.Bignum.X86_64.InScr B Z m m := fun _ _ => rfl

theorem InScr.trans {B : Addr} {Z : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Bignum.X86_64.InScr B Z m₁ m₂) (h₂ : VG.Proof.Bignum.X86_64.InScr B Z m₂ m₃) :
    VG.Proof.Bignum.X86_64.InScr B Z m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem InScr.of_outside {B : Addr} {Z o n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside B o n m m') (hZ : o + n ≤ Z) :
    VG.Proof.Bignum.X86_64.InScr B Z m m' := fun x hx => h x (Or.inr (by omega))

theorem InScr.of_frm {B : Addr} {Z : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : VG.Proof.Bignum.X86_64.InScr B Z m m' :=
  fun x hx => h x fun r hr => Or.inr (by have := hZ r hr; omega)

theorem InScr.of_arrays {B : Addr} {Z w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hjs : ∀ j ∈ js, j < 8) : VG.Proof.Bignum.X86_64.InScr B Z m m' :=
  fun x hx => h x fun j hj => Or.inr (by have := slot_le (w := w) (hjs j hj); omega)

/-- The header slots read on exit and by the setup: the saved registers and
the arguments. -/
def Fixed (B : Addr) (m m' : Mem) : Prop :=
  ∀ i, i < 6 ∨ (16 ≤ i ∧ i < 22) → VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i)

theorem Fixed.refl (B : Addr) (m : Mem) : VG.Proof.Bignum.X86_64.Fixed B m m := fun _ _ => rfl

theorem Fixed.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Bignum.X86_64.Fixed B m₁ m₂) (h₂ : VG.Proof.Bignum.X86_64.Fixed B m₂ m₃) :
    VG.Proof.Bignum.X86_64.Fixed B m₁ m₃ := fun i hi => (h₂ i hi).trans (h₁ i hi)

theorem Fixed.of_outside {B : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside B o n m m')
    (ho : 8 * 22 ≤ o ∨ (8 * 6 ≤ o ∧ o + n ≤ 8 * 16)) : VG.Proof.Bignum.X86_64.Fixed B m m' :=
  fun _ hi => h.word (by omega) (by omega)

theorem Fixed.of_frm {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (ho : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16)) : VG.Proof.Bignum.X86_64.Fixed B m m' :=
  fun _ hi => h.word_eq (fun r hr => by have := ho r hr; omega) (by omega)

theorem Fixed.of_arrays {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') :
    VG.Proof.Bignum.X86_64.Fixed B m m' :=
  fun i hi => h.word_eq (fun j _ => Or.inl (by have := hdr_lt_slot w j (show i < 32 by omega); omega))
    (by omega)

theorem Fixed.store (m : Mem) (B : Addr) {i : Nat} (v : BitVec 64) (hi : 6 ≤ i) (hi' : i < 32)
    (hi'' : i < 16 ∨ 22 ≤ i) : VG.Proof.Bignum.X86_64.Fixed B m (m.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) :=
  Fixed.of_outside (VG.Proof.Bignum.X86_64.writeW_outside m B v (by omega)) (by omega)

/-! ## `w` -/

theorem shr3_w (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  rw [sx7, show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The first block: `w`, the bases, and `m`'s base and pointer. -/
theorem setupHead_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32)
    (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * sN) = np) :
    WP isa (.block (([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7),
      .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++ setBases ++
      ([.mov .rsi (.mem (hdr sN)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rsi = np ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rbx, .rsi, .r12] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sW)) (BitVec.ofNat 64 ((k + 7) / 8))) ?_ rfl)
    fun t₁ ⟨⟨h12, hcx, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sK) (by unfold sK sFn; omega),
      hs.st (d := 8 * sW) (by unfold sW; omega), hK, VG.Proof.Bignum.X86_64.shr3_w k hk]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hN₂ : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sN) = np := by
    rw [ho₂.word (by unfold sN sFn sArr; omega) (by omega), hm₁,
      (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by unfold sN sW sFn; omega) (by omega)]; exact hN
  have hW₂ : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₂.word (by unfold sW sArr; omega) (by omega), hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = np ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ∧ t.mem = t₂.mem) ?_ rfl) fun t ⟨⟨hsi, hbx, hm⟩, k₃⟩ => ?_
  · xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₂.ld (d := 8 * sArr aN) (by omega), hN₂, hb₂ aN (by decide)]
  refine ⟨(k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12),
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hcx), hsi, hbx, by rw [hm]; exact hW₂,
    fun j hj => by rw [hm]; exact hb₂ j hj, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [hm]
  exact (Frm.of_outside (by rw [hm₁] at *; exact VG.Proof.Bignum.X86_64.writeW_outside s.mem B _ (by omega)) (by simp)).trans
    (Frm.of_outside ho₂ (by simp))

/-! ## Sequences -/

theorem wp_seqs_append {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa (seqs a) s fun t => WP isa (seqs b) t Q) : WP isa (seqs (a ++ b)) s Q := by
  induction a generalizing s with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact WP.seq h
    | cons d rest =>
      simp only [seqs, List.cons_append] at h ⊢
      exact WP.seq (WP.mono (WP.seq_iff.mp h) fun t ht => ih (by simp) ht)

/-! ## Byte strings outside the working space -/

/-- The bytes `bs` at `p`, readable, outside the working space. -/
structure Src (s : State) (B : Addr) (Z : Nat) (p : Addr) (bs : List Byte) : Prop where
  rd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1
  val : ∀ i (h : i < bs.length), s.mem (p + BitVec.ofNat 64 i) = bs[i]
  out : ∀ i < bs.length, Z ≤ VG.Proof.Bignum.X86_64.ofs B (p + BitVec.ofNat 64 i)

theorem Src.congr {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : VG.Proof.Bignum.X86_64.Src s B Z p bs)
    (hm : VG.Proof.Bignum.X86_64.InScr B Z s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : VG.Proof.Bignum.X86_64.Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm _ (h.out i hi)]; exact h.val i hi, h.out⟩

theorem Src.congrK {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} {rs : List Reg}
    (h : VG.Proof.Bignum.X86_64.Src s B Z p bs) (hm : VG.Proof.Bignum.X86_64.InScr B Z s.mem t.mem) (k : VG.Proof.MlKem.X86_64.Keep rs s t) : VG.Proof.Bignum.X86_64.Src t B Z p bs :=
  h.congr hm k.2.1 k.2.2

/-- `loadBE` of bytes outside the working space into array `j`. -/
theorem loadArr_ok {s : State} {B : Addr} {Z k : Nat} {p : Addr} {bs : List Byte} {j : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hj : j < 8) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hsrc : VG.Proof.Bignum.X86_64.Src s B Z p bs) (hk : bs.length = k) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (hsi : s.gpr .rsi = p) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j)) :
    WP isa loadBE s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) ((k + 7) / 8) = Spec.Rsa.os2ip bs ∧
      Arrays B ((k + 7) / 8) [j] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s t := by
  have := slot_le (w := (k + 7) / 8) hj
  refine WP.mono (loadBE_ok hs hsi hcx hbx hk hk1 hk' rfl (by omega) (fun i hi => hsrc.rd i (by omega))
    (fun i hi => hsrc.val i (by omega)) (fun i hi => Or.inr (by have := hsrc.out i (by omega); omega)))
    fun t ⟨h1, h2, h3⟩ => ⟨h1, Arrays.of_outside (List.mem_singleton_self j) h2 (Nat.le_refl _) (by omega), h3⟩

/-! ## The steps of the setup -/

/-- `w`, the bases, `m` and the input. -/
def loadSteps : List (Prog isa) := [.block ([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7),
      .shift .shr .r12 3, .store (hdr sW) .r12] ++ setBases ++
      [.mov .rsi (.mem (hdr sN)), .mov .rbx (.mem (hdr (sArr aN)))]),
      loadBE,
      .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
      loadBE]

/-- The mask of `input < m`, `-m⁻¹` and the number 1. -/
def restSteps : List (Prog isa) := [.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
        .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
        cfToRbp],
      .block ([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] ++ minv ++
        [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
      setWord aOne .rcx]

/-- What the loads change. -/
def loadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (VG.Proof.Bignum.X86_64.slot w aN, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aX, 8 * (w + 2))]

theorem Frm.of_arrays1 {B : Addr} {w j : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Arrays B w [j] m m')
    (hr : (VG.Proof.Bignum.X86_64.slot w j, 8 * (w + 2)) ∈ rs) : Frm B rs m m' :=
  Frm.of_arrays h fun _ hj => (List.mem_singleton.mp hj) ▸ hr

/-- `w`, the bases, `m` into array `aN` and the input into `aX`. -/
theorem setupLoad_ok {s : State} {B : Addr} {Z k : Nat} {np ip : Addr} {nb xb : List Byte} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk : k < 2 ^ 31)
    (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * sN) = np)
    (hIn : VG.Proof.Bignum.X86_64.word s.mem B (8 * sIn) = ip) (hnb : VG.Proof.Bignum.X86_64.Src s B Z np nb) (hxb : VG.Proof.Bignum.X86_64.Src s B Z ip xb)
    (hnl : nb.length = k) (hxl : xb.length = k) :
    WP isa (seqs VG.Proof.Bignum.X86_64.loadSteps) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j)) ∧
      Frm B (VG.Proof.Bignum.X86_64.loadRanges ((k + 7) / 8)) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eW : sW = 6 := rfl
  have eIn : sIn = 21 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAX : sArr aX = 9 := rfl
  unfold VG.Proof.Bignum.X86_64.loadSteps
  have hsl : ∀ r ∈ VG.Proof.Bignum.X86_64.loadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := by
    have := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show aX < 8 by decide)
    simp only [VG.Proof.Bignum.X86_64.loadRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [eW, eA] <;> omega
  have hhd : ∀ i, 8 * i + 8 ≤ 8 * sW ∨ (16 ≤ i ∧ i < 32) →
      ∀ r ∈ VG.Proof.Bignum.X86_64.loadRanges ((k + 7) / 8), 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i hi
    have := hdr_lt_slot ((k + 7) / 8) aN (i := i) (by omega)
    have := hdr_lt_slot ((k + 7) / 8) aX (i := i) (by omega)
    simp only [VG.Proof.Bignum.X86_64.loadRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [eW, eA] at * <;> omega
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.setupHead_ok hs hdi hZ (by omega) hK hN)
    fun t₁ ⟨h12, hcx, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (VG.Proof.Bignum.X86_64.loadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [VG.Proof.Bignum.X86_64.loadRanges])
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.loadArr_ok hs₁ (by decide) hZ (hnb.congrK (InScr.of_frm hf₁' hsl) k₁) hnl (by omega)
    hk hsi hcx hbx) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hf₂ : Frm B (VG.Proof.Bignum.X86_64.loadRanges ((k + 7) / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays1 ha₂ (by simp [VG.Proof.Bignum.X86_64.loadRanges]))
  have hw₂ : ∀ i, 8 * i + 8 ≤ 8 * sW ∨ (16 ≤ i ∧ i < 32) → VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) :=
    fun i hi => hf₂.word_eq (hhd i hi) (by omega)
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have hb₂ : ∀ j < 8, VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) := fun j hj => by
    rw [ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = ip ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aX) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sIn) (by omega), hs₂.ld (d := 8 * sK) (by omega),
      hs₂.ld (d := 8 * sArr aX) (by omega), hw₂ sIn (by omega), hw₂ sK (by omega), hIn, hK, hb₂ aX (by decide)])
    rfl) fun t₃ ⟨⟨hsi₃, hcx₃, hbx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  have hf₃ : Frm B (VG.Proof.Bignum.X86_64.loadRanges ((k + 7) / 8)) s.mem t₃.mem := by rw [hm₃]; exact hf₂
  refine WP.mono (VG.Proof.Bignum.X86_64.loadArr_ok hs₃ (by decide) hZ (hxb.congrK (InScr.of_frm hf₃ hsl) ((k₁.trans k₂).trans k₃))
    hxl (by omega) hk hsi₃ hcx₃ hbx₃) fun t ⟨hv, ha, k₄⟩ => ?_
  have hN' : wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [ha.wv_eq (fun j hj => by
      rw [List.mem_singleton.mp hj]; have := slot_sep (w := (k + 7) / 8) (show aN ≠ aX by decide); omega)
      (by have := slot_le (w := (k + 7) / 8) (show aN < 8 by decide); omega), hm₃]
    exact hv₂
  refine ⟨hN', hv, ?_, fun j hj => ?_, hf₃.trans (Frm.of_arrays1 ha (by simp [VG.Proof.Bignum.X86_64.loadRanges])),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [ha.hslot (by decide), hm₃, ha₂.hslot (by decide)]; exact hW₁
  · rw [ha.hslot (by unfold sArr; omega), hm₃]; exact hb₂ j hj

theorem wv_mod64 (m : Mem) (p : Addr) (d : Nat) {n : Nat} (hn : 1 ≤ n) :
    wv m p d n % 2 ^ 64 = (VG.Proof.Bignum.X86_64.word m p d).toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp [wv, Nat.mod_eq_of_lt (VG.Proof.Bignum.X86_64.word m p d).isLt]
    · rw [wv, Nat.add_mod, ih hn', show 64 * n = 64 + 64 * (n - 1) by omega, Nat.pow_add, Nat.mul_assoc,
        Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt (VG.Proof.Bignum.X86_64.word m p d).isLt]

/-- After the setup: the modulus `N`, `-N⁻¹` in the header, the input `X`,
the number 1, and the mask of `X < N`. -/
structure SetupOut (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X : Nat) : Prop where
  good : Good t B Z w minv
  n : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N
  inv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aX) w = X
  one : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aOne) w = 1
  mask : VG.Proof.Bignum.X86_64.word t.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask (decide (X < N))
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  r10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN)

/-- The mask of `X < N`, `-N⁻¹` and the number 1. -/
theorem setupRest_ok {s : State} {B : Addr} {Z w : Nat} {N X : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hW : VG.Proof.Bignum.X86_64.word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hb : ∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j))
    (hN : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N) (hX : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aX) w = X) (hodd : N % 2 = 1) :
    WP isa (seqs VG.Proof.Bignum.X86_64.restSteps) s fun t => ∃ minv, VG.Proof.Bignum.X86_64.SetupOut t B Z w minv N X ∧
      Frm B [(8 * sMinv, 8), (8 * sMask, 8), (VG.Proof.Bignum.X86_64.slot w aOne, 8 * (w + 2))] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have h0 := slot_le (w := w) (show 0 < 8 by decide)
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eK : sMask = 22 := rfl
  have eAX : sArr aX = 9 := rfl
  have eAN : sArr aN = 8 := rfl
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold VG.Proof.Bignum.X86_64.restSteps
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aX) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sW (by omega), hl (sArr aX) (by omega), hl (sArr aN) (by omega),
      hW, hb aX (by decide), hb aN (by decide)]) rfl) fun t₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (cmpLoop_ok hs₁ hbx h10 h12 hbp (by omega) hw'
    (by have := slot_le (w := w) (show aX < 8 by decide); omega)
    (by have := slot_le (w := w) (show aN < 8 by decide); omega)) fun t₂ ⟨hbp₂, hm₂, k₂⟩ => ?_)
  rw [hm₁, hN, hX] at hbp₂
  have hs₂ := hs₁.congr k₂.2.2
  have hm₂' : t₂.mem = s.mem := hm₂.trans hm₁
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have h10₂ : t₂.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) := (k₂.gpr (by decide)).trans h10
  -- `-N⁻¹`.
  have hodd₀ : (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1 := by
    rw [← VG.Proof.Bignum.X86_64.wv_mod64 _ _ _ (show 1 ≤ w by omega), Nat.mod_mod_of_dvd _ (by decide), hN, hodd]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  have hst : ∀ i < 32, InRegions t₂.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs₂.st (by omega)
  have hsN : (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) (VG.Proof.Bignum.X86_64.mask (decide (X < N)))).readW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN)) 64 =
      VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN) :=
    (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by have := hdr_lt_slot w aN (show sMask < 32 by decide); omega)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega)
  refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) (VG.Proof.Bignum.X86_64.mask (decide (X < N)))) (by
    xrun [State.ea, hdr, at0, hdi₂, hdrOff, hst sMask (by omega), hbp₂, h10₂, hm₂', hsN,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := VG.Proof.Bignum.X86_64.slot w aN) (by have := slot_le (w := w) (show aN < 8 by decide); omega)]) rfl)
    fun t₃ ⟨⟨hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [hbx₃] at hinv
  have hs₄ := (hs₂.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = 1 ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧
      t.mem = t₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by omega)]) rfl)
    fun t₅ ⟨⟨hdx₅, hcx₅, hm₅⟩, k₅⟩ => ?_
  have hs₅ := hs₄.congr k₅.2.2
  have hdi₅ : t₅.gpr .rdi = B := (k₅.gpr (by decide)).trans hdi₄
  have hm₅' : t₅.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMask)) (VG.Proof.Bignum.X86_64.mask (decide (X < N)))).writeW (VG.Proof.Bignum.X86_64.off B (8 * sMinv))
      (t₄.gpr .r15) := by rw [hm₅, hm₄, hm₃]
  have hwv : ∀ j < 8, wv t₅.mem B (VG.Proof.Bignum.X86_64.slot w j) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w := fun j hj => by
    have := slot_le (w := w) hj
    rw [hm₅', (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).wv (by have := hdr_lt_slot w j (show sMinv < 32 by decide); omega)
      (by omega), (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).wv
      (by have := hdr_lt_slot w j (show sMask < 32 by decide); omega) (by omega)]
  have hw0 : VG.Proof.Bignum.X86_64.word t₅.mem B (VG.Proof.Bignum.X86_64.slot w aN) = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN) := by
    have := slot_le (w := w) (show aN < 8 by decide)
    rw [hm₅', (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word
      (by have := hdr_lt_slot w aN (show sMinv < 32 by decide); omega) (by omega)]; exact hsN
  have hhd : ∀ i < 32, i ≠ sMask → i ≠ sMinv → VG.Proof.Bignum.X86_64.word t₅.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hm₅', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  have hH : Hdr t₅.mem B w (t₄.gpr .r15) :=
    ⟨by rw [hhd sW (by decide) (by decide) (by decide)]; exact hW,
      by rw [hm₅', VG.Proof.Bignum.X86_64.word_writeW_self],
      fun j hj => by rw [hhd (sArr j) (by unfold sArr; omega) (by unfold sArr sMask sFn; omega)
        (by unfold sArr sMinv; omega)]; exact hb j hj⟩
  have h12₅ : t₅.gpr .r12 = BitVec.ofNat 64 w :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans h12)))
  have h10₅ : t₅.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h10₂))
  refine WP.mono (setWord_ok hs₅ hdi₅ hH hZ h12₅ (by omega) hw' (o := aOne) (by decide) (ri := .rcx) (by decide)
    (i := 0) (by omega) hcx₅) fun t ⟨hone, ho, k₆⟩ => ⟨t₄.gpr .r15, ?_, ?_, ?_⟩
  · have ha : Arrays B w [aOne] t₅.mem t.mem := Arrays.of_outside (List.mem_singleton_self _) ho
      (Nat.le_refl _) (Nat.le_refl _)
    have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
    refine ⟨⟨hs₅.congr k₆.2.2, (k₆.gpr (by decide)).trans hdi₅, ha.hdr hH⟩, ?_, ?_, ?_, ?_, ?_,
      (k₆.gpr (by decide)).trans h12₅, (k₆.gpr (by decide)).trans h10₅⟩
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aN (by decide), hN]
    · rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega), hw0]; exact hinv
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aX (by decide), hX]
    · rw [hone, hdx₅]; rfl
    · rw [ha.hslot (by decide), hm₅', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm₅'] at ho
    exact ((Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)) (by simp)).trans
      (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)) (by simp))).trans (Frm.of_outside ho (by simp))
  · exact (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)

/-- What the setup changes. -/
def setupRanges (w : Nat) : List (Nat × Nat) :=
  VG.Proof.Bignum.X86_64.loadRanges w ++ [(8 * sMinv, 8), (8 * sMask, 8), (VG.Proof.Bignum.X86_64.slot w aOne, 8 * (w + 2))]

/-- The setup, for a valid modulus. -/
theorem setup_ok {s : State} {B : Addr} {Z k : Nat} {np ip : Addr} {nb xb : List Byte} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * sN) = np)
    (hIn : VG.Proof.Bignum.X86_64.word s.mem B (8 * sIn) = ip) (hnb : VG.Proof.Bignum.X86_64.Src s B Z np nb) (hxb : VG.Proof.Bignum.X86_64.Src s B Z ip xb)
    (hnl : nb.length = k) (hxl : xb.length = k) (hodd : Spec.Rsa.os2ip nb % 2 = 1) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.loadSteps ++ VG.Proof.Bignum.X86_64.restSteps)) s fun t => ∃ minv,
      VG.Proof.Bignum.X86_64.SetupOut t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) ∧
      Frm B (VG.Proof.Bignum.X86_64.setupRanges ((k + 7) / 8)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.loadSteps]) (by simp [VG.Proof.Bignum.X86_64.restSteps])
    (WP.mono (VG.Proof.Bignum.X86_64.setupLoad_ok hs hdi hZ (by omega) hk hK hN hIn hnb hxb hnl hxl)
      fun t₁ ⟨hN₁, hX₁, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.Bignum.X86_64.setupRest_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hZ (by omega) (by omega)
    hW₁ hb₁ hN₁ hX₁ hodd) fun t ⟨minv, ho, hf, k₂⟩ => ⟨minv, ho, ?_, (k₁.trans k₂).mono (by decide)⟩
  exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans
    (hf.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubR2`. -/
section

/-!
# `vg_rsa_public` on x86-64: `R² mod m`

`2^(b - 1)` for the bit length `b` of `m` (from the top bit of its top
word), doubled `64 - j + w` times to `2^w R mod m`, then squared six times
in Montgomery form: `R² mod m` (`r2_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

variable (M : Mont)

/-- One squaring of `[aR2] ≡ 2^E R`. -/
theorem sq_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N E : Nat} (hg : Good t B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N)
    (hn : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N) (hinv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hlt : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N) (hc : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ E * 2 ^ (64 * w) % N) :
    WP isa (M.mm aR2 aR2 aR2) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N ∧
      ((VG.Proof.Bignum.X86_64.word t'.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N ∧ wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ (2 * E) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aR2] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  refine WP.mono (M.mm_ok hg hZ hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hinv (by rw [hn]; exact hlt)) fun t' ⟨hg', hlt', hm, ha, k⟩ => ?_
  rw [hn] at hlt' hm
  refine ⟨hg', by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hn,
    by rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv, hlt', ?_, ha, k⟩
  exact VG.Proof.Bignum.mont_sq hR hc hm

/-- `n + 1` squarings: `2^E R` becomes `2^(2^(n + 1) E) R`. -/
theorem sqs_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N E : Nat} (n : Nat)
    (hg : Good t B Z w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N)
    (hn : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N) (hinv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hlt : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N) (hc : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ E * 2 ^ (64 * w) % N) :
    WP isa (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2))) t fun t' => Good t' B Z w minv ∧
      wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N ∧
      wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ (2 ^ (n + 1) * E) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aR2] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  induction n generalizing t E with
  | zero =>
    exact WP.mono (VG.Proof.Bignum.X86_64.sq_ok M hg hZ hw hw' hR hn hinv hlt hc) fun t' ⟨h1, _, _, h4, h5, h6, h7⟩ =>
      ⟨h1, h4, by rw [h5]; rfl, h6, h7⟩
  | succ n ih =>
    show WP isa (.seq (M.mm aR2 aR2 aR2) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))) t _
    refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.sq_ok M hg hZ hw hw' hR hn hinv hlt hc) fun t₁ ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ?_)
    refine WP.mono (ih h1 h2 h3 h4 h5) fun t' ⟨g1, g2, g3, g4, g5⟩ => ⟨g1, g2, ?_, h6.trans g4 |>.mono (by simp),
      (h7.trans g5).mono (by decide)⟩
    rw [g3, show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 from rfl, Nat.mul_assoc]

/-- The steps of `R² mod m`. -/
def r2Steps : List (Prog isa) := [
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  M.mm aR2 aR2 aR2, M.mm aR2 aR2 aR2, M.mm aR2 aR2 aR2, M.mm aR2 aR2 aR2, M.mm aR2 aR2 aR2, M.mm aR2 aR2 aR2]

/-- What `R² mod m` changes. -/
def r2Ranges (w : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot w aAcc, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aTmp, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aR2, 8 * (w + 2)), (8 * sCnt, 8)]

/-- The start, `2^(b - 1)` for the bit length `b` of the odd `N`, is below
it. -/
theorem start_lt {N T L w : Nat} (hw : 2 ≤ w) (hodd : N % 2 = 1)
    (hT : N = N % 2 ^ (64 * (w - 1)) + 2 ^ (64 * (w - 1)) * T) (hL : 2 ^ L ≤ T) :
    2 ^ L * 2 ^ (64 * (w - 1)) < N := by
  have h1 : 2 ^ L * 2 ^ (64 * (w - 1)) ≤ 2 ^ (64 * (w - 1)) * T := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hL
  rcases Nat.lt_or_ge (2 ^ L * 2 ^ (64 * (w - 1))) N with h | h
  · exact h
  · exfalso
    have he : N = 2 ^ L * 2 ^ (64 * (w - 1)) := by omega
    have : 2 ^ L * 2 ^ (64 * (w - 1)) % 2 = 0 := by
      rw [show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]
    omega

theorem r2Ranges_arr (w : Nat) {j : Nat} (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.r2Ranges w, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w j := by
  have := hdr_lt_slot w j (show sCnt < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  simp only [VG.Proof.Bignum.X86_64.r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> omega

theorem r2Ranges_hdr (w : Nat) {i : Nat} (hi : i < 32) (h : i ≠ sCnt) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.r2Ranges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  have := hdr_lt_slot w aAcc hi
  have := hdr_lt_slot w aTmp hi
  have := hdr_lt_slot w aR2 hi
  simp only [VG.Proof.Bignum.X86_64.r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCnt, sFn] at * <;> omega

theorem r2Ranges_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.r2Ranges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have := slot_le (w := w) (show aAcc < 8 by decide)
  have := slot_le (w := w) (show aTmp < 8 by decide)
  have := slot_le (w := w) (show aR2 < 8 by decide)
  have := hdr_lt_slot w 0 (show sCnt < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  simp only [VG.Proof.Bignum.X86_64.r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> omega

theorem Frm.r2_wv {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (VG.Proof.Bignum.X86_64.r2Ranges w) m m')
    (hn : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    wv m' B (VG.Proof.Bignum.X86_64.slot w j) w = wv m B (VG.Proof.Bignum.X86_64.slot w j) w :=
  h.wv_eq (fun r hr => by have := VG.Proof.Bignum.X86_64.r2Ranges_arr w h1 h2 h3 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem Frm.r2_word {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (VG.Proof.Bignum.X86_64.r2Ranges w) m m')
    (hn : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    VG.Proof.Bignum.X86_64.word m' B (VG.Proof.Bignum.X86_64.slot w j) = VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w j) :=
  h.word_eq (fun r hr => by have := VG.Proof.Bignum.X86_64.r2Ranges_arr w h1 h2 h3 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem pow_r2 {L w : Nat} (hL : L < 64) (hw : 1 ≤ w) :
    2 ^ (64 - L + w) * (2 ^ L * 2 ^ (64 * (w - 1))) = 2 ^ w * 2 ^ (64 * w) := by
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega

/-- `R² mod m`, for the odd `m` of `w ≥ 2` words, its top word not zero. -/
theorem r2_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat} (hg : Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30) (hn : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN)) (hodd : N % 2 = 1)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.r2Steps M)) s fun t => Good t B Z w minv ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N ∧ wv t.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (VG.Proof.Bignum.X86_64.r2Ranges w) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega
  -- The top word `T` of `N`.
  have hsl := slot_le (w := w) (show aN < 8 by decide)
  have hsplit : N = N % 2 ^ (64 * (w - 1)) +
      2 ^ (64 * (w - 1)) * (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1))).toNat := by
    have e : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) (w - 1 + 1) = N := by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w aN) (w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hNlt : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  generalize hT : (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1))).toNat = T at hsplit
  have hT0 : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at hsplit
      have := Nat.mod_lt N (Nat.two_pow_pos (64 * (w - 1))); omega
    · exact h
  have hT1 : T < 2 ^ 64 := hT ▸ BitVec.isLt _
  have hL : T.log2 < 64 := (Nat.log2_lt (by omega)).mpr hT1
  have hle := Nat.log2_self_le (n := T) (by omega)
  have hv0 := VG.Proof.Bignum.X86_64.start_lt hw hodd hsplit hle
  unfold VG.Proof.Bignum.X86_64.r2Steps
  -- The top word.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 T ∧ t.mem = s.mem) (by
    xrun [State.ea, ix, addrm8 h10 h12 (by omega), hs.ld (show VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1) + 8 ≤ Z by omega)]
    rw [← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl) fun t₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (topBit_ok hax hT0 hT1) fun t₂ ⟨hdx₂, hcx₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 w := (k12.gpr (by decide)).trans h12
  have hm₂' : t₂.mem = s.mem := hm₂.trans hm₁
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (w - 1) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sCnt)) (BitVec.ofNat 64 (64 - T.log2))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (d := 8 * sCnt) (by have := hdr_lt_slot w 0 (show sCnt < 32 by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega),
      hcx₂, h12₂, hm₂', ofNat64_pred (show 1 ≤ w by omega) (by omega)]) rfl) fun t₃ ⟨⟨hcx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  have hH₃ : Hdr t₃.mem B w minv := by rw [hm₃]; exact Hdr.store hg.hdr (by decide) (by decide) _
  have hdx₃ : t₃.gpr .rdx = BitVec.ofNat 64 (2 ^ T.log2) := (k₃.gpr (by decide)).trans hdx₂
  refine WP.seq (WP.mono (setWord_ok hs₃ ((k₃.gpr (by decide)).trans hdi₂) hH₃ hZ
    ((k₃.gpr (by decide)).trans h12₂) (by omega) hw' (o := aR2) (by decide) (ri := .rcx) (by decide)
    (i := w - 1) (by omega) hcx₃) fun t₄ ⟨hv₄, ho₄, k₄⟩ => ?_)
  rw [hdx₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hL)] at hv₄
  have hs₄ := hs₃.congr k₄.2.2
  have ha₄ : Arrays B w [aR2] t₃.mem t₄.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₄ (Nat.le_refl _) (Nat.le_refl _)
  have hH₄ : Hdr t₄.mem B w minv := ha₄.hdr hH₃
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  have hcnt₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (8 * sCnt) = BitVec.ofNat 64 (64 - T.log2) := by
    rw [ha₄.hslot (by decide), hm₃, VG.Proof.Bignum.X86_64.word_writeW_self]
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (64 - T.log2 + w) ∧
      t.mem = t₄.mem) (by
    have h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
    have h0' := slot_le (w := w) (show 0 < 8 by decide)
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.ld (d := 8 * sCnt) (by unfold sCnt sFn; omega),
      hs₄.ld (d := 8 * sW) (by unfold sW; omega),
      hcnt₄, hH₄.hw, ← BitVec.ofNat_add]) rfl) fun t₅ ⟨⟨hcx₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  have hN₄ : wv t₄.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) hn', hm₃, hdrStore_wv _ _ _ (by decide) (by decide) hn']
    exact hn
  have hw0₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (VG.Proof.Bignum.X86_64.slot w aN) = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN) := by
    rw [ha₄.word0_of_not_mem (by decide) (by decide) hn' (by omega), hm₃,
      hdrStore_word _ _ _ (by decide) (by decide) hn']
  refine WP.seq (WP.mono (doubles_ok hs₅ ((k₅.gpr (by decide)).trans hdi₄) (hm₅ ▸ hH₄) hZ hw hw'
    (mo := aN) (acc := aAcc) (tmp := aTmp) (o := aR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sl := sCnt) (by decide) (by decide)
    (c := 64 - T.log2 + w) (by omega) (by omega) hcx₅ (by rw [hm₅, hv₄, hN₄]; exact hv0))
    fun t₆ ⟨hv₆, hf₆, hH₆, k₆⟩ => ?_)
  rw [hm₅, hv₄, hN₄, VG.Proof.Bignum.X86_64.pow_r2 hL (by omega)] at hv₆
  have hf₆' : Frm B (VG.Proof.Bignum.X86_64.r2Ranges w) t₅.mem t₆.mem := hf₆
  have hg₆ : Good t₆ B Z w minv := ⟨hs₅.congr k₆.2.2, (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans hdi₄),
    hH₆⟩
  show WP isa (seqs (List.replicate (5 + 1) (M.mm aR2 aR2 aR2))) t₆ _
  refine WP.mono (VG.Proof.Bignum.X86_64.sqs_ok M 5 hg₆ hZ hw hw' hR (E := w)
    (by rw [hf₆'.r2_wv hn' (by decide) (by decide) (by decide) (by decide), hm₅]; exact hN₄)
    (by rw [hf₆'.r2_word hn' (by decide) (by decide) (by decide) (by decide), hm₅, hw0₄]; exact hinv)
    (by rw [hv₆]; exact Nat.mod_lt _ hN0) (by rw [hv₆, Nat.mod_mod]))
    fun t ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, by rw [h3]; congr 2, ?_,
      ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans h5).mono (by decide)⟩
  have f₃ : Frm B (VG.Proof.Bignum.X86_64.r2Ranges w) s.mem t₃.mem := by
    rw [hm₃]; exact Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by have := hdr_lt_slot w 0 (show sCnt < 32 by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega)) (by simp [VG.Proof.Bignum.X86_64.r2Ranges])
  exact (((f₃.trans (Frm.of_arrays ha₄ (by simp [VG.Proof.Bignum.X86_64.r2Ranges]))).trans (by rw [hm₅]; exact Frm.refl _ _ _)).trans
    hf₆').trans (Frm.of_arrays h4 (by simp [VG.Proof.Bignum.X86_64.r2Ranges]))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubExp`. -/
section

/-!
# `vg_rsa_public` on x86-64: the exponentiation

`Y := R mod m` and `X := x R mod m` from `R² mod m`, the exponentiation
(`Y ≡ x^e R`), and `Y R⁻¹ = x^e mod m` (`expPhase_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- The steps of the exponentiation. -/
def expSteps : List (Prog isa) := [mm aY aR2 aOne, mm aXm aX aR2, VG.Impl.Bignum.X86_64.Public.expLoop, mm aY aY aOne]

/-- What the exponentiation changes. -/
def expPhaseRanges (w : Nat) : List (Nat × Nat) := (VG.Proof.Bignum.X86_64.slot w aXm, 8 * (w + 2)) :: expRanges w

theorem expPhaseRanges_arr (w : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ aXm) : ∀ r ∈ VG.Proof.Bignum.X86_64.expPhaseRanges w, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w j := by
  have := hdr_lt_slot w j (show 31 < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  have s4 := slot_sep (w := w) h4
  have := hj
  simp only [VG.Proof.Bignum.X86_64.expPhaseRanges, expRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [VG.Impl.Bignum.X86_64.Public.sI, VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, sFn] at * <;> omega

theorem expPhaseRanges_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.expPhaseRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact slot_le (by decide)
  · exact expRanges_le w r hr

/-- A Montgomery multiplication `[o] := [a] [b] R⁻¹` that keeps the modulus. -/
theorem mmN_ok (M : Mont) {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat} (hg : Good t B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc) (d5 : o ≠ aN)
    (hn : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N) (hinv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv t.mem B (VG.Proof.Bignum.X86_64.slot w b) w < N) (d6 : a ≠ aTmp := by decide) (d7 : b ≠ aTmp := by decide) :
    WP isa (M.mm o a b) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N ∧
      ((VG.Proof.Bignum.X86_64.word t'.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem B (VG.Proof.Bignum.X86_64.slot w o) w < N ∧
      wv t'.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % N = wv t.mem B (VG.Proof.Bignum.X86_64.slot w a) w * wv t.mem B (VG.Proof.Bignum.X86_64.slot w b) w % N ∧
      Arrays B w [aAcc, aTmp, o] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  have hnm : aN ∉ [aAcc, aTmp, o] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, Ne.symm d5⟩
  refine WP.mono (M.mm_ok hg hZ hw hw' ho ha hb d1 d2 d3 d4 hinv (by rw [hn]; exact hB) d6 d7)
    fun t' ⟨hg', hlt', hm, hA, k⟩ => ?_
  rw [hn] at hlt' hm
  exact ⟨hg', by rw [hA.wv_of_not_mem (by decide) hnm hn']; exact hn,
    by rw [hA.word0_of_not_mem (by decide) hnm hn' (by omega)]; exact hinv, hlt', hm, hA, k⟩

theorem Frm.ep_wv {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (VG.Proof.Bignum.X86_64.expPhaseRanges w) m m')
    (hn : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ aXm) : wv m' B (VG.Proof.Bignum.X86_64.slot w j) w = wv m B (VG.Proof.Bignum.X86_64.slot w j) w :=
  h.wv_eq (fun r hr => by have := VG.Proof.Bignum.X86_64.expPhaseRanges_arr w hj h1 h2 h3 h4 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem Frm.ep_hdr {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (VG.Proof.Bignum.X86_64.expPhaseRanges w) m m') {i : Nat}
    (hi : i < 32) (h0 : i ≠ VG.Impl.Bignum.X86_64.Public.sI) (h1 : i ≠ VG.Impl.Bignum.X86_64.Public.sV) (h2 : i ≠ VG.Impl.Bignum.X86_64.Public.sBit) : VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) :=
  h.word_eq (fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · have := hdr_lt_slot w aXm hi; omega
    · exact expRanges_hdr w hi h0 h1 h2 r hr) (by omega)

theorem Frm.ep_of_arrays {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ j ∈ js, j = aAcc ∨ j = aTmp ∨ j = aY ∨ j = aXm) : Frm B (VG.Proof.Bignum.X86_64.expPhaseRanges w) m m' :=
  Frm.of_arrays h fun j hj => by
    rcases hjs j hj with rfl | rfl | rfl | rfl <;> simp [VG.Proof.Bignum.X86_64.expPhaseRanges, expRanges, bitRanges]

/-- The exponentiation: `x^e mod m` into `[aY]`, for `[aR2] ≡ R²`. -/
theorem expPhase_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat} {ep : Addr} {L : Nat}
    {eb : List Byte} (hg : Good s B Z w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hodd : N % 2 = 1) (hN1 : 1 < N) (hn : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hX : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aX) w = X) (hone : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aOne) w = 1)
    (hlt2 : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w < N)
    (hr2 : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N)
    (he : VG.Proof.Bignum.X86_64.word s.mem B (8 * sE) = ep) (hlen : VG.Proof.Bignum.X86_64.word s.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2 ^ 31) (heb : VG.Proof.Bignum.X86_64.Src s B Z ep eb) :
    WP isa (seqs VG.Proof.Bignum.X86_64.expSteps) s fun t => Good t B Z w minv ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = X ^ Spec.Rsa.os2ip eb % N ∧
      Frm B (VG.Proof.Bignum.X86_64.expPhaseRanges w) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  unfold VG.Proof.Bignum.X86_64.expSteps
  -- `Y := R`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mmN_ok Mont.base (o := aY) (a := aR2) (b := aOne) hg hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn hinv (by rw [hone]; exact hN1))
    fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  have f₁ := Frm.ep_of_arrays ha₁ (by simp)
  have hY₁ : wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = 2 ^ (64 * w) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₁, hone, Nat.mul_one, hr2]
  -- `X := x R`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mmN_ok Mont.base (o := aXm) (a := aX) (b := aR2) hg₁ hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn₁ hinv₁
    (by rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlt2))
    fun t₂ ⟨hg₂, hn₂, hinv₂, hlt₂, hm₂, ha₂, k₂⟩ => ?_)
  have f₂ := Frm.ep_of_arrays ha₂ (by simp)
  rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide),
    f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide), hX] at hm₂
  have hX₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w % N = X * 2 ^ (64 * w) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₂, Nat.mul_mod, hr2, ← Nat.mul_mod, Nat.mul_assoc]
  have hY₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aY) w :=
    ha₂.wv_of_not_mem (by decide) (by decide) hn'
  -- The exponentiation.
  have f₁₂ := f₁.trans f₂
  have hs₂ : ∀ i < 32, i ≠ VG.Impl.Bignum.X86_64.Public.sI → i ≠ VG.Impl.Bignum.X86_64.Public.sV → i ≠ VG.Impl.Bignum.X86_64.Public.sBit → VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) :=
    fun i hi h0 h1 h2 => f₁₂.ep_hdr hi h0 h1 h2
  have hin₂ : VG.Proof.Bignum.X86_64.InScr B Z s.mem t₂.mem :=
    InScr.of_frm f₁₂ fun r hr => (VG.Proof.Bignum.X86_64.expPhaseRanges_le w r hr).trans hZ
  have heb₂ := heb.congrK hin₂ (k₁.trans k₂)
  refine WP.seq (WP.mono (expLoop_ok (x := X) (Y := wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aY) w) ⟨hg₂, hn₂, hinv₂, rfl⟩ hZ hw hw' hR
    hlt₂ hX₂ rfl (by rw [hY₂]; exact hlt₁) (by rw [hY₂]; exact hY₁)
    (by rw [hs₂ sE (by decide) (by decide) (by decide) (by decide)]; exact he)
    (by rw [hs₂ sElen (by decide) (by decide) (by decide) (by decide)]; exact hlen)
    hL hL1 hL' (fun i hi => heb₂.rd i (by omega)) (fun i hi => heb₂.val i (by omega))
    (fun i hi => heb₂.out i (by omega))) fun t₃ ⟨hc₃, ⟨Y₃, hY₃, hYN₃, hYc₃⟩, f₃, k₃⟩ => ?_)
  have f₃' : Frm B (VG.Proof.Bignum.X86_64.expPhaseRanges w) t₂.mem t₃.mem := f₃.mono fun r hr => List.mem_cons_of_mem _ hr
  have f₁₃ := f₁₂.trans f₃'
  -- `Y R⁻¹`.
  refine WP.mono (VG.Proof.Bignum.X86_64.mmN_ok Mont.base (o := aY) (a := aY) (b := aOne) hc₃.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.n hc₃.inv
    (by rw [f₁₃.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide), hone]; exact hN1))
    fun t ⟨hg₄, _, _, hlt₄, hm₄, ha₄, k₄⟩ => ⟨hg₄, ?_, f₁₃.trans (Frm.ep_of_arrays ha₄ (by simp)),
      (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  rw [f₁₃.ep_wv (j := aOne) hn' (by decide) (by decide) (by decide) (by decide) (by decide), hone, Nat.mul_one,
    hY₃] at hm₄
  have hc : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = X ^ Spec.Rsa.os2ip eb % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hYc₃]
  rw [← hc, Nat.mod_eq_of_lt hlt₄]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubOut`. -/
section

/-!
# `vg_rsa_public` on x86-64: the result

The result, masked, to `out`; the mask's low bit returned; the saved
registers restored (`outPhase_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- The steps of the result, from array `j`. -/
def outStepsArr (j : Nat) : List (Prog isa) := [
  .block [.mov .rbx (.mem (hdr (sArr j))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  storeBE,
  .block ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] ++ exit)]

/-- The steps of the result. -/
abbrev outSteps : List (Prog isa) := VG.Proof.Bignum.X86_64.outStepsArr aY

theorem exit_eq : exit = [.mov .rbx (.mem (hdr 0)), .mov .rbp (.mem (hdr 1)), .mov .r12 (.mem (hdr 2)),
    .mov .r13 (.mem (hdr 3)), .mov .r14 (.mem (hdr 4)), .mov .r15 (.mem (hdr 5))] := rfl

theorem mask_and1 (c : Bool) : VG.Proof.Bignum.X86_64.mask c &&& 1 = BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

/-- A byte of the working space is not one of `out`'s. -/
theorem scr_ne_out {B out : Addr} {Z k : Nat} (hsep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 j))
    {d i : Nat} (hd : d + i < Z) (hZ : Z ≤ 2 ^ 64) :
    ∀ j < k, VG.Proof.Bignum.X86_64.off B d + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j := by
  intro j hj he
  have h := hsep j hj
  rw [← he, VG.Proof.Bignum.X86_64.ofs_off B (by omega)] at h
  omega

/-- The result: `i2osp (c ? Y : 0)` to `out`, `c` returned, and the saved
registers restored from the header, `Y` in array `j`. -/
theorem outPhaseArr_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    {j : Nat} (hj : j < 8)
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) ((k + 7) / 8) = Y)
    (hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = out) (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask c)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.outStepsArr j)) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h0 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold VG.Proof.Bignum.X86_64.outStepsArr
  refine WP.seq (WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) ∧ t.gpr .rsi = out ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sOut (by decide), hl sK (by decide),
      hl sMask (by decide), hg.hdr.harr j hj, hO, hK, hM]) rfl)
    fun t₁ ⟨⟨hbx, hsi, hcx, h15, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (storeBE_ok hs₁ hbx hsi hcx h15 hk1 hk' rfl
    (by have := slot_le (w := (k + 7) / 8) hj; omega)
    (fun j hj => by rw [k₁.2.2]; exact hout j hj) hsep) fun t₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  rw [hm₁, hY] at hb₂
  have hw₂ : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hf₂ _ (VG.Proof.Bignum.X86_64.scr_ne_out hsep (d := 8 * i) (i := b) (by omega) (by omega)), hm₁]
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => by
    rw [hrd₂, hwr₂, k₁.2.1, k₁.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  rw [VG.Proof.Bignum.X86_64.exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (8 * 0) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.word s.mem B (8 * 1) ∧ t.gpr .r12 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 2) ∧
      t.gpr .r13 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 3) ∧ t.gpr .r14 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 4) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sMask (by decide), hw₂ sMask (by decide), hM, VG.Proof.Bignum.X86_64.mask_and1,
      hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide), hl₂ 3 (by decide), hl₂ 4 (by decide),
      hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide), hw₂ 2 (by decide), hw₂ 3 (by decide),
      hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨by rw [hm]; exact hb₂, hax, ?_,
      fun x hx => by rw [hm, hf₂ x hx, hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem outPhase_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aY) ((k + 7) / 8) = Y)
    (hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = out) (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask c)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs VG.Proof.Bignum.X86_64.outSteps) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      VG.Proof.MlKem.X86_64.Keep mmRegs s t :=
  VG.Proof.Bignum.X86_64.outPhaseArr_ok (by decide) hg hZ hk1 hk' hY hO hK hM hout hsep

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubMain`. -/
section

/-!
# `vg_rsa_public` on x86-64: the computation for a valid modulus

`main`, from the header that `entry` leaves, for a valid modulus: the
result `i2osp (x^e mod m)` (or zeros, if the input is not below `m`) to
`out`, the mask's low bit returned, and the saved registers restored
(`main_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem main_eq : VG.Impl.Bignum.X86_64.Public.main = seqs ((VG.Proof.Bignum.X86_64.loadSteps ++ VG.Proof.Bignum.X86_64.restSteps) ++ ((VG.Proof.Bignum.X86_64.r2Steps Mont.base) ++ (VG.Proof.Bignum.X86_64.expSteps ++ VG.Proof.Bignum.X86_64.outSteps))) := rfl

/-- What `main` starts from: the working space at `B` (its base in `rdi`),
the header `entry` leaves (`out`, `m`, its length `k`, `e`, its length `L`,
the input), and the byte strings outside the working space. -/
structure MainPre (s : State) (B : Addr) (Z k : Nat) (op np ep ip : Addr) (L : Nat)
    (nb eb xb : List Byte) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr s B Z
  rdi : s.gpr .rdi = B
  z : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = op
  hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * sN) = np
  hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hE : VG.Proof.Bignum.X86_64.word s.mem B (8 * sE) = ep
  hL : VG.Proof.Bignum.X86_64.word s.mem B (8 * sElen) = BitVec.ofNat 64 L
  hIn : VG.Proof.Bignum.X86_64.word s.mem B (8 * sIn) = ip
  n : VG.Proof.Bignum.X86_64.Src s B Z np nb
  x : VG.Proof.Bignum.X86_64.Src s B Z ip xb
  e : VG.Proof.Bignum.X86_64.Src s B Z ep eb
  nl : nb.length = k
  xl : xb.length = k
  el : eb.length = L
  L1 : 1 ≤ L
  L2 : L ≤ k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 j)

/-- What `main` (and `fail`) leave: the result `r` (a number below `256^k`)
to `out`, the flag `c` returned, the saved registers restored, and memory
outside the working space and `out` unchanged. -/
structure MainPost (s t : State) (B : Addr) (Z k : Nat) (op : Addr) (r : Nat) (c : Bool) : Prop where
  bytes : (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp r k
  rax : t.gpr .rax = BitVec.ofNat 64 c.toNat
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i)
  frame : ∀ x, Z ≤ VG.Proof.Bignum.X86_64.ofs B x → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

theorem setupRanges_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.setupRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  have := slot_le (w := w) (show aX < 8 by decide)
  have := slot_le (w := w) (show aOne < 8 by decide)
  simp only [VG.Proof.Bignum.X86_64.setupRanges, VG.Proof.Bignum.X86_64.loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv, sMask, sFn] at * <;> omega

theorem setupRanges_fixed (w : Nat) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.setupRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have h1 : VG.Proof.Bignum.X86_64.slot w 0 ≤ VG.Proof.Bignum.X86_64.slot w aN := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have h2 : VG.Proof.Bignum.X86_64.slot w 0 ≤ VG.Proof.Bignum.X86_64.slot w aX := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have h3 : VG.Proof.Bignum.X86_64.slot w 0 ≤ VG.Proof.Bignum.X86_64.slot w aOne := by unfold VG.Proof.Bignum.X86_64.slot; omega
  simp only [VG.Proof.Bignum.X86_64.setupRanges, VG.Proof.Bignum.X86_64.loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv, sMask, sFn] at * <;> omega

theorem r2Ranges_fixed (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.r2Ranges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aR2 (show 31 < 32 by decide)
  simp only [VG.Proof.Bignum.X86_64.r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCnt, sFn] at * <;> omega

theorem expPhaseRanges_fixed (w : Nat) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.expPhaseRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aXm (show 31 < 32 by decide)
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aY (show 31 < 32 by decide)
  simp only [VG.Proof.Bignum.X86_64.expPhaseRanges, expRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [VG.Impl.Bignum.X86_64.Public.sI, VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, sFn] at * <;> omega

/-- What a valid modulus gives: odd, above 1, its top word not zero. -/
theorem valid_facts {N k : Nat} (hv : Spec.Rsa.modulusValid N k = true) (hk : 64 ≤ k) :
    N % 2 = 1 ∧ 1 < N ∧ 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ N := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hv
  have h4 := of_decide_eq_true h4
  have hp : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ 256 ^ (k - 1) := by
    rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have h256 : 256 ≤ 256 ^ (k - 1) := by
    have := Nat.pow_le_pow_right (n := 256) (by decide) (show 1 ≤ k - 1 by omega); simpa using this
  exact ⟨beq_iff_eq.mp h1, by omega, hp.trans h4⟩

/-- `main`, for a valid modulus `m`: `i2osp (x^e mod m)` if `x < m` and
zeros otherwise, and `x < m` returned. -/
theorem main_ok {s : State} {B : Addr} {Z k : Nat} {op np ep ip : Addr} {L : Nat} {nb eb xb : List Byte}
    (h : VG.Proof.Bignum.X86_64.MainPre s B Z k op np ep ip L nb eb xb) (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa VG.Impl.Bignum.X86_64.Public.main s fun t => VG.Proof.Bignum.X86_64.MainPost s t B Z k op
      (if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
        Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % Spec.Rsa.os2ip nb else 0)
      (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) := by
  obtain ⟨hodd, hN1, hlo⟩ := VG.Proof.Bignum.X86_64.valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hn := h.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => (h' r hr).trans hZ
  rw [VG.Proof.Bignum.X86_64.main_eq]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.loadSteps]) (by simp [VG.Proof.Bignum.X86_64.r2Steps])
    (WP.mono (VG.Proof.Bignum.X86_64.setup_ok h.scr h.rdi hZ (by omega) (by omega) h.hK h.hN h.hIn h.n h.x h.nl h.xl hodd)
      fun t₁ ⟨minv, so, f₁, k₁⟩ => ?_)
  have x₁ := Fixed.of_frm f₁ (VG.Proof.Bignum.X86_64.setupRanges_fixed _)
  have i₁ := InScr.of_frm f₁ (hZs (VG.Proof.Bignum.X86_64.setupRanges_le _))
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.r2Steps]) (by simp [VG.Proof.Bignum.X86_64.expSteps])
    (WP.mono (VG.Proof.Bignum.X86_64.r2_ok Mont.base so.good hZ (by omega) (by omega) so.n so.inv so.r12 so.r10 hodd hlo)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have x₂ := Fixed.of_frm f₂ (VG.Proof.Bignum.X86_64.r2Ranges_fixed _)
  have i₂ := InScr.of_frm f₂ (hZs (VG.Proof.Bignum.X86_64.r2Ranges_le _))
  have x₁₂ := x₁.trans x₂
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.expSteps]) (by simp [VG.Proof.Bignum.X86_64.outSteps, VG.Proof.Bignum.X86_64.outStepsArr])
    (WP.mono (VG.Proof.Bignum.X86_64.expPhase_ok (X := Spec.Rsa.os2ip xb) hg₂ hZ (by omega) (by omega) hodd hN1
      (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.n)
      (by rw [f₂.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact so.inv)
      (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.x)
      (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.one)
      hlt₂ hr₂ (by rw [x₁₂ sE (by decide)]; exact h.hE) (by rw [x₁₂ sElen (by decide)]; exact h.hL)
      h.el h.L1 (by omega) (h.e.congrK (i₁.trans i₂) (k₁.trans k₂)))
      fun t₃ ⟨hg₃, hY₃, f₃, k₃⟩ => ?_)
  have x₃ := Fixed.of_frm f₃ (VG.Proof.Bignum.X86_64.expPhaseRanges_fixed _)
  have i₃ := InScr.of_frm f₃ (hZs (VG.Proof.Bignum.X86_64.expPhaseRanges_le _))
  have x₁₃ := x₁₂.trans x₃
  have k₁₃ := (k₁.trans k₂).trans k₃
  have hM₃ : VG.Proof.Bignum.X86_64.word t₃.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) := by
    rw [f₃.ep_hdr (by decide) (by decide) (by decide) (by decide),
      f₂.word_eq (VG.Proof.Bignum.X86_64.r2Ranges_hdr _ (by decide) (by decide)) (by unfold sMask sFn; omega)]
    exact so.mask
  refine WP.mono (VG.Proof.Bignum.X86_64.outPhase_ok hg₃ hZ (by omega) (by omega) hY₃ (by rw [x₁₃ sOut (by decide)]; exact h.hO)
    (by rw [x₁₃ sK (by decide)]; exact h.hK) hM₃ (fun j hj => by rw [k₁₃.2.2]; exact h.out j hj) h.outSep)
    fun t ⟨hb, hax, hsv, hfr, k₄⟩ => ⟨?_, hax, fun i hi => by rw [hsv i hi]; exact x₁₃ i (by omega),
      fun x hx hx' => by rw [hfr x hx', i₃ x hx, i₂ x hx, i₁ x hx], (k₁₃.trans k₄).mono (by decide)⟩
  rw [hb]
  by_cases hc : Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb <;> simp [hc]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubFail`. -/
section

/-!
# `vg_rsa_public` on x86-64: an invalid modulus

`fail` writes `k` zeros to `out`, returns 0 and restores the saved
registers (`fail_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

/-- After `j` zeros from `s₀`. -/
structure FailInv (s₀ : State) (op : Addr) (k j : Nat) (t : State) : Prop where
  keep : VG.Proof.MlKem.X86_64.Keep [.rsi, .rcx] s₀ t
  rsi : t.gpr .rsi = op + BitVec.ofNat 64 j
  rcx : t.gpr .rcx = BitVec.ofNat 64 (k - j)
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem i2osp_zero (k : Nat) : Spec.Rsa.i2osp 0 k = (List.range k).map fun _ => 0 := by
  unfold Spec.Rsa.i2osp
  simp

theorem fail_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = op) (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 j)) :
    WP isa VG.Impl.Bignum.X86_64.Public.fail s fun t => VG.Proof.Bignum.X86_64.MainPost s t B Z k op 0 false := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold VG.Impl.Bignum.X86_64.Public.fail
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := k) (by omega) (VG.Proof.Bignum.X86_64.FailInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t₂ hI => ?_)
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = k))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ k - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, VG.WriteBytes.writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, VG.WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  -- The saved registers.
  have hw₂ : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hI.frame _ (fun j hj => VG.Proof.Bignum.X86_64.scr_ne_out hsep (d := 8 * i) (i := b) (by omega) (by omega) j (by omega)), hm₁]
  have k12 := k₁.trans hI.keep
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  rw [VG.Proof.Bignum.X86_64.exit_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (8 * 0) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.word s.mem B (8 * 1) ∧ t.gpr .r12 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 2) ∧
      t.gpr .r13 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 3) ∧ t.gpr .r14 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 4) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide),
      hw₂ 2 (by decide), hw₂ 3 (by decide), hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨?_, ?_, ?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [VG.Proof.Bignum.X86_64.i2osp_zero]
    exact List.map_congr_left fun i hi => by rw [hm]; exact hI.bytes i (List.mem_range.mp hi)
  · rw [k₃.gpr (by decide), hI.keep.gpr (by decide), hax]; rfl
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm, hI.frame x hx, hm₁]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PubEntry`. -/
section

/-!
# `vg_rsa_public` on x86-64: the entry

`entry` saves the callee-saved registers and the arguments in the header of
the working space, and leaves its base in `rdi` (`entry_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- Slot `i` of the header at `r11`. -/
def hdr11 (i : Nat) : MemOp := { base := .r11, disp := 8 * (i : Int) }

theorem entry_eq : VG.Impl.Bignum.X86_64.Public.entry = ([.mov .r11 (.mem { base := .rsp, disp := 24 }),
    .store (VG.Proof.Bignum.X86_64.hdr11 0) .rbx, .store (VG.Proof.Bignum.X86_64.hdr11 1) .rbp, .store (VG.Proof.Bignum.X86_64.hdr11 2) .r12, .store (VG.Proof.Bignum.X86_64.hdr11 3) .r13,
    .store (VG.Proof.Bignum.X86_64.hdr11 4) .r14, .store (VG.Proof.Bignum.X86_64.hdr11 5) .r15,
    .store (VG.Proof.Bignum.X86_64.hdr11 sOut) .rdi, .store (VG.Proof.Bignum.X86_64.hdr11 sN) .rdx, .store (VG.Proof.Bignum.X86_64.hdr11 sK) .rcx, .store (VG.Proof.Bignum.X86_64.hdr11 sE) .r8,
    .store (VG.Proof.Bignum.X86_64.hdr11 sElen) .r9] : List Instr) ++ [.mov .rax (.mem { base := .rsp, disp := 8 }), .store (VG.Proof.Bignum.X86_64.hdr11 sIn) .rax,
    .mov .rdi (.reg .r11)] := rfl

/-- A word of the header past a store to another slot. -/
theorem word_skip {m : Mem} {B : Addr} {i j : Nat} {v x : BitVec 64} (h : VG.Proof.Bignum.X86_64.word m B (8 * j) = x)
    (hij : i ≠ j) (hi : i < 32) (hj : j < 32) : VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) B (8 * j) = x :=
  (hdrStore_hdr m B v hi hj hij).trans h

theorem Outside.store_hdr {B : Addr} {n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside B 0 n m m') {i : Nat}
    (hi : 8 * i + 8 ≤ n) (hn : n ≤ 2 ^ 64) (v : BitVec 64) : VG.Proof.Bignum.X86_64.Outside B 0 n m (m'.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) :=
  fun x hx => (VG.Proof.Bignum.X86_64.writeW_outside m' B v (by omega) x (by omega)).trans (h x hx)

/-- The header after `entry`'s stores. -/
def entryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk ve vl : BitVec 64) : Mem :=
  ((((((((((m.writeW (VG.Proof.Bignum.X86_64.off B (8 * 0)) v0).writeW (VG.Proof.Bignum.X86_64.off B (8 * 1)) v1).writeW (VG.Proof.Bignum.X86_64.off B (8 * 2)) v2).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * 3)) v3).writeW (VG.Proof.Bignum.X86_64.off B (8 * 4)) v4).writeW (VG.Proof.Bignum.X86_64.off B (8 * 5)) v5).writeW (VG.Proof.Bignum.X86_64.off B (8 * sOut)) vo).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * sN)) vn).writeW (VG.Proof.Bignum.X86_64.off B (8 * sK)) vk).writeW (VG.Proof.Bignum.X86_64.off B (8 * sE)) ve).writeW (VG.Proof.Bignum.X86_64.off B (8 * sElen)) vl

theorem entryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk ve vl : BitVec 64) :
    let m' := VG.Proof.Bignum.X86_64.entryMem m B v0 v1 v2 v3 v4 v5 vo vn vk ve vl
    VG.Proof.Bignum.X86_64.word m' B (8 * 0) = v0 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 1) = v1 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 2) = v2 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 3) = v3 ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * 4) = v4 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 5) = v5 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sOut) = vo ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sN) = vn ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * sK) = vk ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sE) = ve ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sElen) = vl ∧
    VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' VG.Proof.Bignum.X86_64.entryMem
  all_goals first
    | (repeat (first | refine VG.Proof.Bignum.X86_64.word_skip ?_ (by decide) (by decide) (by decide) |
        exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(the third stack argument) in `rdi`. -/
theorem entry_ok {s : State} {B : Addr} (hB : stackArg s 2 = B)
    (hw : ∀ i < 22, InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8)
    (ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8)
    (hsep : ∀ m', VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0) :
    WP isa (.block VG.Impl.Bignum.X86_64.Public.entry) s fun t => t.gpr .rdi = B ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 0) = s.gpr .rbx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 1) = s.gpr .rbp ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 2) = s.gpr .r12 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 3) = s.gpr .r13 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 4) = s.gpr .r14 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 5) = s.gpr .r15 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sOut) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sN) = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sK) = s.gpr .rcx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = s.gpr .r8 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = s.gpr .r9 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sIn) = stackArg s 0 ∧
      VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi] s t := by
  have e0 : s.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := rfl
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have hB' : s.mem.readW (stackArgAddr s 2) 64 = B := hB
  have hA0 : s.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := rfl
  rw [VG.Proof.Bignum.X86_64.entry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 0) = s.gpr .rbx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 1) = s.gpr .rbp ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 2) = s.gpr .r12 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 3) = s.gpr .r13 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * 4) = s.gpr .r14 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * 5) = s.gpr .r15 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sOut) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sN) = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sK) = s.gpr .rcx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = s.gpr .r8 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = s.gpr .r9 ∧ VG.Proof.Bignum.X86_64.Outside B 0 (8 * 22) s.mem t.mem) ?_ rfl)
    fun t₁ ⟨⟨h11, h0, h1, h2, h3, h4, h5, hO, hN, hK, hE, hL, ho₁⟩, k₁⟩ => ?_
  · xrun [State.ea, VG.Proof.Bignum.X86_64.hdr11, e2, ha2, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sOut (by decide),
      hw sN (by decide), hw sK (by decide), hw sE (by decide), hw sElen (by decide)]
    exact VG.Proof.Bignum.X86_64.entryMem_facts _ _ _ _ _ _ _ _ _ _ _ _ _
  have hr₁ : t₁.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := hsep _ ho₁
  have ha0₁ : InRegions (t₁.rd ++ t₁.wr) (stackArgAddr s 0) 8 := by rw [k₁.2.1, k₁.2.2]; exact ha0
  have hw₁ : InRegions t₁.wr (VG.Proof.Bignum.X86_64.off B (8 * sIn)) 8 := by rw [k₁.2.2]; exact hw sIn (by decide)
  have e0₁ : t₁.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := by rw [k₁.gpr (by decide)]; exact e0
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.gpr .rdi = B ∧
      t.mem = t₁.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sIn)) (stackArg s 0)) (by
    xrun [State.ea, VG.Proof.Bignum.X86_64.hdr11, e0₁, ha0₁, hr₁, h11, hdrOff, hw₁]) rfl) fun t ⟨⟨hdi, hm⟩, k₂⟩ => ?_
  refine ⟨hdi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [hm]
  · exact VG.Proof.Bignum.X86_64.word_skip h0 (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip h1 (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip h2 (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip h3 (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip h4 (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip h5 (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip hO (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip hN (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip hK (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip hE (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_skip hL (by decide) (by decide) (by decide)
  · exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · exact Outside.store_hdr ho₁ (by decide) (by decide) _
  · exact (k₁.trans k₂).mono (by decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry`. -/
section

/-!
# RSA with the CRT on x86-64: the entry

`Crt.entry` saves the callee-saved registers and the arguments (the pointers
and lengths among them `main` reads, some from the stack) in the header of
the working space, and leaves its base in `rdi` (`crtEntry_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Stack argument `j` (from 0) into `rax`, then into header slot `i` at `r11`. -/
def crtPair (j i : Nat) : List Instr :=
  [.mov .rax (.mem { base := .rsp, disp := 8 * ((j + 1 : Nat) : Int) }), .store (VG.Proof.Bignum.X86_64.hdr11 i) .rax]

/-- `crtPair` for each `(j, i)`. -/
def crtPairs : List (Nat × Nat) → List Instr
  | [] => []
  | p :: ps => VG.Proof.Bignum.X86_64.crtPair p.1 p.2 ++ VG.Proof.Bignum.X86_64.crtPairs ps

theorem crtEntry_eq : Crt.entry = ([.mov .r11 (.mem { base := .rsp, disp := 88 }),
    .store (VG.Proof.Bignum.X86_64.hdr11 0) .rbx, .store (VG.Proof.Bignum.X86_64.hdr11 1) .rbp, .store (VG.Proof.Bignum.X86_64.hdr11 2) .r12, .store (VG.Proof.Bignum.X86_64.hdr11 3) .r13,
    .store (VG.Proof.Bignum.X86_64.hdr11 4) .r14, .store (VG.Proof.Bignum.X86_64.hdr11 5) .r15,
    .store (VG.Proof.Bignum.X86_64.hdr11 sOut) .rdi, .store (VG.Proof.Bignum.X86_64.hdr11 sN) .rdx, .store (VG.Proof.Bignum.X86_64.hdr11 sK) .rcx, .store (VG.Proof.Bignum.X86_64.hdr11 sIn) .r8] : List Instr) ++
    (VG.Proof.Bignum.X86_64.crtPairs [(0, sP), (1, sPlen), (2, sQ), (3, sQlen), (4, sDp), (6, sDq), (8, sQinv)] ++
      ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

theorem stackArgAddr_disp (s : State) (j : Nat) :
    s.gpr .rsp + BitVec.ofInt 64 (8 * ((j + 1 : Nat) : Int)) = stackArgAddr s j := by
  rw [show (8 * ((j + 1 : Nat) : Int)) = ((8 * (j + 1) : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rfl

/-- One stack argument into the header. -/
theorem crtPair_ok {t : State} {B A : Addr} {j i : Nat} {v : BitVec 64} (h11 : t.gpr .r11 = B)
    (hA : t.gpr .rsp + BitVec.ofInt 64 (8 * ((j + 1 : Nat) : Int)) = A)
    (ha : InRegions (t.rd ++ t.wr) A 8) (hv : t.mem.readW A 64 = v) (hw : InRegions t.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8) :
    WP isa (.block (VG.Proof.Bignum.X86_64.crtPair j i)) t fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' :=
  WP.keep [.rax] (by xrun [VG.Proof.Bignum.X86_64.crtPair, State.ea, VG.Proof.Bignum.X86_64.hdr11, hA, ha, hv, h11, hdrOff, hw]) rfl

/-- The stack arguments `p.1` into the header slots `p.2`, for `p ∈ ps`. -/
theorem crtPairs_ok {s : State} {B : Addr} : ∀ (ps : List (Nat × Nat)) (t : State),
    (∀ p ∈ ps, p.2 < 32 ∧ InRegions (s.rd ++ s.wr) (stackArgAddr s p.1) 8 ∧
      (∀ m', VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s p.1) 64 = stackArg s p.1) ∧
      InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * p.2)) 8) →
    t.gpr .r11 = B → t.gpr .rsp = s.gpr .rsp → t.rd = s.rd → t.wr = s.wr → VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem t.mem →
    WP isa (.block (VG.Proof.Bignum.X86_64.crtPairs ps)) t fun t' =>
      t'.mem = ps.foldl (fun m p => m.writeW (VG.Proof.Bignum.X86_64.off B (8 * p.2)) (stackArg s p.1)) t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t'
  | [], _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | p :: ps, t, hps, h11, hsp, hrd, hwr, ho => by
    obtain ⟨hi, ha, hsep, hw⟩ := hps p List.mem_cons_self
    rw [show VG.Proof.Bignum.X86_64.crtPairs (p :: ps) = VG.Proof.Bignum.X86_64.crtPair p.1 p.2 ++ VG.Proof.Bignum.X86_64.crtPairs ps from rfl, WP.block_append_iff]
    refine WP.mono (VG.Proof.Bignum.X86_64.crtPair_ok h11 (by rw [hsp]; exact VG.Proof.Bignum.X86_64.stackArgAddr_disp s p.1) (by rw [hrd, hwr]; exact ha)
      (hsep _ ho) (by rw [hwr]; exact hw)) fun t₁ ⟨hm, k⟩ => ?_
    refine WP.mono (VG.Proof.Bignum.X86_64.crtPairs_ok ps t₁ (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (by rw [k.gpr (by decide)]; exact h11) (by rw [k.gpr (by decide)]; exact hsp) (k.2.1.trans hrd)
      (k.2.2.trans hwr) (by rw [hm]; exact Outside.store_hdr ho (by omega) (by decide) _))
      fun t' ⟨hm', k'⟩ => ⟨by rw [hm', hm]; rfl, (k.trans k').mono (by decide)⟩

/-- The header after the stores from registers. -/
def crtEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi : BitVec 64) : Mem :=
  (((((((((m.writeW (VG.Proof.Bignum.X86_64.off B (8 * 0)) v0).writeW (VG.Proof.Bignum.X86_64.off B (8 * 1)) v1).writeW (VG.Proof.Bignum.X86_64.off B (8 * 2)) v2).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * 3)) v3).writeW (VG.Proof.Bignum.X86_64.off B (8 * 4)) v4).writeW (VG.Proof.Bignum.X86_64.off B (8 * 5)) v5).writeW (VG.Proof.Bignum.X86_64.off B (8 * sOut)) vo).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * sN)) vn).writeW (VG.Proof.Bignum.X86_64.off B (8 * sK)) vk).writeW (VG.Proof.Bignum.X86_64.off B (8 * sIn)) vi

/-- The header after the entry's stores. -/
def crtEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) : Mem :=
  (((((((VG.Proof.Bignum.X86_64.crtEntryMemA m B v0 v1 v2 v3 v4 v5 vo vn vk vi).writeW (VG.Proof.Bignum.X86_64.off B (8 * sP)) vp).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * sPlen)) vpl).writeW (VG.Proof.Bignum.X86_64.off B (8 * sQ)) vq).writeW (VG.Proof.Bignum.X86_64.off B (8 * sQlen)) vql).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * sDp)) vdp).writeW (VG.Proof.Bignum.X86_64.off B (8 * sDq)) vdq).writeW (VG.Proof.Bignum.X86_64.off B (8 * sQinv)) vqi

theorem crtEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi : BitVec 64) :
    VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) m (VG.Proof.Bignum.X86_64.crtEntryMemA m B v0 v1 v2 v3 v4 v5 vo vn vk vi) := by
  unfold VG.Proof.Bignum.X86_64.crtEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem crtEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) :
    let m' := VG.Proof.Bignum.X86_64.crtEntryMem m B v0 v1 v2 v3 v4 v5 vo vn vk vi vp vpl vq vql vdp vdq vqi
    VG.Proof.Bignum.X86_64.word m' B (8 * 0) = v0 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 1) = v1 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 2) = v2 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 3) = v3 ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * 4) = v4 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 5) = v5 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sOut) = vo ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sN) = vn ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * sK) = vk ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sIn) = vi ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sP) = vp ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sPlen) = vpl ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * sQ) = vq ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sQlen) = vql ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sDp) = vdp ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * sDq) = vdq ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sQinv) = vqi ∧ VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' VG.Proof.Bignum.X86_64.crtEntryMem VG.Proof.Bignum.X86_64.crtEntryMemA
  all_goals first
    | (repeat (first | refine VG.Proof.Bignum.X86_64.word_skip ?_ (by decide) (by decide) (by decide) |
        exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `Crt.entry`: the header, from the arguments, and the working space's
base (stack argument 10) in `rdi`. -/
theorem crtEntry_ok {s : State} {B : Addr} (hB : stackArg s 10 = B)
    (hw : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8)
    (ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 11, ∀ m', VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block Crt.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sOut) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sN) = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sK) = s.gpr .rcx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sIn) = s.gpr .r8 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sP) = stackArg s 0 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sPlen) = stackArg s 1 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sQ) = stackArg s 2 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sQlen) = stackArg s 3 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sDp) = stackArg s 4 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sDq) = stackArg s 6 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sQinv) = stackArg s 8 ∧
      VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi] s t := by
  have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
  have hB' : s.mem.readW (stackArgAddr s 10) 64 = B := hB
  have ha10 := ha 10 (by decide)
  rw [VG.Proof.Bignum.X86_64.crtEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = VG.Proof.Bignum.X86_64.crtEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, VG.Proof.Bignum.X86_64.hdr11, e10, ha10, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sOut (by decide),
      hw sN (by decide), hw sK (by decide), hw sIn (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact VG.Proof.Bignum.X86_64.crtEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = VG.Proof.Bignum.X86_64.crtEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3) (stackArg s 4) (stackArg s 6) (stackArg s 8) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho⟩ :=
    VG.Proof.Bignum.X86_64.crtEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 3) (stackArg s 4) (stackArg s 6) (stackArg s 8)
  refine ⟨hdi, fun i hi => ?_, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtSel`. -/
section

/-!
# RSA with the CRT on x86-64: a masked copy with SSE2

`sseSelect` (`Impl/Rsa/X86_64/Crt.lean`) replaces the words of `[rbx]` by
those of `[r8]` under the mask `rbp` (all ones or zero), two words at a time
in the `xmm` registers: each pair becomes `T ^ ((E ^ T) & mask)`
(`sseSelect_ok`), over the words below `2 ⌈w / 2⌉`, one more than `w` when
`w` is odd.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## The arithmetic -/

theorem sel_mask (c : Bool) (t e : BitVec 64) : t ^^^ ((e ^^^ t) &&& VG.Proof.Bignum.X86_64.mask c) = if c then e else t := by
  cases c
  · simp [mask_false]
  · rw [show VG.Proof.Bignum.X86_64.mask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_comm t e, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rfl

/-- Quadword `q` of a 128-bit value. -/
abbrev q128 (v : BitVec 128) (q : Nat) : BitVec 64 := qword v q

theorem q128_low (x : BitVec 64) : VG.Proof.Bignum.X86_64.q128 ((0 : BitVec 64) ++ x) 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VG.Proof.Bignum.X86_64.q128, qword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  rw [BitVec.getLsbD_append]; simp [hi]

theorem q128_pair (x : BitVec 64) {q : Nat} (hq : q < 2) : VG.Proof.Bignum.X86_64.q128 (x ++ x) q = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VG.Proof.Bignum.X86_64.q128, qword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]
  rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
  · simp [hi]
  · simp [show ¬ 64 * 1 + i < 64 by omega]

theorem q128_xor (a b : BitVec 128) (q : Nat) : VG.Proof.Bignum.X86_64.q128 (a ^^^ b) q = VG.Proof.Bignum.X86_64.q128 a q ^^^ VG.Proof.Bignum.X86_64.q128 b q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [VG.Proof.Bignum.X86_64.q128, qword, hi]

theorem q128_and (a b : BitVec 128) (q : Nat) : VG.Proof.Bignum.X86_64.q128 (a &&& b) q = VG.Proof.Bignum.X86_64.q128 a q &&& VG.Proof.Bignum.X86_64.q128 b q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [VG.Proof.Bignum.X86_64.q128, qword, hi]

/-- The mask in both quadwords: `punpcklqdq` of `movq`. -/
theorem q128_dup (x : BitVec 64) {q : Nat} (hq : q < 2) :
    VG.Proof.Bignum.X86_64.q128 (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ x) ((0 : BitVec 64) ++ x)) q = x := by
  simp only [XBinOp.eval]
  rw [show qword ((0 : BitVec 64) ++ x) 0 = x from VG.Proof.Bignum.X86_64.q128_low x]
  exact VG.Proof.Bignum.X86_64.q128_pair x hq

/-- Quadword `q` of a 16-byte read. -/
theorem q128_read (m : Mem) (a : Addr) {q : Nat} (hq : q < 2) :
    VG.Proof.Bignum.X86_64.q128 (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 (8 * q)) 64 := by
  have e := readW_extract m a (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  exact e

/-- A 16-byte write, read back a quadword at a time. -/
theorem read_write128 (m : Mem) (a : Addr) (v : BitVec 128) {q : Nat} (hq : q < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * q)) 64 = VG.Proof.Bignum.X86_64.q128 v q := by
  have e := readW_writeW_inside m a v (k := 8 * q) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  exact e

/-! ## A pair of words -/

theorem off_add_eq (B : Addr) (a d : Nat) : VG.Proof.Bignum.X86_64.off B a + BitVec.ofNat 64 d = VG.Proof.Bignum.X86_64.off B (a + d) := off_off B a d

/-- The loop body of `sseSelect`. -/
def selPair : List Instr :=
  [.movdquLoad .xmm1 (ix .r8 .r14), .movdquLoad .xmm2 (ix .rbx .r14), .xop (.bin .pxor .xmm1 .xmm2),
    .xop (.bin .pand .xmm1 .xmm0), .xop (.bin .pxor .xmm2 .xmm1), .movdquStore (ix .rbx .r14) .xmm2,
    .alu .add .r14 (.imm 2), .alu .cmp .r14 (.reg .r13)]

theorem inRegions16 {s : State} {B : Addr} {Z : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) {d : Nat} (hd : d + 16 ≤ Z) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B d) 16 ∧ InRegions s.wr (VG.Proof.Bignum.X86_64.off B d) 16 := by
  obtain ⟨r, hr, hc⟩ := hs.region hd (by decide)
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r, hr, hc⟩⟩

/-- Words `2 j` and `2 j + 1` of `[rbx]` replaced under the mask. -/
theorem selPair_ok {s : State} {B : Addr} {Z eA eo j n : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * j))
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (2 * n)) (hjn : j < n) (hn : 2 * n < 2 ^ 64)
    (hA : eA + 16 * j + 16 ≤ Z) (ho : eo + 16 * j + 16 ≤ Z) {msk : BitVec 64}
    (hx0 : ∀ q < 2, VG.Proof.Bignum.X86_64.q128 (s.xmm .xmm0) q = msk) :
    WP isa (.block VG.Proof.Bignum.X86_64.selPair) s fun t =>
      (∀ q < 2, VG.Proof.Bignum.X86_64.word t.mem B (eo + 16 * j + 8 * q) =
        VG.Proof.Bignum.X86_64.word s.mem B (eo + 16 * j + 8 * q) ^^^
          ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 16 * j + 8 * q) ^^^ VG.Proof.Bignum.X86_64.word s.mem B (eo + 16 * j + 8 * q)) &&& msk)) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (eo + 16 * j)) (t.mem.readW (VG.Proof.Bignum.X86_64.off B (eo + 16 * j)) 128) ∧
      t.gpr .r14 = BitVec.ofNat 64 (2 * (j + 1)) ∧ t.zf = some (decide (j + 1 = n)) ∧
      (∀ q < 2, VG.Proof.Bignum.X86_64.q128 (t.xmm .xmm0) q = msk) ∧ VG.Proof.MlKem.X86_64.Keep [.r14] s t := by
  have hn' := hs.nowrap
  obtain ⟨iA, -⟩ := VG.Proof.Bignum.X86_64.inRegions16 hs (d := eA + 16 * j) (by omega)
  obtain ⟨iO, sO⟩ := VG.Proof.Bignum.X86_64.inRegions16 hs (d := eo + 16 * j) (by omega)
  have eA' : s.ea (ix .r8 .r14) = VG.Proof.Bignum.X86_64.off B (eA + 16 * j) := by rw [ea_ix0 s h8 h14]; congr 1; omega
  have eO' : s.ea (ix .rbx .r14) = VG.Proof.Bignum.X86_64.off B (eo + 16 * j) := by rw [ea_ix0 s hbx h14]; congr 1; omega
  let X1 := s.mem.readW (VG.Proof.Bignum.X86_64.off B (eA + 16 * j)) 128
  let X2 := s.mem.readW (VG.Proof.Bignum.X86_64.off B (eo + 16 * j)) 128
  let s₁ := s.setXmm .xmm1 X1
  let s₂ := s₁.setXmm .xmm2 X2
  let s₃ := s₂.setXmm .xmm1 (XBinOp.eval .pxor X1 X2)
  let s₄ := s₃.setXmm .xmm1 (XBinOp.eval .pand (XBinOp.eval .pxor X1 X2) (s.xmm .xmm0))
  let V := XBinOp.eval .pxor X2 (XBinOp.eval .pand (XBinOp.eval .pxor X1 X2) (s.xmm .xmm0))
  let s₅ := s₄.setXmm .xmm2 V
  let s₆ : State := { s₅ with mem := s.mem.writeW (VG.Proof.Bignum.X86_64.off B (eo + 16 * j)) V }
  unfold VG.Proof.Bignum.X86_64.selPair
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [exec, eA', State.load128, iA, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by
    simp only [exec, show s₁.ea (ix .rbx .r14) = VG.Proof.Bignum.X86_64.off B (eo + 16 * j) from eO', State.load128,
      show s₁.rd = s.rd from rfl, show s₁.wr = s.wr from rfl, iO, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₄, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₅, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₆, by
    simp only [exec, show s₅.ea (ix .rbx .r14) = VG.Proof.Bignum.X86_64.off B (eo + 16 * j) from eO', State.store128,
      show s₅.wr = s.wr from rfl, sO, ite_true]; rfl, ?_⟩
  have hadd : BitVec.ofNat 64 (2 * j) + 2 = BitVec.ofNat 64 (2 * (j + 1)) := by
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, BitVec.ofNat_add]; rfl
  have hcmp : (BitVec.ofNat 64 (2 * (j + 1)) - BitVec.ofNat 64 (2 * n) == 0) = decide (j + 1 = n) := by
    rw [ofNat_sub_beq (by omega) hn]; exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (2 * (j + 1)) ∧
      t.zf = some (decide (j + 1 = n)) ∧ t.mem = s₆.mem ∧ t.xmm = s₆.xmm)
    (by xrun [show s₆.gpr = s.gpr from rfl, h14, h13, hadd, hcmp]; rfl) rfl) fun t ⟨⟨h14', hz, hm, hx⟩, k⟩ => ?_
  have hrd : ∀ (m : Mem) (d : Nat) {q : Nat}, q < 2 → VG.Proof.Bignum.X86_64.q128 (m.readW (VG.Proof.Bignum.X86_64.off B d) 128) q = VG.Proof.Bignum.X86_64.word m B (d + 8 * q) :=
    fun m d q hq => by rw [VG.Proof.Bignum.X86_64.q128_read m _ hq, VG.Proof.Bignum.X86_64.off_add_eq]
  have hV : t.mem.readW (VG.Proof.Bignum.X86_64.off B (eo + 16 * j)) 128 = V := by
    rw [hm]; exact Mem.readW_writeW_self (n := 16) _ _ V (by decide)
  refine ⟨fun q hq => ?_, by rw [hV]; exact hm, h14', hz, fun q hq => by rw [hx]; exact hx0 q hq,
    fun r hr => k.1 r hr, k.2.1, k.2.2⟩
  rw [show VG.Proof.Bignum.X86_64.word t.mem B (eo + 16 * j + 8 * q) = VG.Proof.Bignum.X86_64.q128 (t.mem.readW (VG.Proof.Bignum.X86_64.off B (eo + 16 * j)) 128) q from
      (hrd t.mem _ hq).symm, hV]
  show VG.Proof.Bignum.X86_64.q128 (X2 ^^^ ((X1 ^^^ X2) &&& s.xmm .xmm0)) q = _
  rw [VG.Proof.Bignum.X86_64.q128_xor, VG.Proof.Bignum.X86_64.q128_and, VG.Proof.Bignum.X86_64.q128_xor, hx0 q hq, hrd _ _ hq, hrd _ _ hq]

/-! ## The selection -/

/-- `sseSelect`'s setup: the mask in both quadwords of `xmm0`, `r13 = 2 ⌈w / 2⌉`, `r14 = 0`. -/
theorem selSetup_ok {s : State} {w : Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 31) :
    WP isa (.block [.xop (.movq .xmm0 .rbp), .xop (.bin .punpcklqdq .xmm0 .xmm0), .mov .r13 (.reg .r12),
        .alu .add .r13 (.imm 1), .shift .shr .r13 1, .alu .add .r13 (.reg .r13), .mov32 .r14 (.imm 0)]) s
      fun t => (∀ q < 2, VG.Proof.Bignum.X86_64.q128 (t.xmm .xmm0) q = s.gpr .rbp) ∧ t.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) ∧
        t.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r13, .r14] s t := by
  let s₂ := (s.setXmm .xmm0 ((0 : BitVec 64) ++ s.gpr .rbp)).setXmm .xmm0
    (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ s.gpr .rbp) ((0 : BitVec 64) ++ s.gpr .rbp))
  have h13 : (BitVec.ofNat 64 w + 1) >>> 1 + (BitVec.ofNat 64 w + 1) >>> 1 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) := by
    rw [ofNat_add_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  rw [WP.block_cons_iff]
  refine ⟨s.setXmm .xmm0 ((0 : BitVec 64) ++ s.gpr .rbp), rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, rfl, ?_⟩
  refine WP.mono (WP.keep [.r13, .r14] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) ∧
      t.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧ t.mem = s.mem ∧ t.xmm = s₂.xmm)
    (by xrun [show s₂.gpr = s.gpr from rfl, h12, h13]; exact ⟨rfl, rfl⟩) rfl) fun t ⟨⟨h13, h14, hm, hx⟩, k⟩ =>
    ⟨fun q hq => by rw [hx]; exact VG.Proof.Bignum.X86_64.q128_dup _ hq, h13, h14, hm, fun r hr => k.1 r hr, k.2.1, k.2.2⟩

/-- A 16-byte write changes only its bytes. -/
theorem writeW128_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.Outside base d 16 m (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) := by
  intro x hx
  apply Mem.write_apply (n := 16)
  simp only [VG.Proof.Bignum.X86_64.ofs] at hx
  have : (x - VG.Proof.Bignum.X86_64.off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- After `j` pairs of `sseSelect`, of `n`. -/
structure SseInv (s : State) (B : Addr) (eA eo n : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  keep : VG.Proof.MlKem.X86_64.Keep [.r13, .r14] s t
  r13 : t.gpr .r13 = BitVec.ofNat 64 (2 * n)
  r14 : t.gpr .r14 = BitVec.ofNat 64 (2 * j)
  msk : ∀ q < 2, VG.Proof.Bignum.X86_64.q128 (t.xmm .xmm0) q = VG.Proof.Bignum.X86_64.mask lt
  out : VG.Proof.Bignum.X86_64.Outside B eo (16 * n) s.mem t.mem
  val : ∀ i < 2 * n, VG.Proof.Bignum.X86_64.word t.mem B (eo + 8 * i) =
    if i < 2 * j then (if lt then VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * i) else VG.Proof.Bignum.X86_64.word s.mem B (eo + 8 * i))
    else VG.Proof.Bignum.X86_64.word s.mem B (eo + 8 * i)

/-- `sseSelect`: `[rbx] := rbp ? [r8] : [rbx]` over `w` words, changing at most `w + 1`. -/
theorem sseSelect_ok {s : State} {B : Addr} {Z w eA eo : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {lt : Bool} (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 1) ≤ Z) (ho : eo + 8 * (w + 1) ≤ Z)
    (sA : eo + 8 * (w + 1) ≤ eA ∨ eA + 8 * (w + 1) ≤ eo) :
    WP isa Crt.sseSelect s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eo w) ∧
      VG.Proof.Bignum.X86_64.Outside B eo (8 * (w + 1)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r13, .r14] s t := by
  have hn := hs.nowrap
  have hnw : 16 * ((w + 1) / 2) ≤ 8 * (w + 1) := by omega
  unfold Crt.sseSelect
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.selSetup_ok h12 hw') fun t ⟨hx, h13, h14, hm, k⟩ => ?_)
  have h0 : VG.Proof.Bignum.X86_64.SseInv s B eA eo ((w + 1) / 2) lt 0 t := ⟨k, h13, h14, by rw [← hbp]; exact hx,
    by rw [hm]; exact Outside.refl _ _ _ _, fun i _ => by rw [hm]; simp⟩
  refine WP.mono (wp_upto (a := 0) (N := (w + 1) / 2) (by omega) (VG.Proof.Bignum.X86_64.SseInv s B eA eo ((w + 1) / 2) lt)
    (fun j _ hj t hI => ?_) (fun t h => h) h0) fun t hI => ⟨?_, hI.out.mono (Nat.le_refl _) (by omega), hI.keep⟩
  · have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
    have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo := (hI.keep.gpr (by decide)).trans hbx
    refine WP.mono (VG.Proof.Bignum.X86_64.selPair_ok (hs.congr hI.keep.2.2) t8 tbx hI.r14 hI.r13 hj (by omega) (by omega) (by omega)
      hI.msk) fun t' ⟨hv, hm, h14, hz, hx, k⟩ => ⟨hz, ?_⟩
    have o' : VG.Proof.Bignum.X86_64.Outside B (eo + 16 * j) 16 t.mem t'.mem := by rw [hm]; exact VG.Proof.Bignum.X86_64.writeW128_outside _ _ _ (by omega)
    refine ⟨(hI.keep.trans k).mono (by decide), (k.gpr (by decide)).trans hI.r13, h14, hx,
      hI.out.trans (o'.mono (by omega) (by omega)), fun i hi => ?_⟩
    by_cases hlo : i < 2 * j
    · rw [o'.word (by omega) (by omega), hI.val i hi]
      simp only [hlo, show i < 2 * (j + 1) by omega, ↓reduceIte]
    by_cases hhi : 2 * j + 2 ≤ i
    · rw [o'.word (by omega) (by omega), hI.val i hi]
      simp only [hlo, show ¬ i < 2 * (j + 1) by omega, ↓reduceIte]
    obtain ⟨q, hq, rfl⟩ : ∃ q, q < 2 ∧ i = 2 * j + q := ⟨i - 2 * j, by omega, by omega⟩
    have hA' : VG.Proof.Bignum.X86_64.word t.mem B (eA + 16 * j + 8 * q) = VG.Proof.Bignum.X86_64.word s.mem B (eA + 16 * j + 8 * q) :=
      hI.out.word (by omega) (by omega)
    have hO' : VG.Proof.Bignum.X86_64.word t.mem B (eo + 16 * j + 8 * q) = VG.Proof.Bignum.X86_64.word s.mem B (eo + 16 * j + 8 * q) := by
      rw [show eo + 16 * j + 8 * q = eo + 8 * (2 * j + q) by omega, hI.val _ (by omega)]
      simp only [hlo, ↓reduceIte]
    rw [show eo + 8 * (2 * j + q) = eo + 16 * j + 8 * q by omega,
      show eA + 8 * (2 * j + q) = eA + 16 * j + 8 * q by omega, hv q hq, hA', hO', VG.Proof.Bignum.X86_64.sel_mask]
    simp only [show 2 * j + q < 2 * (j + 1) by omega, ↓reduceIte]
  · cases lt
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact wv_congr fun i hi => by rw [hI.val i (by omega)]; simp
    · simp only [↓reduceIte]
      exact wv_congr2 fun i hi => by rw [hI.val i (by omega)]; simp [show i < 2 * ((w + 1) / 2) by omega]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtExp`. -/
section

/-!
# RSA with the CRT on x86-64: the exponentiation in a prime's workspace

In a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`), with
`Y ≡ R` and `[aXc] ≡ x R`: `tabBuild` writes the table `T_j ≡ x^j R` after
the arrays (`tabBuild_ok`); a window `v` is four squarings, `[aT] := T_v` by
a masked selection from every entry (`tabSel_ok`) and `Y := Y T_v R⁻¹`
(`crtWin_ok`); `expLoop` does two windows for every byte of the exponent,
read from the modulus' header (`crtExpLoop_ok`): `Y ≡ x^d R`.

The values hold if `Y ≡ R` and `[aXc] ≡ x R`, which a proposition `Q` (in
the phases, that `X` divides `n`) gives; the bounds hold whatever.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## What the exponentiation changes -/

theorem slot_mono (w : Nat) {j k : Nat} (h : j ≤ k) : VG.Proof.Bignum.X86_64.slot w j ≤ VG.Proof.Bignum.X86_64.slot w k := by
  unfold VG.Proof.Bignum.X86_64.slot; have := Nat.mul_le_mul_right (8 * (w + 2)) h; omega

/-- Entry `j` of the table is the workspace's array `8 + j`. -/
theorem ent_le (wx : Nat) {j : Nat} (hj : j < 16) :
    VG.Proof.Bignum.X86_64.slot wx (8 + j) + 8 * (wx + 2) ≤ VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx := by
  have := Nat.mul_le_mul_right (8 * (wx + 2)) (show 8 + j + 1 ≤ 24 by omega)
  unfold VG.Proof.Bignum.X86_64.slot VG.Proof.Bignum.X86_64.tabBytes
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- What a window of the exponentiation changes in the prime's workspace:
arrays and header slots. -/
def crtWinRanges (wx : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot wx aAcc, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx aTmp, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx aY, 8 * (wx + 2)),
    (VG.Proof.Bignum.X86_64.slot wx Crt.aT, 8 * (wx + 2)), (8 * Crt.sV, 8), (8 * Crt.sBit, 8), (8 * Crt.sNib, 8), (8 * Crt.sEnt, 8),
    (8 * Crt.sJ, 8)]

/-- What the exponentiation changes: also the exponent's pointer and length,
the byte index, and the table. -/
def crtExpRanges (wx : Nat) : List (Nat × Nat) :=
  (8 * Crt.sExp, 8) :: (8 * Crt.sExpLen, 8) :: (8 * Crt.sI, 8) :: (8 * Crt.sTab, 8) ::
    (VG.Proof.Bignum.X86_64.slot wx 8, VG.Proof.Bignum.X86_64.tabBytes wx) :: VG.Proof.Bignum.X86_64.crtWinRanges wx

theorem crtWinRanges_sub (wx : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.crtWinRanges wx, r ∈ VG.Proof.Bignum.X86_64.crtExpRanges wx := fun _ hr =>
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hr))))

theorem crtWinRanges_ok (wx : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.crtWinRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by
  have := hdr_lt_slot wx 0 (show 31 < 32 by decide)
  have := slot_le (w := wx) (show aAcc < 8 by decide)
  have := slot_le (w := wx) (show aTmp < 8 by decide)
  have := slot_le (w := wx) (show aY < 8 by decide)
  have := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have h1 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx aAcc := VG.Proof.Bignum.X86_64.slot_mono wx (by decide)
  have h2 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx aTmp := VG.Proof.Bignum.X86_64.slot_mono wx (by decide)
  have h3 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx aY := VG.Proof.Bignum.X86_64.slot_mono wx (by decide)
  have h4 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx Crt.aT := VG.Proof.Bignum.X86_64.slot_mono wx (by decide)
  simp only [VG.Proof.Bignum.X86_64.crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn] at * <;> omega

theorem crtExpRanges_ok (wx : Nat) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.crtExpRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx := by
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  intro r hr
  simp only [VG.Proof.Bignum.X86_64.crtExpRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · simp only [Crt.sExp, sFn]; omega
  · simp only [Crt.sExpLen, sFn]; omega
  · simp only [Crt.sI, sFn]; omega
  · simp only [Crt.sTab, sFn]; omega
  · simp only; omega
  · have := VG.Proof.Bignum.X86_64.crtWinRanges_ok wx r hr; omega

/-- The arrays the exponentiation does not change. -/
theorem crtExpRanges_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ Crt.aT) : ∀ r ∈ VG.Proof.Bignum.X86_64.crtExpRanges wx, VG.Proof.Bignum.X86_64.slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx j := by
  have := hdr_lt_slot wx j (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) h1
  have s2 := slot_sep (w := wx) h2
  have s3 := slot_sep (w := wx) h3
  have s4 := slot_sep (w := wx) h4
  have s8 := slot_le (w := wx) hj
  simp only [VG.Proof.Bignum.X86_64.crtExpRanges, VG.Proof.Bignum.X86_64.crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sTab, Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn] at * <;>
    omega

/-- A header slot that a window does not change. -/
theorem crtWinRanges_hdr (wx : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ Crt.sV) (h2 : k ≠ Crt.sBit)
    (h3 : k ≠ Crt.sNib) (h4 : k ≠ Crt.sEnt) (h5 : k ≠ Crt.sJ) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.crtWinRanges wx, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have := hdr_lt_slot wx aAcc hk
  have := hdr_lt_slot wx aTmp hk
  have := hdr_lt_slot wx aY hk
  have := hdr_lt_slot wx Crt.aT hk
  simp only [VG.Proof.Bignum.X86_64.crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn] at * <;> omega

/-- The table's entries are past what a window changes. -/
theorem crtWinRanges_ent (wx : Nat) (j : Nat) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.crtWinRanges wx, VG.Proof.Bignum.X86_64.slot wx (8 + j) + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx (8 + j) :=
  fun r hr => Or.inr (by have := (VG.Proof.Bignum.X86_64.crtWinRanges_ok wx r hr).2; have := VG.Proof.Bignum.X86_64.slot_mono wx (show 8 ≤ 8 + j by omega); omega)

/-! ## The prime's workspace -/

/-- What the exponentiation keeps in the workspace at `P` (`w_X` words) and
its table: the prime `X` (and its low word, for `-X⁻¹`), and `Xc`. -/
structure CExpCtx (t : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) : Prop where
  good : Good t P (VG.Proof.Bignum.X86_64.slot wx 8) wx minv
  scrT : VG.Proof.Bignum.X86_64.Scr t P (VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx)
  n : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aN) wx = X
  inv : ((VG.Proof.Bignum.X86_64.word t.mem P (VG.Proof.Bignum.X86_64.slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx = Xc

theorem CExpCtx.ld {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off P (8 * i)) 8 :=
  hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)

theorem CExpCtx.st {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions t.wr (VG.Proof.Bignum.X86_64.off P (8 * i)) 8 :=
  hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega)

/-- What changes only within the exponentiation's ranges keeps the context. -/
theorem CExpCtx.of_frm {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hf : Frm P (VG.Proof.Bignum.X86_64.crtExpRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : VG.Proof.Bignum.X86_64.CExpCtx t' P wx minv X Xc := by
  have hn := hc.scrT.nowrap
  have rN := VG.Proof.Bignum.X86_64.crtExpRanges_arr wx (j := aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rX := VG.Proof.Bignum.X86_64.crtExpRanges_arr wx (j := Crt.aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lX := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hh : ∀ i < 17, VG.Proof.Bignum.X86_64.word t'.mem P (8 * i) = VG.Proof.Bignum.X86_64.word t.mem P (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => Or.inl (by have := VG.Proof.Bignum.X86_64.crtExpRanges_ok wx r hr; omega))
      (by have := hdr_lt_slot wx 8 (show i < 32 by omega); omega)
  exact ⟨⟨hc.good.scr.congr hwr, hdi.trans hc.good.rdi,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (hc.good.hdr.harr j hj)⟩⟩, hc.scrT.congr hwr,
    by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact hc.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact hc.inv,
    by rw [hf.wv_eq (fun r hr => by have := rX r hr; omega) (by omega)]; exact hc.x⟩

theorem CExpCtx.of_win {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hf : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : VG.Proof.Bignum.X86_64.CExpCtx t' P wx minv X Xc :=
  hc.of_frm (hf.mono (VG.Proof.Bignum.X86_64.crtWinRanges_sub wx)) hwr hdi

/-- The table: `T_j < X`, and `T_j ≡ x^j R` if `Q`; its first entry's
address in `sTab`. -/
structure CTab (m : Mem) (P : Addr) (wx X : Nat) (Q : Prop) (x : Nat) : Prop where
  tab : VG.Proof.Bignum.X86_64.word m P (8 * Crt.sTab) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)
  lt : ∀ j < 16, wv m P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx < X
  val : Q → ∀ j < 16, wv m P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx % X = x ^ j * 2 ^ (64 * wx) % X

theorem CTab.of_win {m m' : Mem} {P : Addr} {wx X : Nat} {Q : Prop} {x : Nat} (h : VG.Proof.Bignum.X86_64.CTab m P wx X Q x)
    (hf : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) m m') (hn : P.toNat + (VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx) ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.CTab m' P wx X Q x := by
  have he : ∀ j < 16, wv m' P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx = wv m P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx := fun j hj =>
    hf.wv_eq (fun r hr => by have := VG.Proof.Bignum.X86_64.crtWinRanges_ent wx j r hr; omega) (by have := VG.Proof.Bignum.X86_64.ent_le wx hj; omega)
  refine ⟨?_, fun j hj => (he j hj).symm ▸ h.lt j hj, fun hQ j hj => (he j hj).symm ▸ h.val hQ j hj⟩
  rw [hf.word_eq (VG.Proof.Bignum.X86_64.crtWinRanges_hdr wx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by have := hdr_lt_slot wx 8 (show Crt.sTab < 32 by decide); omega)]
  exact h.tab

/-! ## The table's entries -/

/-- `off P e` moved up an entry, as `nextEnt` computes it. -/
theorem entStep (P : Addr) (e wx : Nat) :
    VG.Proof.Bignum.X86_64.off P e + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2) + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2)) +
      (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2) + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2)))) =
      VG.Proof.Bignum.X86_64.off P (e + 8 * (wx + 2)) := by
  rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
  simp only [BitVec.ofNat_add_ofNat, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc]
  congr 2
  omega

/-- `sEnt` moves up an entry. -/
theorem nextEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) {e : Nat} (he : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off P e) :
    WP isa Crt.nextEnt t fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sEnt)) (VG.Proof.Bignum.X86_64.off P (e + 8 * (wx + 2))) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sEnt))
    (VG.Proof.Bignum.X86_64.off P (e + 8 * (wx + 2)))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  unfold Crt.nextEnt
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sW) (by decide),
    hc.st (i := Crt.sEnt) (by decide), he, hc.good.hdr.hw]
  rw [VG.Proof.Bignum.X86_64.entStep]

/-- `toEnt a`: entry `j`, at `sEnt`, `:= [a]`. -/
theorem toEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) {a j : Nat} (ha : a < 8) (hj : j < 16)
    (he : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + j))) :
    WP isa (seqs (Crt.toEnt a)) t fun t' => wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx a) wx ∧
      VG.Proof.Bignum.X86_64.Outside P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) (8 * wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hT := VG.Proof.Bignum.X86_64.ent_le wx hj
  have sa := slot_le (w := wx) ha
  have sp := slot_sep (w := wx) (show a ≠ 8 + j by omega)
  unfold Crt.toEnt
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 wx ∧
      t₁.gpr .rsi = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx a) ∧ t₁.gpr .rbx = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) ∧ t₁.mem = t.mem)
    (by xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := sArr a) (by unfold sArr; omega),
      hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sW) (by decide), hc.good.hdr.harr a ha, he,
      hc.good.hdr.hw]) rfl) fun t₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hc.scrT.congr k₁.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega) (by omega) (by omega) (fun i hi => hs₁.ld (by omega))
    (fun i hi => hs₁.st (by omega)) (fun i hi b hb => by rw [VG.Proof.Bignum.X86_64.ofs_off P (by omega)]; omega))
    fun t' ⟨hv, _, ho', k⟩ => ⟨by rw [hv, hm₁], by rw [hm₁] at ho'; exact ho', (k₁.trans k).mono (by decide)⟩

/-! ## Reading an entry -/

theorem xor_eq_zero_iff {x y : BitVec 64} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· ^^^ y) h
    simpa [BitVec.xor_assoc] using this
  · rintro rfl
    simp

theorem ofNat64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; rfl

/-- The selection's start: `sEnt := sTab`, `sJ := 0`. -/
theorem selInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (ht : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sTab) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sTab)), .store (hdr Crt.sEnt) .rax, .mov32 .rax (.imm 0),
      .store (hdr Crt.sJ) .rax]) t fun t' =>
      t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sEnt)) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8))).writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sJ))
        (BitVec.setWidth 64 (0 : BitVec 32)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sEnt))
      (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8))).writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sJ)) (BitVec.setWidth 64 (0 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sTab) (by decide), ht,
      hc.st (i := Crt.sEnt) (by decide), hc.st (i := Crt.sJ) (by decide)]) rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩

/-- An entry's mask and the selection's bases. -/
theorem selHead_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) {j v : Nat} (hj : j < 16) (hv : v < 16)
    (hJ : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j) (hN : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hE : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + j))) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sJ)), .alu .xor .rax (.mem (hdr Crt.sNib)), .alu .cmp .rax (.imm 1),
        .alu .sbb .rbp (.reg .rbp), .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr Crt.sEnt)),
        .mov .rsi (.mem (hdr (sArr Crt.aT))), .mov .rbx (.mem (hdr (sArr Crt.aT)))]) t fun t' =>
      t'.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide (j = v)) ∧ t'.gpr .r12 = BitVec.ofNat 64 wx ∧
      t'.gpr .r8 = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) ∧ t'.gpr .rsi = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) ∧
      t'.gpr .rbx = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) ∧ t'.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r12, .r8, .rsi, .rbx] t t' := by
  refine WP.mono (WP.keep [.rax, .rbp, .r12, .r8, .rsi, .rbx] (Q := fun t' =>
      (∃ b : Bool, b = decide (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 v = 0) ∧ t'.gpr .rbp = VG.Proof.Bignum.X86_64.mask b) ∧
      t'.gpr .r12 = BitVec.ofNat 64 wx ∧ t'.gpr .r8 = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) ∧
      t'.gpr .rsi = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) ∧ t'.gpr .rbx = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) ∧ t'.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sJ) (by decide), hc.ld (i := Crt.sNib) (by decide),
      hc.ld (i := sW) (by decide), hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sArr Crt.aT) (by decide), hJ, hN,
      hE, hc.good.hdr.hw, hc.good.hdr.harr Crt.aT (by decide)]
    exact ⟨_, VG.Proof.Bignum.X86_64.decide_lt_one _, rfl⟩) rfl)
    fun t' ⟨⟨⟨b, hb, hbp⟩, h12, h8, hsi, hbx, hm⟩, k⟩ => ⟨?_, h12, h8, hsi, hbx, hm, k⟩
  rw [hbp, hb]
  congr 1
  exact decide_eq_decide.mpr (xor_eq_zero_iff.trans (VG.Proof.Bignum.X86_64.ofNat64_inj (by omega) (by omega)))

/-- The entry's index up, `ZF` when it reaches 16. -/
theorem selEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) {j : Nat} (hj : j < 16) (hJ : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sJ)), .alu .add .rax (.imm 1), .store (hdr Crt.sJ) .rax,
      .alu .cmp .rax (.imm 16)]) t fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sJ)) (BitVec.ofNat 64 (j + 1)) ∧ t'.zf = some (decide (j + 1 = 16)) ∧
        VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sJ))
      (BitVec.ofNat 64 (j + 1)) ∧ t'.zf = some (decide (j + 1 = 16))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sJ) (by decide), hc.st (i := Crt.sJ) (by decide), hJ,
      ofNat_add_one]
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show 16 < 2 ^ 64 by decide)]) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩

theorem slot_succ (w k : Nat) : VG.Proof.Bignum.X86_64.slot w (k + 1) = VG.Proof.Bignum.X86_64.slot w k + 8 * (w + 2) := by
  unfold VG.Proof.Bignum.X86_64.slot; rw [Nat.succ_mul]; omega

/-- What the selection changes: `T`, the entry and its index. -/
def selRanges (wx : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot wx Crt.aT, 8 * (wx + 2)), (8 * Crt.sEnt, 8), (8 * Crt.sJ, 8)]

theorem selRanges_sub (wx : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.selRanges wx, r ∈ VG.Proof.Bignum.X86_64.crtWinRanges wx := by
  simp only [VG.Proof.Bignum.X86_64.selRanges, VG.Proof.Bignum.X86_64.crtWinRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> simp

/-- After `j` entries of the selection of entry `v` from `t₀`. -/
structure TabSelInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc v : Nat) (j : Nat) (t : State) :
    Prop where
  ctx : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc
  nib : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v
  ent : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + j))
  idx : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 j
  val : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx =
    if v < j then wv t₀.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + v)) wx else wv t₀.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx
  frm : Frm P (VG.Proof.Bignum.X86_64.selRanges wx) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

/-- The selection's loop body, as a list. -/
def selBody : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr Crt.sJ)), .alu .xor .rax (.mem (hdr Crt.sNib)), .alu .cmp .rax (.imm 1),
      .alu .sbb .rbp (.reg .rbp), .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr Crt.sEnt)),
      .mov .rsi (.mem (hdr (sArr Crt.aT))), .mov .rbx (.mem (hdr (sArr Crt.aT)))],
    Crt.sseSelect, Crt.nextEnt,
    .block [.mov .rax (.mem (hdr Crt.sJ)), .alu .add .rax (.imm 1), .store (hdr Crt.sJ) .rax,
      .alu .cmp .rax (.imm 16)]]

theorem tabSelect_eq : Crt.tabSelect = [.block [.mov .rax (.mem (hdr Crt.sTab)), .store (hdr Crt.sEnt) .rax,
    .mov32 .rax (.imm 0), .store (hdr Crt.sJ) .rax], .loop (seqs VG.Proof.Bignum.X86_64.selBody) .ne] := rfl

/-- Entry `j` of the selection. -/
theorem selStep_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v j : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16) (hj : j < 16) (hI : VG.Proof.Bignum.X86_64.TabSelInv t₀ P wx minv X Xc v j t) :
    WP isa (seqs VG.Proof.Bignum.X86_64.selBody) t fun t' => t'.zf = some (decide (j + 1 = 16)) ∧
      VG.Proof.Bignum.X86_64.TabSelInv t₀ P wx minv X Xc v (j + 1) t' := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hE := VG.Proof.Bignum.X86_64.ent_le wx hj
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hTE := slot_sep (w := wx) (show Crt.aT ≠ 8 + j by unfold Crt.aT; omega)
  have hE8 := VG.Proof.Bignum.X86_64.slot_mono wx (show 8 ≤ 8 + j by omega)
  simp only [VG.Proof.Bignum.X86_64.selBody, seqs]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.selHead_ok hc hj hv hI.idx hI.nib hI.ent)
    fun t₁ ⟨hbp, h12, h8, hsi, hbx, hm₁, k₁⟩ => ?_)
  have hs₁ := hc.scrT.congr k₁.2.2
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.sseSelect_ok hs₁ h8 hbx h12 hbp (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun t₂ ⟨hsel₂, o₂, k₂⟩ => ?_)
  have f₂ : Frm P (VG.Proof.Bignum.X86_64.selRanges wx) t₁.mem t₂.mem :=
    Frm.of_outside (o₂.mono (o' := VG.Proof.Bignum.X86_64.slot wx Crt.aT) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega))
      (by simp [VG.Proof.Bignum.X86_64.selRanges])
  have hc₂ : VG.Proof.Bignum.X86_64.CExpCtx t₂ P wx minv X Xc :=
    hc.of_win ((by rw [hm₁]; exact Frm.refl _ _ _ : Frm P (crtWinRanges wx) t.mem t₁.mem).trans
      (f₂.mono (VG.Proof.Bignum.X86_64.selRanges_sub wx))) (k₂.2.2.trans k₁.2.2) ((k₂.gpr (by decide)).trans (k₁.gpr (by decide)))
  have hh₂ : ∀ k < 32, VG.Proof.Bignum.X86_64.word t₂.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t.mem P (8 * k) := fun k hk => by
    rw [o₂.word (by have := hdr_lt_slot wx Crt.aT hk; omega) (by omega), hm₁]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.nextEnt_ok (e := VG.Proof.Bignum.X86_64.slot wx (8 + j)) hc₂ (by rw [hh₂ _ (by decide)]; exact hI.ent)) fun t₃ ⟨hm₃, k₃⟩ => ?_)
  have o₃ := VG.Proof.Bignum.X86_64.writeW_outside t₂.mem P (d := 8 * Crt.sEnt) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + j) + 8 * (wx + 2))) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm P (VG.Proof.Bignum.X86_64.selRanges wx) t₂.mem t₃.mem := Frm.of_outside o₃ (by simp [VG.Proof.Bignum.X86_64.selRanges])
  have hc₃ := hc₂.of_win (f₃.mono (VG.Proof.Bignum.X86_64.selRanges_sub wx)) k₃.2.2 (k₃.gpr (by decide))
  refine WP.mono (VG.Proof.Bignum.X86_64.selEnd_ok hc₃ hj (by
    rw [hm₃, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₂ _ (by decide)]; exact hI.idx))
    fun t' ⟨hm', hz', k'⟩ => ⟨hz', ?_⟩
  have o₄ := VG.Proof.Bignum.X86_64.writeW_outside t₃.mem P (d := 8 * Crt.sJ) (BitVec.ofNat 64 (j + 1)) (by decide)
  rw [← hm'] at o₄
  have f₄ : Frm P (VG.Proof.Bignum.X86_64.selRanges wx) t₃.mem t'.mem := Frm.of_outside o₄ (by simp [VG.Proof.Bignum.X86_64.selRanges])
  have hTv : wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx = wv t₂.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx := by
    rw [o₄.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sJ < 32 by decide); omega) (by omega),
      o₃.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide); omega) (by omega)]
  have hEv : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx = wv t₀.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx :=
    hI.frm.wv_eq (fun r hr => by
      have := hdr_lt_slot wx (8 + j) (show 31 < 32 by decide)
      simp only [VG.Proof.Bignum.X86_64.selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega
      · simp only [Crt.sEnt, sFn]; omega
      · simp only [Crt.sJ, sFn]; omega) (by omega)
  refine ⟨hc₃.of_win (f₄.mono (VG.Proof.Bignum.X86_64.selRanges_sub wx)) k'.2.2 (k'.gpr (by decide)), ?_, ?_, ?_, ?_,
    ((((hI.frm.trans (by rw [hm₁]; exact Frm.refl _ _ _)).trans f₂).trans f₃).trans f₄),
    ((((hI.keep.trans k₁).trans k₂).trans k₃).trans k').mono (by decide)⟩
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₂ _ (by decide)]; exact hI.nib
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hm₃, VG.Proof.Bignum.X86_64.word_writeW_self, ← VG.Proof.Bignum.X86_64.slot_succ, Nat.add_assoc]
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hTv, hsel₂, hm₁, hI.val]
    by_cases hjv : j = v
    · subst hjv
      simp only [decide_true, ↓reduceIte, Nat.lt_succ_self]
      exact hEv
    · simp only [hjv, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hvj : v < j
      · simp only [hvj, ↓reduceIte, show v < j + 1 by omega]
      · simp only [hvj, ↓reduceIte, show ¬ v < j + 1 by omega]

/-- The selection: `[aT] := T_v`. -/
theorem tabSel_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sTab) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)) (hN : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (seqs Crt.tabSelect) t fun t' => VG.Proof.Bignum.X86_64.CExpCtx t' P wx minv X Xc ∧
      wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + v)) wx ∧
      Frm P (VG.Proof.Bignum.X86_64.selRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  rw [VG.Proof.Bignum.X86_64.tabSelect_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t.mem P (d := 8 * Crt.sEnt) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)) (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sEnt)) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8))) P (d := 8 * Crt.sJ)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (VG.Proof.Bignum.X86_64.selRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.selRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.selRanges]))
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have h₁ : VG.Proof.Bignum.X86_64.TabSelInv t₁ P wx minv X Xc v 0 t₁ := by
    refine ⟨hc.of_win (f₁.mono (VG.Proof.Bignum.X86_64.selRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide)), ?_, ?_, ?_, by simp,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self]
    · rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
  refine WP.mono (wp_upto (a := 0) (N := 16) (by decide) (VG.Proof.Bignum.X86_64.TabSelInv t₁ P wx minv X Xc v)
    (fun j _ hj s hI => VG.Proof.Bignum.X86_64.selStep_ok hw hw' hv hj hI) (fun s h => h) h₁) fun t' hI => ?_
  have hEv : wv t₁.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + v)) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + v)) wx :=
    f₁.wv_eq (fun r hr => by
      have := VG.Proof.Bignum.X86_64.slot_mono wx (show 8 ≤ 8 + v by omega)
      simp only [VG.Proof.Bignum.X86_64.selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot wx 8 (show 31 < 32 by decide); omega
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot wx 8 (show 31 < 32 by decide); omega)
      (by have := VG.Proof.Bignum.X86_64.ent_le wx hv; omega)
  refine ⟨hI.ctx, by rw [hI.val]; simp only [hv, ↓reduceIte]; exact hEv, f₁.trans hI.frm, (k₁.trans hI.keep).mono (by decide)⟩

/-! ## A window -/

/-- The window count decremented, `ZF` when it reaches 0. -/
theorem crtBitEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc b : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hb : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b)
    (hb' : b < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]) t
      fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 1)) ∧
        t'.zf = some (decide (b - 1 = 0)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  have hs : ∀ i < 32, InRegions t.wr (VG.Proof.Bignum.X86_64.off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sBit))
      (BitVec.ofNat 64 (b - 1)) ∧ t'.zf = some (decide (b - 1 = 0))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl Crt.sBit (by decide), hs Crt.sBit (by decide), hb,
      ofNat64_pred hb1 (by omega), ofNat64_beq_zero (show b - 1 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- A Montgomery product of `Y ≡ x^E R` and `T ≡ x^v R`: `x^(E+v) R`. -/
theorem mont_mulT {Y Y' T x E v R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = x ^ E * R % m)
    (hT : T % m = x ^ v * R % m) (h : Y' * R % m = Y * T % m) : Y' % m = x ^ (E + v) * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hY, hT, ← Nat.mul_mod, Nat.pow_add]
  congr 1
  grind

/-- `Y := Y² R⁻¹`: `x^E R` becomes `x^(2E) R`. -/
theorem crtSq_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E : Nat} (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X) :
    WP isa (M.mm aY aY aY) t fun t' => VG.Proof.Bignum.X86_64.CExpCtx t' P wx minv X Xc ∧ wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X ∧
      (Q → wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ (2 * E) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, VG.Proof.Bignum.X86_64.word t'.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t.mem P (8 * k)) ∧
      Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good (Nat.le_refl _) hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hY)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hm₁
  have f₁ : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [VG.Proof.Bignum.X86_64.crtWinRanges])
  exact ⟨hc.of_win f₁ k₁.2.2 (k₁.gpr (by decide)), hlt₁, fun hq => VG.Proof.Bignum.mont_sq hR (hYv hq) hm₁,
    fun k hk => ha₁.hslot hk, f₁, k₁⟩

/-- `Y := Y T R⁻¹`: `x^E R` and `T ≡ x^v R` give `x^(E+v) R`. -/
theorem crtMulT_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hT : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx < X)
    (hYv : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hTv : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx % X = x ^ v * 2 ^ (64 * wx) % X) :
    WP isa (M.mm aY aY Crt.aT) t fun t' => VG.Proof.Bignum.X86_64.CExpCtx t' P wx minv X Xc ∧ wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X ∧
      (Q → wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ (E + v) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, VG.Proof.Bignum.X86_64.word t'.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t.mem P (8 * k)) ∧
      Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hc.good (Nat.le_refl _) hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hT)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hm₁
  have f₁ : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [VG.Proof.Bignum.X86_64.crtWinRanges])
  exact ⟨hc.of_win f₁ k₁.2.2 (k₁.gpr (by decide)), hlt₁, fun hq => VG.Proof.Bignum.X86_64.mont_mulT hR (hYv hq) (hTv hq) hm₁,
    fun k hk => ha₁.hslot hk, f₁, k₁⟩

/-- The window's value: `(V >> 4) & 15`. -/
theorem nibMask (V : Nat) (hV : V < 2 ^ 64) :
    (BitVec.ofNat 64 V >>> 4 &&& BitVec.signExtend 64 (15 : BitVec 32)) = BitVec.ofNat 64 (V / 16 % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
    Nat.shiftRight_eq_div_pow, show (BitVec.signExtend 64 (15 : BitVec 32)).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

/-- The block after the squarings: the window into `sNib`, and `sV` up 4 bits. -/
theorem winMid_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc V : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hV : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 60) :
    WP isa (.block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .store (hdr Crt.sV) .rax,
      .shift .shr .rdx 4, .alu .and .rdx (.imm 15), .store (hdr Crt.sNib) .rdx]) t fun t' =>
      t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V))).writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sNib))
        (BitVec.ofNat 64 (V / 16 % 16)) ∧ VG.Proof.MlKem.X86_64.Keep [.rdx, .rax] t t' := by
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun t' => t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sV))
      (BitVec.ofNat 64 (16 * V))).writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sNib)) (BitVec.ofNat 64 (V / 16 % 16))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sV) (by decide),
      hc.st (i := Crt.sNib) (by decide), hV, VG.Proof.Bignum.X86_64.nibMask V (by omega), ← BitVec.ofNat_add]
    rw [show V + V + (V + V) + (V + V + (V + V)) + (V + V + (V + V) + (V + V + (V + V))) = 16 * V by omega])
    rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩

theorem expWin_eq (mul : Nat → Nat → Nat → Prog isa) : Crt.expWin mul =
    [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY,
      .block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .store (hdr Crt.sV) .rax,
        .shift .shr .rdx 4, .alu .and .rdx (.imm 15), .store (hdr Crt.sNib) .rdx]] ++
    (Crt.tabSelect ++ [mul aY aY Crt.aT,
      .block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]]) := rfl

/-- One window: `Y ≡ x^E R` becomes `x^(16 E + v) R` for the window
`v = ⌊V / 16⌋ mod 16` of the value `V` in `sV`, which moves up 4 bits; the
window count `b` drops. -/
theorem crtWin_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E V b : Nat} (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (htab : VG.Proof.Bignum.X86_64.CTab t.mem P wx X Q x) (hw : 2 ≤ wx)
    (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hV : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 56)
    (hb : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa (seqs (Crt.expWin M.mm)) t fun t' => VG.Proof.Bignum.X86_64.CExpCtx t' P wx minv X Xc ∧ VG.Proof.Bignum.X86_64.CTab t'.mem P wx X Q x ∧
      wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X ∧
      (Q → wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ (16 * E + V / 16 % 16) * 2 ^ (64 * wx) % X) ∧
      VG.Proof.Bignum.X86_64.word t'.mem P (8 * Crt.sV) = BitVec.ofNat 64 (16 * V) ∧
      VG.Proof.Bignum.X86_64.word t'.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  rw [VG.Proof.Bignum.X86_64.expWin_eq]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp [VG.Proof.Bignum.X86_64.tabSelect_eq]) ?_
  simp only [seqs]
  -- Four squarings.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.crtSq_ok M hc hw hw' hR hY hYv) fun t₁ ⟨hc₁, hY₁, hYv₁, hh₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.crtSq_ok M hc₁ hw hw' hR hY₁ hYv₁) fun t₂ ⟨hc₂, hY₂, hYv₂, hh₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.crtSq_ok M hc₂ hw hw' hR hY₂ hYv₂) fun t₃ ⟨hc₃, hY₃, hYv₃, hh₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.crtSq_ok M hc₃ hw hw' hR hY₃ hYv₃) fun t₄ ⟨hc₄, hY₄, hYv₄, hh₄, f₄, k₄⟩ => ?_)
  have hh04 : ∀ k < 32, VG.Proof.Bignum.X86_64.word t₄.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t.mem P (8 * k) := fun k hk =>
    (hh₄ k hk).trans ((hh₃ k hk).trans ((hh₂ k hk).trans (hh₁ k hk)))
  have f04 : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t₄.mem := ((f₁.trans f₂).trans f₃).trans f₄
  have k04 : VG.Proof.MlKem.X86_64.Keep mmRegs t t₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  -- The window, and `sV` up.
  refine WP.mono (VG.Proof.Bignum.X86_64.winMid_ok (V := V) hc₄ (by rw [hh04 _ (by decide)]; exact hV) (by omega)) fun t₅ ⟨hm₅, k₅⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t₄.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (16 * V)) (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t₄.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V))) P (d := 8 * Crt.sNib)
    (BitVec.ofNat 64 (V / 16 % 16)) (by decide)
  rw [← hm₅] at o2
  have f₅ : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t₄.mem t₅.mem :=
    (Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.crtWinRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.crtWinRanges]))
  have hc₅ := hc₄.of_win f₅ k₅.2.2 (k₅.gpr (by decide))
  have htab₅ : VG.Proof.Bignum.X86_64.CTab t₅.mem P wx X Q x := htab.of_win (f04.trans f₅) hn
  have hY₅ : wv t₅.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx = wv t₄.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx := by
    rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sNib < 32 by decide); omega) (by omega),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega) (by omega)]
  have hh₅ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sNib → VG.Proof.Bignum.X86_64.word t₅.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t.mem P (8 * k) :=
    fun k hk h1 h2 => by
      rw [hm₅, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1),
        hh04 k hk]
  have hv16 : V / 16 % 16 < 16 := Nat.mod_lt _ (by decide)
  -- `T := T_v`.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.tabSelect_eq]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.tabSel_ok hc₅ hw hw' hv16 (by rw [hh₅ _ (by decide) (by decide) (by decide)]; exact htab.tab)
    (by rw [hm₅, VG.Proof.Bignum.X86_64.word_writeW_self])) fun t₆ ⟨hc₆, hT₆, f₆, k₆⟩ => ?_
  have f₆' : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t₅.mem t₆.mem := f₆.mono (VG.Proof.Bignum.X86_64.selRanges_sub wx)
  have hY₆ : wv t₆.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx = wv t₅.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx :=
    f₆.wv_eq (fun r hr => by
      have := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
      simp only [VG.Proof.Bignum.X86_64.selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega) (by omega)
  have hh₆ : ∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → VG.Proof.Bignum.X86_64.word t₆.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t₅.mem P (8 * k) :=
    fun k hk h1 h2 => f₆.word_eq (fun r hr => by
      have := hdr_lt_slot wx Crt.aT hk
      simp only [VG.Proof.Bignum.X86_64.selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega
      · simp only [Crt.sEnt, sFn] at h1 ⊢; omega
      · simp only [Crt.sJ, sFn] at h2 ⊢; omega) (by omega)
  have htab₆ : VG.Proof.Bignum.X86_64.CTab t₆.mem P wx X Q x := htab₅.of_win f₆' hn
  simp only [seqs]
  -- `Y := Y T`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.crtMulT_ok M (Q := Q) (x := x) (E := 16 * E) (v := V / 16 % 16) hc₆ hw hw' hR
    (by rw [hT₆]; exact htab₅.lt _ hv16)
    (fun hq => by rw [hY₆, hY₅, hYv₄ hq, show 2 * (2 * (2 * (2 * E))) = 16 * E by omega])
    (fun hq => by rw [hT₆]; exact htab₅.val hq _ hv16)) fun t₇ ⟨hc₇, hY₇, hYv₇, hh₇, f₇, k₇⟩ => ?_)
  -- The count.
  refine WP.mono (VG.Proof.Bignum.X86_64.crtBitEnd_ok hc₇ (by
    rw [hh₇ _ (by decide), hh₆ _ (by decide) (by decide) (by decide), hh₅ _ (by decide) (by decide) (by decide)]
    exact hb) hb1 hb') fun t' ⟨hm', hz', k'⟩ => ?_
  have o₈ := VG.Proof.Bignum.X86_64.writeW_outside t₇.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm'] at o₈
  have f₈ : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t₇.mem t'.mem := Frm.of_outside o₈ (by simp [VG.Proof.Bignum.X86_64.crtWinRanges])
  have fall : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t'.mem := (((f04.trans f₅).trans f₆').trans f₇).trans f₈
  refine ⟨hc₇.of_win f₈ k'.2.2 (k'.gpr (by decide)), htab.of_win fall hn, ?_, ?_, ?_, ?_, hz', fall,
    ((((k04.trans k₅).trans k₆).trans k₇).trans k').mono (by decide)⟩
  · rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega) (by omega)]; exact hY₇
  · intro hq
    rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega) (by omega)]
    exact hYv₇ hq
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₇ _ (by decide),
      hh₆ _ (by decide) (by decide) (by decide), hm₅, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]

/-! ## The windows of a byte -/

/-- After `j` windows of the byte `v` from `t₀`, where `Y ≡ x^E R`. -/
structure CWinInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x E v : Nat)
    (j : Nat) (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc
  tab : VG.Proof.Bignum.X86_64.CTab t.mem P wx X Q x
  ylt : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X
  y : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ (E * 16 ^ j + v / 16 ^ (2 - j)) * 2 ^ (64 * wx) % X
  v : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (v * 16 ^ j)
  b : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (2 - j)
  frm : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

theorem win_step {E v j : Nat} (hv : v < 256) (hj : j < 2) :
    16 * (E * 16 ^ j + v / 16 ^ (2 - j)) + v * 16 ^ j / 16 % 16 = E * 16 ^ (j + 1) + v / 16 ^ (2 - (j + 1)) := by
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd] <;>
    omega

/-- Window `j` of the byte `v`. -/
theorem crtWinStep_ok (M : Mont) {t s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256) {j : Nat}
    (hj : j < 2) (hI : VG.Proof.Bignum.X86_64.CWinInv t P wx minv X Xc Q x E v j s) :
    WP isa (seqs (Crt.expWin M.mm)) s fun s' => s'.zf = some (decide (j + 1 = 2)) ∧
      VG.Proof.Bignum.X86_64.CWinInv t P wx minv X Xc Q x E v (j + 1) s' := by
  have hp : 16 ^ j ≤ 16 := by rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide
  refine WP.mono (VG.Proof.Bignum.X86_64.crtWin_ok M (E := E * 16 ^ j + v / 16 ^ (2 - j)) hI.ctx hI.tab hw hw' hR hI.ylt hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega) hI.b (by omega) (by omega))
    fun s' ⟨hc', htab', hY', hYv', hV', hb', hz', hfr', k'⟩ => ⟨?_, hc', htab', hY', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  · intro hq; rw [hYv' hq, VG.Proof.Bignum.X86_64.win_step hv hj]
  · rw [hV', Nat.pow_succ]; congr 1; rw [Nat.mul_comm 16, Nat.mul_assoc]
  · rw [hb']; congr 1

/-- The two windows of the byte `v`: `Y ≡ x^E R` becomes `x^(256 E + v) R`. -/
theorem crtWins_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256)
    (h0 : VG.Proof.Bignum.X86_64.CWinInv t P wx minv X Xc Q x E v 0 t) :
    WP isa (.loop (seqs (Crt.expWin M.mm)) .ne) t (VG.Proof.Bignum.X86_64.CWinInv t P wx minv X Xc Q x E v 2) :=
  wp_upto (a := 0) (N := 2) (by decide) (VG.Proof.Bignum.X86_64.CWinInv t P wx minv X Xc Q x E v)
    (fun _ _ hj _ hI => VG.Proof.Bignum.X86_64.crtWinStep_ok M hw hw' hR hv hj hI) (fun _ h => h) h0

/-! ## The bytes of the exponent -/

/-- After `i` bytes of the exponent (`L` bytes `eb` at `ep`) from `t₀`. -/
structure CByteInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (ep : Addr) (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc
  tab : VG.Proof.Bignum.X86_64.CTab t.mem P wx X Q x
  ylt : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X
  y : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ VG.Proof.Bignum.X86_64.pre eb i * 2 ^ (64 * wx) % X
  idx : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sExp) = ep
  len : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (VG.Proof.Bignum.X86_64.crtExpRanges wx) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

/-- The loads of the byte's address. -/
theorem crtByteHead1_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hI : VG.Proof.Bignum.X86_64.CByteInv t₀ P wx minv X Xc Q x ep L eb i t) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ VG.Proof.Bignum.X86_64.CByteInv t₀ P wx minv X Xc Q x ep L eb i t₁ := by
  have hc := hI.ctx
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Crt.sI) (by decide),
      hI.e, hI.idx]) rfl)
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  have hf : Frm P (VG.Proof.Bignum.X86_64.crtExpRanges wx) t.mem t₁.mem := by rw [hm]; exact Frm.refl _ _ _
  exact ⟨hc.of_frm hf k.2.2 (k.gpr (by decide)), hm ▸ hI.tab, hm ▸ hI.ylt, hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e,
    hm ▸ hI.len, hI.frm.trans hf, (hI.keep.trans k).mono (by decide)⟩

/-- The byte into `sV`, and the window count 2: the start of the windows. -/
theorem crtByteHead2_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx ≤ VG.Proof.Bignum.X86_64.ofs P (ep + BitVec.ofNat 64 i))
    (hI : VG.Proof.Bignum.X86_64.CByteInv t₀ P wx minv X Xc Q x ep L eb i t) (hax : t.gpr .rax = ep)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
      .mov32 .rax (.imm 2), .store (hdr Crt.sBit) .rax]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sV)) ((eb[i]'(by omega)).setWidth 64)).writeW
        (VG.Proof.Bignum.X86_64.off P (8 * Crt.sBit)) (BitVec.setWidth 64 (2 : BitVec 32)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t₁ ∧
      VG.Proof.Bignum.X86_64.CWinInv t₁ P wx minv X Xc Q x (VG.Proof.Bignum.X86_64.pre eb i) (eb[i]'(by omega)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (VG.Proof.Bignum.X86_64.crtExpRanges_ok wx r hr).2; have := hout i hi; omega)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sV))
      ((eb[i]'(by omega)).setWidth 64)).writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sBit)) (BitVec.setWidth 64 (2 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hax, hcx, byteRead, hrdi, hbi, hc.st (i := Crt.sV) (by decide),
      hc.st (i := Crt.sBit) (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t.mem P (d := 8 * Crt.sV) ((eb[i]'(by omega)).setWidth 64) (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sV)) ((eb[i]'(by omega)).setWidth 64)) P
    (d := 8 * Crt.sBit) (BitVec.setWidth 64 (2 : BitVec 32)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (VG.Proof.Bignum.X86_64.crtWinRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.crtWinRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.crtWinRanges]))
  have hc₁ := hc.of_win f₁ k₁.2.2 (k₁.gpr (by decide))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hYe : wv t₁.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx := by
    rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega) (by omega),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega) (by omega)]
  refine ⟨hc₁, hI.tab.of_win f₁ hn, hYe ▸ hI.ylt, fun hq => ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [hYe, hI.y hq, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 16 ^ 2 from hv),
      Nat.add_zero]
  · rw [o2.word (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self, setWidth_byte, Nat.pow_zero, Nat.pow_zero]
  · rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl

theorem crtByteHead_eq : ([.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
      .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
      .store (hdr Crt.sBit) .rax] : List Instr) =
    ([.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))] : List Instr) ++
    ([.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
      .store (hdr Crt.sBit) .rax] : List Instr) := rfl

/-- One byte of the exponent: its two windows, then the next byte. -/
theorem crtByte_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx ≤ VG.Proof.Bignum.X86_64.ofs P (ep + BitVec.ofNat 64 i))
    (hI : VG.Proof.Bignum.X86_64.CByteInv t₀ P wx minv X Xc Q x ep L eb i t) :
    WP isa (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (Crt.expWin M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ VG.Proof.Bignum.X86_64.CByteInv t₀ P wx minv X Xc Q x ep L eb (i + 1) t' := by
  have hn := hI.ctx.scrT.nowrap
  simp only [seqs]
  rw [VG.Proof.Bignum.X86_64.crtByteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (VG.Proof.Bignum.X86_64.crtByteHead1_ok hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (VG.Proof.Bignum.X86_64.crtByteHead2_ok hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.crtWins_ok M hw hw' hR hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ →
      VG.Proof.Bignum.X86_64.word t₂.mem P (8 * k) = VG.Proof.Bignum.X86_64.word tₐ.mem P (8 * k) := fun k hk h1 h2 h3 h4 h5 => by
    rw [h₂.frm.word_eq (VG.Proof.Bignum.X86_64.crtWinRanges_hdr wx hk h1 h2 h3 h4 h5) (by omega), hm₁,
      hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    hIₐ.len
  have hlen₂' : (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide),
      hidx₂, ofNat_add_one, hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂',
      ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega) (show L < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  have o' := VG.Proof.Bignum.X86_64.writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
  rw [← hm'] at o'
  have f' : Frm P (VG.Proof.Bignum.X86_64.crtExpRanges wx) t₂.mem t'.mem := Frm.of_outside o' (by simp [VG.Proof.Bignum.X86_64.crtExpRanges])
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hYe : wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx = wv t₂.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx :=
    o'.wv (by have := hdr_lt_slot wx aY (show Crt.sI < 32 by decide); omega) (by omega)
  refine ⟨hc₂.of_frm f' k'.2.2 (k'.gpr (by decide)), ?_, hYe ▸ h₂.ylt, fun hq => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [o'.word (by decide) (by decide)]; exact h₂.tab.tab,
      fun j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega)
        (by have := VG.Proof.Bignum.X86_64.ent_le wx hj; omega)]; exact h₂.tab.lt j hj,
      fun hq j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega)
        (by have := VG.Proof.Bignum.X86_64.ent_le wx hj; omega)]; exact h₂.tab.val hq j hj⟩
  · rw [hYe, h₂.y hq, pre_succ eb (by omega)]
    congr 3
    simp only [Nat.reducePow, Nat.reduceSub, Nat.pow_zero, Nat.div_one]
    omega
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm P (VG.Proof.Bignum.X86_64.crtExpRanges wx) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside tₐ.mem P _ (d := 8 * Crt.sV) (by decide))
        (by simp [VG.Proof.Bignum.X86_64.crtExpRanges, VG.Proof.Bignum.X86_64.crtWinRanges])).trans
        (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ P _ (d := 8 * Crt.sBit) (by decide))
          (by simp [VG.Proof.Bignum.X86_64.crtExpRanges, VG.Proof.Bignum.X86_64.crtWinRanges]))
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (VG.Proof.Bignum.X86_64.crtWinRanges_sub wx))).trans f'
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-! ## The table -/

/-- The table's base, past the last array, into `sTab` and `sEnt`. -/
theorem tabInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) :
    WP isa (.block [.mov .rax (.mem (hdr (sArr aOne))), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
      .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx),
      .store (hdr Crt.sTab) .rax, .store (hdr Crt.sEnt) .rax]) t fun t' =>
      t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sTab)) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8))).writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sEnt))
        (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sTab))
      (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8))).writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sEnt)) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := sArr aOne) (by decide), hc.ld (i := sW) (by decide),
    hc.st (i := Crt.sTab) (by decide), hc.st (i := Crt.sEnt) (by decide), hc.good.hdr.harr aOne (by decide),
    hc.good.hdr.hw]
  rw [VG.Proof.Bignum.X86_64.entStep, ← VG.Proof.Bignum.X86_64.slot_succ]
  rfl

/-- `sBit := 14`, the count of the table's products. -/
theorem cnt14_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) :
    WP isa (.block [.mov32 .rax (.imm 14), .store (hdr Crt.sBit) .rax]) t fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sBit)) (BitVec.ofNat 64 14) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sBit))
      (BitVec.ofNat 64 14)) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sBit) (by decide)]
  rfl

/-- What the table's build changes: the products' arrays, its slots and the table. -/
def buildRanges (wx : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot wx aAcc, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx aTmp, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx Crt.aT, 8 * (wx + 2)),
    (8 * Crt.sTab, 8), (8 * Crt.sEnt, 8), (8 * Crt.sBit, 8), (VG.Proof.Bignum.X86_64.slot wx 8, VG.Proof.Bignum.X86_64.tabBytes wx)]

theorem buildRanges_sub (wx : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.buildRanges wx, r ∈ VG.Proof.Bignum.X86_64.crtExpRanges wx := by
  simp only [VG.Proof.Bignum.X86_64.buildRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [VG.Proof.Bignum.X86_64.crtExpRanges, VG.Proof.Bignum.X86_64.crtWinRanges]

/-- `Y` is past what the build changes. -/
theorem buildRanges_y (wx : Nat) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.buildRanges wx, VG.Proof.Bignum.X86_64.slot wx aY + 8 * wx ≤ r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx aY := by
  have := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) (show aY ≠ aAcc by decide)
  have s2 := slot_sep (w := wx) (show aY ≠ aTmp by decide)
  have s3 := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
  have s8 := slot_le (w := wx) (show aY < 8 by decide)
  simp only [VG.Proof.Bignum.X86_64.buildRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sTab, Crt.sEnt, Crt.sBit, sFn] at * <;> omega

/-- After `i` of the table's products from `t₀`: entries `0 … i + 1`
written, `T ≡ x^(i+1) R` the last. -/
structure BuildInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (i : Nat) (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc
  tab : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sTab) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)
  ent : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sEnt) = VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + (i + 1)))
  cnt : VG.Proof.Bignum.X86_64.word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (14 - i)
  tlt : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx < X
  tval : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx % X = x ^ (i + 1) * 2 ^ (64 * wx) % X
  elt : ∀ j < i + 2, wv t.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx < X
  eval : Q → ∀ j < i + 2, wv t.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx % X = x ^ j * 2 ^ (64 * wx) % X
  frm : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

/-- A product of the table's build. -/
def tabBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul Crt.aT Crt.aT Crt.aXc, Crt.nextEnt] ++ (Crt.toEnt Crt.aT ++
    [.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]])

/-- The table's product `i`. -/
theorem buildStep_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X)
    (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) {i : Nat} (hi : i < 14)
    (hI : VG.Proof.Bignum.X86_64.BuildInv t₀ P wx minv X Xc Q x i t) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.tabBody M.mm)) t
      fun t' => t'.zf = some (decide (i + 1 = 14)) ∧ VG.Proof.Bignum.X86_64.BuildInv t₀ P wx minv X Xc Q x (i + 1) t' := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  unfold VG.Proof.Bignum.X86_64.tabBody
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  -- `T := T Xc`.
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _) hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.x, hc.n]; exact hXN)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁
  rw [hc.n, hc.x] at hm₁
  have f₁ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₁ := hc.of_frm (f₁.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide))
  have he₁ : ∀ j < 16, wv t₁.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx := fun j hj =>
    ha₁.wv_eq (fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have := VG.Proof.Bignum.X86_64.slot_mono wx (show 8 ≤ 8 + j by omega)
      rcases hk with rfl | rfl | rfl
      · exact Or.inr (by have := slot_le (w := wx) (show aAcc < 8 by decide); omega)
      · exact Or.inr (by have := slot_le (w := wx) (show aTmp < 8 by decide); omega)
      · exact Or.inr (by omega)) (by have := VG.Proof.Bignum.X86_64.ent_le wx hj; omega)
  -- `sEnt` up.
  refine WP.mono (VG.Proof.Bignum.X86_64.nextEnt_ok (e := VG.Proof.Bignum.X86_64.slot wx (8 + (i + 1))) hc₁ (by rw [ha₁.hslot (by decide)]; exact hI.ent))
    fun t₂ ⟨hm₂, k₂⟩ => ?_
  have o₂ := VG.Proof.Bignum.X86_64.writeW_outside t₁.mem P (d := 8 * Crt.sEnt) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx (8 + (i + 1)) + 8 * (wx + 2))) (by decide)
  rw [← hm₂] at o₂
  have f₂ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₁.mem t₂.mem := Frm.of_outside o₂ (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₂ := hc₁.of_frm (f₂.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₂.2.2 (k₂.gpr (by decide))
  have hT₂ : wv t₂.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx = wv t₁.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx :=
    o₂.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide); omega) (by omega)
  have he₂ : ∀ j < 16, wv t₂.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx = wv t₁.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx := fun j hj =>
    o₂.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sEnt < 32 by decide); omega) (by have := VG.Proof.Bignum.X86_64.ent_le wx hj; omega)
  -- Entry `i + 2 := T`.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [Crt.toEnt]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.toEnt_ok hc₂ hw hw' (a := Crt.aT) (j := i + 2) (by decide) (by omega) (by
    rw [hm₂, VG.Proof.Bignum.X86_64.word_writeW_self, ← VG.Proof.Bignum.X86_64.slot_succ]; rfl)) fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_
  have hE := VG.Proof.Bignum.X86_64.ent_le wx (show i + 2 < 16 by omega)
  have hE8 := VG.Proof.Bignum.X86_64.slot_mono wx (show 8 ≤ 8 + (i + 2) by omega)
  have f₃ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₂.mem t₃.mem :=
    Frm.of_outside (o₃.mono (o' := VG.Proof.Bignum.X86_64.slot wx 8) (n' := VG.Proof.Bignum.X86_64.tabBytes wx) hE8 (by omega)) (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₃ := hc₂.of_frm (f₃.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₃.2.2 (k₃.gpr (by decide))
  have hh₃ : ∀ k < 32, VG.Proof.Bignum.X86_64.word t₃.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t₂.mem P (8 * k) := fun k hk =>
    o₃.word (by have := hdr_lt_slot wx (8 + (i + 2)) hk; omega) (by omega)
  have hT8 : VG.Proof.Bignum.X86_64.slot wx Crt.aT + 8 * (wx + 2) ≤ VG.Proof.Bignum.X86_64.slot wx (8 + (i + 2)) := by
    have := VG.Proof.Bignum.X86_64.slot_mono wx (show Crt.aT + 1 ≤ 8 + (i + 2) by unfold Crt.aT; omega)
    rw [VG.Proof.Bignum.X86_64.slot_succ] at this; omega
  have hT₃ : wv t₃.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx = wv t₂.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx :=
    o₃.wv (by omega) (by omega)
  simp only [seqs]
  -- The count.
  refine WP.mono (VG.Proof.Bignum.X86_64.crtBitEnd_ok hc₃ (b := 14 - i) (by rw [hh₃ _ (by decide), hm₂,
                           hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₁.hslot (by decide)]; exact hI.cnt) (by omega)
    (by omega)) fun t' ⟨hm', hz', k'⟩ => ⟨by rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega), ?_⟩
  have o₄ := VG.Proof.Bignum.X86_64.writeW_outside t₃.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (14 - i - 1)) (by decide)
  rw [← hm'] at o₄
  have f₄ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₃.mem t'.mem := Frm.of_outside o₄ (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hT' : wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx = wv t₁.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx := by
    rw [o₄.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sBit < 32 by decide); omega) (by omega), hT₃, hT₂]
  have hE' : ∀ j < 16, wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx = wv t₃.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx := fun j hj =>
    o₄.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sBit < 32 by decide); omega) (by have := VG.Proof.Bignum.X86_64.ent_le wx hj; omega)
  -- Entries other than `i + 2` are kept by `toEnt`.
  have hEo : ∀ j < 16, j ≠ i + 2 → wv t₃.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + j)) wx :=
    fun j hj hne => by
      have := slot_sep (w := wx) (show 8 + j ≠ 8 + (i + 2) by omega)
      rw [o₃.wv (by omega) (by have := VG.Proof.Bignum.X86_64.ent_le wx hj; omega), he₂ j hj, he₁ j hj]
  have hTv : Q → wv t₁.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx % X = x ^ (i + 1 + 1) * 2 ^ (64 * wx) % X := fun hq =>
    VG.Proof.Bignum.X86_64.mont_mulT (E := i + 1) (v := 1) hR (hI.tval hq) (by rw [Nat.pow_one]; exact hXc hq) hm₁
  refine ⟨hc₃.of_frm (f₄.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k'.2.2 (k'.gpr (by decide)), ?_, ?_, ?_, by rw [hT']; exact hlt₁,
    fun hq => by rw [hT']; exact hTv hq, fun j hj => ?_, fun hq j hj => ?_,
    (((hI.frm.trans f₁).trans f₂).trans f₃).trans f₄, ((((hI.keep.trans k₁).trans k₂).trans k₃).trans k').mono
      (by decide)⟩
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₃ _ (by decide), hm₂,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₁.hslot (by decide)]; exact hI.tab
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₃ _ (by decide), hm₂, VG.Proof.Bignum.X86_64.word_writeW_self,
      ← VG.Proof.Bignum.X86_64.slot_succ]
    rfl
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]; congr 1
  · rw [hE' j (by omega)]
    by_cases hj2 : j = i + 2
    · subst hj2; rw [hv₃, hT₂]; exact hlt₁
    · rw [hEo j (by omega) hj2]; exact hI.elt j (by omega)
  · rw [hE' j (by omega)]
    by_cases hj2 : j = i + 2
    · subst hj2; rw [hv₃, hT₂]; exact hTv hq
    · rw [hEo j (by omega) hj2]; exact hI.eval hq j (by omega)

/-- The table's first two entries, `T` and the count. -/
def tabPre : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr (sArr aOne))), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx),
    .store (hdr Crt.sTab) .rax, .store (hdr Crt.sEnt) .rax]] ++ (Crt.toEnt aY ++ ([Crt.nextEnt] ++
    (Crt.toEnt Crt.aXc ++ (Crt.copyArr Crt.aT Crt.aXc ++ [.block [.mov32 .rax (.imm 14), .store (hdr Crt.sBit) .rax]]))))

/-- The table's products. -/
def tabLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .loop (seqs (VG.Proof.Bignum.X86_64.tabBody mul)) .ne

theorem tabBuild_eq (mul : Nat → Nat → Nat → Prog isa) : Crt.tabBuild mul = VG.Proof.Bignum.X86_64.tabPre ++ [VG.Proof.Bignum.X86_64.tabLoop mul] := by
  simp [Crt.tabBuild, VG.Proof.Bignum.X86_64.tabPre, VG.Proof.Bignum.X86_64.tabLoop, VG.Proof.Bignum.X86_64.tabBody]

/-- The table's first two entries: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R`. -/
theorem tabPre_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs VG.Proof.Bignum.X86_64.tabPre) t (VG.Proof.Bignum.X86_64.BuildInv t P wx minv X Xc Q x 0) := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hX0 := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hE0 := VG.Proof.Bignum.X86_64.ent_le wx (show 0 < 16 by decide)
  have hE1 := VG.Proof.Bignum.X86_64.ent_le wx (show 1 < 16 by decide)
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  unfold VG.Proof.Bignum.X86_64.tabPre
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  -- The base.
  refine WP.mono (VG.Proof.Bignum.X86_64.tabInit_ok hc) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t.mem P (d := 8 * Crt.sTab) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)) (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t.mem.writeW (VG.Proof.Bignum.X86_64.off P (8 * Crt.sTab)) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8))) P (d := 8 * Crt.sEnt)
    (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.buildRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.buildRanges]))
  have hc₁ := hc.of_frm (f₁.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide))
  -- `T_0 := Y`.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [Crt.toEnt]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.toEnt_ok hc₁ hw hw' (a := aY) (j := 0) (by decide) (by decide) (by
    rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self])) fun t₂ ⟨hv₂, o₃, k₂⟩ => ?_
  have f₂ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₁.mem t₂.mem :=
    Frm.of_outside (o₃.mono (o' := VG.Proof.Bignum.X86_64.slot wx 8) (n' := VG.Proof.Bignum.X86_64.tabBytes wx) (Nat.le_refl _) (by omega)) (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₂ := hc₁.of_frm (f₂.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₂.2.2 (k₂.gpr (by decide))
  have hh₂ : ∀ k < 32, VG.Proof.Bignum.X86_64.word t₂.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t₁.mem P (8 * k) := fun k hk =>
    o₃.word (by have := hdr_lt_slot wx (8 + 0) hk; omega) (by omega)
  -- `sEnt` up.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  refine WP.mono (VG.Proof.Bignum.X86_64.nextEnt_ok (e := VG.Proof.Bignum.X86_64.slot wx 8) hc₂ (by rw [hh₂ _ (by decide), hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]))
    fun t₃ ⟨hm₃, k₃⟩ => ?_
  have o₄ := VG.Proof.Bignum.X86_64.writeW_outside t₂.mem P (d := 8 * Crt.sEnt) (VG.Proof.Bignum.X86_64.off P (VG.Proof.Bignum.X86_64.slot wx 8 + 8 * (wx + 2))) (by decide)
  rw [← hm₃] at o₄
  have f₃ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₂.mem t₃.mem := Frm.of_outside o₄ (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₃ := hc₂.of_frm (f₃.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₃.2.2 (k₃.gpr (by decide))
  -- `T_1 := Xc`.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [Crt.toEnt]) (by simp [Crt.copyArr]) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.toEnt_ok hc₃ hw hw' (a := Crt.aXc) (j := 1) (by decide) (by decide) (by
    rw [hm₃, VG.Proof.Bignum.X86_64.word_writeW_self, ← VG.Proof.Bignum.X86_64.slot_succ])) fun t₄ ⟨hv₄, o₅, k₄⟩ => ?_
  have hE01 := slot_sep (w := wx) (show 8 + 0 ≠ 8 + 1 by decide)
  have f₄ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₃.mem t₄.mem :=
    Frm.of_outside (o₅.mono (o' := VG.Proof.Bignum.X86_64.slot wx 8) (n' := VG.Proof.Bignum.X86_64.tabBytes wx) (VG.Proof.Bignum.X86_64.slot_mono wx (by decide)) (by omega))
      (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₄ := hc₃.of_frm (f₄.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₄.2.2 (k₄.gpr (by decide))
  have hh₄ : ∀ k < 32, VG.Proof.Bignum.X86_64.word t₄.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t₃.mem P (8 * k) := fun k hk =>
    o₅.word (by have := hdr_lt_slot wx (8 + 1) hk; omega) (by omega)
  -- `T := Xc`.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [Crt.copyArr]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.copyArr_ok hc₄.good (Nat.le_refl _) (by omega) (by omega) (o := Crt.aT) (a := Crt.aXc)
    (by decide) (by decide) (by decide)) fun t₅ ⟨hv₅, o₆, k₅⟩ => ?_
  have f₅ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₄.mem t₅.mem :=
    Frm.of_outside (o₆.mono (o' := VG.Proof.Bignum.X86_64.slot wx Crt.aT) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega))
      (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₅ := hc₄.of_frm (f₅.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₅.2.2 (k₅.gpr (by decide))
  have hh₅ : ∀ k < 32, VG.Proof.Bignum.X86_64.word t₅.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t₄.mem P (8 * k) := fun k hk =>
    o₆.word (by have := hdr_lt_slot wx Crt.aT hk; omega) (by omega)
  have hT8 : ∀ j, VG.Proof.Bignum.X86_64.slot wx Crt.aT + 8 * (wx + 2) ≤ VG.Proof.Bignum.X86_64.slot wx (8 + j) := fun j => by
    have := VG.Proof.Bignum.X86_64.slot_mono wx (show 8 ≤ 8 + j by omega); omega
  simp only [seqs]
  -- The count.
  refine WP.mono (VG.Proof.Bignum.X86_64.cnt14_ok hc₅) fun t₆ ⟨hm₆, k₆⟩ => ?_
  have o₇ := VG.Proof.Bignum.X86_64.writeW_outside t₅.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 14) (by decide)
  rw [← hm₆] at o₇
  have f₆ : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t₅.mem t₆.mem := Frm.of_outside o₇ (by simp [VG.Proof.Bignum.X86_64.buildRanges])
  have hc₆ := hc₅.of_frm (f₆.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx)) k₆.2.2 (k₆.gpr (by decide))
  have f06 : Frm P (VG.Proof.Bignum.X86_64.buildRanges wx) t.mem t₆.mem := ((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆
  have k06 : VG.Proof.MlKem.X86_64.Keep mmRegs t t₆ := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  -- Entries 0 and 1, and `T`, at `t₆`.
  have hX₄ : wv t₄.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx = Xc := hc₄.x
  have e0 : wv t₆.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + 0)) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx := by
    rw [o₇.wv (by have := hdr_lt_slot wx (8 + 0) (show Crt.sBit < 32 by decide); omega) (by omega),
      o₆.wv (by have := hT8 0; omega) (by omega),
      o₅.wv (by omega) (by omega), o₄.wv (by have := hdr_lt_slot wx (8 + 0) (show Crt.sEnt < 32 by decide); omega)
        (by omega), hv₂]
    exact f₁.wv_eq (VG.Proof.Bignum.X86_64.buildRanges_y wx) (by omega)
  have e1 : wv t₆.mem P (VG.Proof.Bignum.X86_64.slot wx (8 + 1)) wx = Xc := by
    rw [o₇.wv (by have := hdr_lt_slot wx (8 + 1) (show Crt.sBit < 32 by decide); omega) (by omega),
      o₆.wv (by have := hT8 1; omega) (by omega), hv₄]
    exact hc₃.x
  have eT : wv t₆.mem P (VG.Proof.Bignum.X86_64.slot wx Crt.aT) wx = Xc := by
    rw [o₇.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sBit < 32 by decide); omega) (by omega), hv₅, hX₄]
  refine ⟨hc₆, ?_, ?_, ?_, by rw [eT]; exact hXN, fun hq => by rw [eT, Nat.zero_add, Nat.pow_one]; exact hXc hq,
    fun j hj => ?_, fun hq j hj => ?_, f06, k06⟩
  · rw [hm₆, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₅ _ (by decide), hh₄ _ (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₂ _ (by decide), hm₁,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm₆, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₅ _ (by decide), hh₄ _ (by decide), hm₃,
      VG.Proof.Bignum.X86_64.word_writeW_self, ← VG.Proof.Bignum.X86_64.slot_succ]
  · rw [hm₆, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [e0]; exact hY
    · rw [e1]; exact hXN
  · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [e0, hYv hq, Nat.pow_zero, Nat.one_mul]
    · rw [e1, Nat.pow_one]; exact hXc hq

/-- The table: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R` and `T_i := T_(i-1) [aXc] R⁻¹`. -/
theorem tabBuild_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : VG.Proof.Bignum.X86_64.CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs (Crt.tabBuild M.mm)) t fun t' => VG.Proof.Bignum.X86_64.CExpCtx t' P wx minv X Xc ∧ VG.Proof.Bignum.X86_64.CTab t'.mem P wx X Q x ∧
      wv t'.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx = wv t.mem P (VG.Proof.Bignum.X86_64.slot wx aY) wx ∧
      (∀ k < 32, k ≠ Crt.sTab → k ≠ Crt.sEnt → k ≠ Crt.sBit → VG.Proof.Bignum.X86_64.word t'.mem P (8 * k) = VG.Proof.Bignum.X86_64.word t.mem P (8 * k)) ∧
      Frm P (VG.Proof.Bignum.X86_64.crtExpRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  rw [VG.Proof.Bignum.X86_64.tabBuild_eq]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.tabPre]) (by simp) (WP.mono (VG.Proof.Bignum.X86_64.tabPre_ok hc hw hw' hXN hXc hY hYv) fun t₆ h₀ => ?_)
  simp only [seqs, VG.Proof.Bignum.X86_64.tabLoop]
  refine WP.mono (wp_upto (a := 0) (N := 14) (by decide) (VG.Proof.Bignum.X86_64.BuildInv t P wx minv X Xc Q x)
    (fun i _ hi s hI => VG.Proof.Bignum.X86_64.buildStep_ok M hw hw' hR hXN hXc hi hI) (fun s h => h) h₀) fun t' hI => ?_
  refine ⟨hI.ctx, ⟨hI.tab, fun j hj => hI.elt j (by omega), fun hq j hj => hI.eval hq j (by omega)⟩,
    hI.frm.wv_eq (VG.Proof.Bignum.X86_64.buildRanges_y wx) (by omega),
    fun k hk h1 h2 h3 => hI.frm.word_eq (fun r hr => by
      simp only [VG.Proof.Bignum.X86_64.buildRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx 0 hk
      have := slot_le (w := wx) (show aAcc < 8 by decide)
      have := VG.Proof.Bignum.X86_64.slot_mono wx (show 0 ≤ aAcc by decide)
      have := VG.Proof.Bignum.X86_64.slot_mono wx (show aAcc ≤ aTmp by decide)
      have := VG.Proof.Bignum.X86_64.slot_mono wx (show aTmp ≤ Crt.aT by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Crt.sTab, Crt.sEnt, Crt.sBit, sFn] at * <;> omega) (by omega),
    hI.frm.mono (VG.Proof.Bignum.X86_64.buildRanges_sub wx), hI.keep⟩

/-! ## The exponentiation -/

/-- `expLoop`'s start: the exponent's pointer and length from the modulus'
header slots `sp` and `sl`, and byte index 0. -/
theorem crtExpInit_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {L : Nat}
    (hep : VG.Proof.Bignum.X86_64.word s.mem B (8 * sp) = ep) (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) s fun t =>
      t.mem = ((s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExp)) ep).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExpLen))
        (BitVec.ofNat 64 L)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sI)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hln : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi' =>
    hc.scr.ld (by have := hdr_lt_slot w 8 hi'; omega)
  have hst : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi'; omega)
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * Crt.sExp) ep (by decide)
  have hW : (s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExp)) ep).readW (VG.Proof.Bignum.X86_64.off B (8 * sl)) 64 = BitVec.ofNat 64 L :=
    ((Frm.of_outside (rs := [(8 * Crt.sExp, 8)]) o1 (by simp)).word_below (L := VG.Proof.Bignum.X86_64.slot wx 8)
      (fun r hr => by rw [List.mem_singleton.mp hr]; unfold Crt.sExp sFn VG.Proof.Bignum.X86_64.slot hdrBytes; omega) (by omega)
      (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes at hi; omega) (by have := hdr_lt_slot w 8 hsl; omega)).trans hel
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = ((s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExp)) ep).writeW
      (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sI))
      (BitVec.setWidth 64 (0 : BitVec 32)))
    (by xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, hl Crt.sLink (by decide), hc.link, hln sp hsp, hep,
      hst Crt.sExp (by decide), hln sl hsl, hW, hst Crt.sExpLen (by decide), hst Crt.sI (by decide)]) rfl)
    fun t ⟨hm, k⟩ => ⟨hm, k⟩

/-- `expLoop`'s start: the exponent's pointer and length, and byte index 0. -/
def expInit (sp sl : Nat) : Prog isa :=
  .block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)), .store (hdr Crt.sExp) .rdx,
    .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx, .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]

/-- `expLoop`'s bytes. -/
def expBytes (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (seqs [
    .block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
      .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
      .store (hdr Crt.sBit) .rax],
    .loop (seqs (Crt.expWin mul)) .ne,
    .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
      .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) .ne

theorem expLoop_eq (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) :
    Crt.expLoop mul sp sl = VG.Proof.Bignum.X86_64.expInit sp sl :: (Crt.tabBuild mul ++ [VG.Proof.Bignum.X86_64.expBytes mul]) := by
  simp [Crt.expLoop, VG.Proof.Bignum.X86_64.expInit, VG.Proof.Bignum.X86_64.expBytes]

/-- `expLoop`'s start and table: the bytes' invariant. -/
theorem crtExpHead_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) wx = X)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx < X)
    (hyc : Q → wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : VG.Proof.Bignum.X86_64.word s.mem B (8 * sp) = ep) (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (he : VG.Proof.Bignum.X86_64.Src s B Z ep eb) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.expInit sp sl :: Crt.tabBuild M.mm)) s
      (VG.Proof.Bignum.X86_64.CByteInv s (VG.Proof.Bignum.X86_64.off B o) wx minv X (wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx) Q x ep eb.length eb 0) := by
  have hPn := hc.scrT.nowrap
  have hBn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases VG.Proof.Bignum.X86_64.ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · omega
  have hc₀ : VG.Proof.Bignum.X86_64.CExpCtx s (VG.Proof.Bignum.X86_64.off B o) wx minv X (wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx) :=
    ⟨hc.good, hc.scrT, hn, hinv, rfl⟩
  rw [← List.singleton_append]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp [VG.Proof.Bignum.X86_64.tabBuild_eq, VG.Proof.Bignum.X86_64.tabPre]) ?_
  simp only [seqs, VG.Proof.Bignum.X86_64.expInit]
  refine WP.mono (VG.Proof.Bignum.X86_64.crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * Crt.sExp) ep (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExp)) ep) (VG.Proof.Bignum.X86_64.off B o) (d := 8 * Crt.sExpLen)
    (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := VG.Proof.Bignum.X86_64.writeW_outside ((s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExp)) ep).writeW
    (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (VG.Proof.Bignum.X86_64.off B o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.crtExpRanges wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.crtExpRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [VG.Proof.Bignum.X86_64.crtExpRanges]))
  have hc₁ := hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide))
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have hYe₁ : wv t₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx = wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx := by
    rw [o3.wv (by unfold Crt.sI sFn at *; omega) (by omega), o2.wv (by unfold Crt.sExpLen sFn at *; omega)
      (by omega), o1.wv (by unfold Crt.sExp sFn at *; omega) (by omega)]
  -- The table.
  refine WP.mono (VG.Proof.Bignum.X86_64.tabBuild_ok M (Q := Q) (x := x) hc₁ hw2 (by omega) hR hxl hxc (by rw [hYe₁]; exact hyl)
    (fun hq => by rw [hYe₁]; exact hyc hq)) fun t₂ ⟨hc₂, htab₂, hYe₂, hh₂, f₂, k₂⟩ => ?_
  refine ⟨hc₂, htab₂, by rw [hYe₂, hYe₁]; exact hyl, fun hq => ?_, ?_, ?_, ?_, f₁.trans f₂,
    (k₁.trans k₂).mono (by decide)⟩
  · rw [hYe₂, hYe₁, hyc hq, pre_zero, Nat.pow_zero, Nat.one_mul]
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self]

/-- The exponentiation in a prime's workspace: `Y < X` and `[aXc] < X`
stay so, and if `Q` gives `Y ≡ R` and `[aXc] ≡ x R` modulo `X`, then
`Y ≡ x^d R`, for the exponent `d` whose `L` bytes `eb` (most significant
first) are at `ep`, outside the working space, the pointer and length in
the modulus' header slots `sp` and `sl`. -/
theorem crtExpLoop_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) wx = X)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx < X)
    (hyc : Q → wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : VG.Proof.Bignum.X86_64.word s.mem B (8 * sp) = ep) (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : VG.Proof.Bignum.X86_64.Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop M.mm sp sl)) s fun t => VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx < X ∧
      (Q → wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.crtExpRanges wx) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hPn := hc.scrT.nowrap
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases VG.Proof.Bignum.X86_64.ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · omega
  rw [VG.Proof.Bignum.X86_64.expLoop_eq, ← List.cons_append]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp) (WP.mono (VG.Proof.Bignum.X86_64.crtExpHead_ok M hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel he) fun t₂ h₂ => ?_)
  simp only [seqs, VG.Proof.Bignum.X86_64.expBytes]
  refine wp_upto (a := 0) (N := eb.length) (by omega)
    (VG.Proof.Bignum.X86_64.CByteInv s (VG.Proof.Bignum.X86_64.off B o) wx minv X (wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Crt.aXc) wx) Q x ep eb.length eb)
    (fun i _ hi' t hI => VG.Proof.Bignum.X86_64.crtByte_ok M hw2 (by omega) hR rfl (by omega) hi' he.rd he.val hout hI)
    (fun t hI => ?_) h₂
  exact ⟨hc.of_frmT hI.frm (VG.Proof.Bignum.X86_64.crtExpRanges_ok wx) hI.keep.2.2 (hI.keep.gpr (by decide)), hI.ylt,
    fun hq => by rw [hI.y hq, pre_len], hI.frm, hI.keep⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtFix`. -/
section

/-!
# `vg_rsa_private_crt` on x86-64: the fixes and the products

`primeFix`, in a prime's workspace, replaces the prime by 3 where the mask is
clear and computes its `-X⁻¹` and the number 1 (`primeFix_ok`);
`pqProduct` leaves `p q` in the modulus' accumulators (`pqProduct_ok`), and
the start of `finish` `m_q + h q` (`finishSum_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## The fixes of a prime -/

/-- The low word of the fixed prime: the masked word or'ed with 3 where the
mask is clear. -/
theorem fixWord (c : Bool) (x : BitVec 64) :
    (VG.Proof.Bignum.X86_64.mask c ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) &&& (3 : BitVec 64) ||| x &&& VG.Proof.Bignum.X86_64.mask c =
      if c then x else 3 := by
  cases c
  · rw [mask_false, show x &&& (0 : BitVec 64) = 0 from BitVec.and_zero,
      show ∀ y : BitVec 64, y ||| (0 : BitVec 64) = y from fun _ => BitVec.or_zero]
    show _ = (3 : BitVec 64); decide
  · rw [mask_true, BitVec.and_allOnes, show (BitVec.allOnes 64 ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) &&&
      (3 : BitVec 64) = 0#64 by decide, BitVec.zero_or]; rfl

/-- The fix of the low word of `[rbx]`. -/
def fixLow : List Instr :=
  [.mov .rax (.reg .r15), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.imm 3),
    .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax, .mov .rbx (.reg .rax)]

/-- `-X⁻¹` into the header, and the operands of `setWord`. -/
def fixTail : List Instr := [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]

/-- The mask from the modulus' header into `sMaskX`. -/
def fixMask : List Instr :=
  [.mov .rax (.mem (hdr Crt.sLink)), .mov .rax (.mem (Crt.ws .rax sMask)), .store (hdr Crt.sMaskX) .rax]

theorem primeFix_eq : Crt.primeFix =
    ([.block VG.Proof.Bignum.X86_64.fixMask] : List (Prog isa)) ++ Crt.maskArr aN ++
      ([.block (VG.Proof.Bignum.X86_64.fixLow ++ minv ++ VG.Proof.Bignum.X86_64.fixTail), setWord aOne .rcx] : List (Prog isa)) := rfl

/-- `primeFix`'s first step: the mask from the modulus' header. -/
theorem fixMask_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hM : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (.block VG.Proof.Bignum.X86_64.fixMask) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sMaskX)) (VG.Proof.Bignum.X86_64.mask c) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hg := hc.good
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hg.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hln : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi' =>
    hc.scr.ld (by have := hdr_lt_slot w 8 hi'; omega)
  have hst : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hg.scr.st (by have := hdr_lt_slot wx 8 hi'; omega)
  refine WP.keep [.rax] (c := .block VG.Proof.Bignum.X86_64.fixMask)
    (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sMaskX)) (VG.Proof.Bignum.X86_64.mask c)) ?_ rfl
  unfold VG.Proof.Bignum.X86_64.fixMask
  xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, hl Crt.sLink (by decide), hc.link,
    hln sMask (by decide), hM, hst Crt.sMaskX (by decide)]

/-- The fix of the low word of `[rbx]` (the masked `x`), into `rbx`. -/
theorem fixLow_ok {t : State} {G : Addr} {Zx d : Nat} {c : Bool} {x : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr t G Zx)
    (hbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off G d) (h15 : t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (hd : d + 8 ≤ Zx)
    (hx : VG.Proof.Bignum.X86_64.word t.mem G d = x &&& VG.Proof.Bignum.X86_64.mask c) :
    WP isa (.block VG.Proof.Bignum.X86_64.fixLow) t fun t' =>
      (t'.gpr .rbx = if c then x else 3) ∧ t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off G d) (if c then x else 3) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbx] t t' := by
  refine WP.mono (WP.keep [.rax, .rbx] (Q := fun t' => (t'.gpr .rbx = if c then x else 3) ∧
    t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off G d) (if c then x else 3)) ?_ rfl) fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  unfold VG.Proof.Bignum.X86_64.fixLow
  xrun [State.ea, at0, hbx, h15, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld hd, hs.st hd, hx, VG.Proof.Bignum.X86_64.fixWord]

/-- In a prime's workspace (`c` the validity mask in the modulus' `sMask`):
the mask into `sMaskX`, `X := c ? X : 3`, `-X⁻¹` and the number 1. -/
theorem primeFix_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool} {X : Nat}
    (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hM : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask c) (hX : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) wx = X)
    (hodd : c = true → X % 2 = 1) :
    WP isa (seqs Crt.primeFix) s fun t => ∃ minv', VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv' ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) wx = (if c then X else 3) ∧
      ((VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN)).toNat * minv'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aOne) wx = 1 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sMaskX) = VG.Proof.Bignum.X86_64.mask c ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx aN, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx aOne, 8 * (wx + 2)), (8 * Crt.sMaskX, 8), (8 * sMinv, 8)]
        s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hGn : (VG.Proof.Bignum.X86_64.off B o).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  have sN := slot_le (w := wx) (show aN < 8 by decide)
  have sO := slot_le (w := wx) (show aOne < 8 by decide)
  have hN0 := hdr_lt_slot wx aN (show 31 < 32 by decide)
  have hO0 := hdr_lt_slot wx aOne (show 31 < 32 by decide)
  have sNO := slot_sep (w := wx) (show aN ≠ aOne by decide)
  have eMX : Crt.sMaskX = 24 := rfl
  have eMi : sMinv = 7 := rfl
  rw [VG.Proof.Bignum.X86_64.primeFix_eq]
  unfold Crt.maskArr
  simp only [List.cons_append, List.nil_append, seqs]
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.fixMask_ok hc hM) fun s₁ ⟨hm₁, k₁⟩ => ?_)
  have o₁ := VG.Proof.Bignum.X86_64.writeW_outside s.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * Crt.sMaskX) (VG.Proof.Bignum.X86_64.mask c) (by decide)
  rw [← hm₁] at o₁
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) [(8 * Crt.sMaskX, 8)] s.mem s₁.mem := Frm.of_outside o₁ (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr, eMX]; omega) k₁.2.2 (k₁.gpr (by decide))
  have hMX₁ : VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (8 * Crt.sMaskX) = VG.Proof.Bignum.X86_64.mask c := by rw [hm₁]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  have hX₁ : wv s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) wx = X := by
    rw [o₁.wv (Or.inr (by omega)) (by omega)]; exact hX
  -- `X &&&= mask`.
  have hg₁ := hc₁.good
  have hl : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hg₁.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  refine WP.seq (WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl Crt.sMaskX (by decide), hl (sArr aN) (by decide),
      hl sW (by decide), hMX₁, hg₁.hdr.harr aN (by decide), hg₁.hdr.hw]) rfl)
    fun s₂ ⟨⟨h15, h12, hbx, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hg₁.scr.congr k₂.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₂.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₂ t → t.cf = s₂.cf →
      VG.Proof.Bignum.X86_64.MaskInv s₂ (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx 8) (VG.Proof.Bignum.X86_64.slot wx aN) c 0 t := fun t h14 hm k _ =>
    ⟨hs₂.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := wx) (by omega) (by omega)
    (VG.Proof.Bignum.X86_64.MaskInv s₂ (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx 8) (VG.Proof.Bignum.X86_64.slot wx aN) c) h0
    (fun i _ hi t hI => VG.Proof.Bignum.X86_64.maskStep_ok hbx h15 h12 (by omega) (by omega) hi hI)) fun s₃ hI => ?_)
  -- The low word, `-X⁻¹` and the number 1.
  have k₃ := hI.keep
  have hbx₃ : s₃.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) := (k₃.gpr (by decide)).trans hbx
  have h15₃ : s₃.gpr .r15 = VG.Proof.Bignum.X86_64.mask c := (k₃.gpr (by decide)).trans h15
  have hx₃ : VG.Proof.Bignum.X86_64.word s₃.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) = VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) &&& VG.Proof.Bignum.X86_64.mask c := by
    have := hI.done 0 (by omega); rw [Nat.mul_zero, Nat.add_zero, hm₂] at this; exact this
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.fixLow_ok hI.scr hbx₃ h15₃ (by omega) hx₃) fun s₄ ⟨hbx₄, hm₄, k₄⟩ => ?_
  have hodd₄ : (s₄.gpr .rbx).toNat % 2 = 1 := by
    rw [hbx₄]
    cases c
    · show (3 : BitVec 64).toNat % 2 = 1; decide
    · show (VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN)).toNat % 2 = 1
      rw [← VG.Proof.Bignum.X86_64.wv_mod64 _ _ _ (show 1 ≤ wx by omega), hX₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd rfl
  refine WP.mono (minv_ok s₄ hodd₄) fun s₅ ⟨hinv, k₅, hm₅⟩ => ?_
  rw [hbx₄] at hinv
  have hs₅ : VG.Proof.Bignum.X86_64.Scr s₅ (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx 8) := (hI.scr.congr k₄.2.2).congr k₅.2.2
  have hdi₅ : s₅.gpr .rdi = VG.Proof.Bignum.X86_64.off B o :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans hg₁.rdi)))
  refine WP.mono (WP.keep [.rdx, .rcx] (c := .block VG.Proof.Bignum.X86_64.fixTail) (Q := fun t => t.gpr .rdx = 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s₅.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sMinv)) (s₅.gpr .r15)) (by
    unfold VG.Proof.Bignum.X86_64.fixTail
    xrun [State.ea, hdr, hdi₅, hdrOff, hs₅.st (d := 8 * sMinv) (by omega)]) rfl)
    fun s₆ ⟨⟨hdx₆, hcx₆, hm₆⟩, k₆⟩ => ?_
  -- What changed so far.
  have o₄ := VG.Proof.Bignum.X86_64.writeW_outside s₃.mem (VG.Proof.Bignum.X86_64.off B o) (d := VG.Proof.Bignum.X86_64.slot wx aN) (if c then VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) else 3)
    (by omega)
  rw [← hm₄] at o₄
  have o₆ := VG.Proof.Bignum.X86_64.writeW_outside s₅.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * sMinv) (s₅.gpr .r15) (by decide)
  rw [← hm₆, hm₅] at o₆
  have o₃ := hI.out
  rw [hm₂] at o₃
  have f₁₄ : Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx aN, 8 * (wx + 2))] s₁.mem s₄.mem :=
    (Frm.of_outside (o₃.mono (o' := VG.Proof.Bignum.X86_64.slot wx aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega))
      (by simp)).trans
      (Frm.of_outside (o₄.mono (o' := VG.Proof.Bignum.X86_64.slot wx aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp))
  have f₁₆ : Frm (VG.Proof.Bignum.X86_64.off B o) ([(VG.Proof.Bignum.X86_64.slot wx aN, 8 * (wx + 2))] ++ [(8 * sMinv, 8)]) s₁.mem s₆.mem :=
    f₁₄.append (Frm.of_outside o₆ (by simp))
  have hh₆ : ∀ i < 32, i ≠ sMinv → VG.Proof.Bignum.X86_64.word s₆.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) = VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) :=
    fun i hi' hne => f₁₆.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · omega
      · rw [eMi] at hne ⊢; omega) (by omega)
  have hH₆ : Hdr s₆.mem (VG.Proof.Bignum.X86_64.off B o) wx (s₅.gpr .r15) :=
    ⟨(hh₆ _ (by decide) (by decide)).trans hc₁.hdr.hw, by rw [hm₆]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _,
      fun j hj => (hh₆ _ (by unfold sArr; omega) (by unfold sArr; rw [eMi]; omega)).trans (hc₁.hdr.harr j hj)⟩
  have K₆ := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆)
  have hdi₆ : s₆.gpr .rdi = VG.Proof.Bignum.X86_64.off B o := (K₆.gpr (by decide)).trans hg₁.rdi
  have h12₆ : s₆.gpr .r12 = BitVec.ofNat 64 wx :=
    ((((k₃.trans k₄).trans k₅).trans k₆).gpr (by decide)).trans h12
  refine WP.mono (setWord_ok (hs₅.congr k₆.2.2) hdi₆ hH₆ (Nat.le_refl _) h12₆ (by omega) (by omega)
    (o := aOne) (by decide) (ri := .rcx) (by decide) (i := 0) (by omega) hcx₆) fun t ⟨hone, ho₇, k₇⟩ => ?_
  have f₇ : Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx aOne, 8 * (wx + 2))] s₆.mem t.mem := Frm.of_outside ho₇ (by simp)
  have f₄t : Frm (VG.Proof.Bignum.X86_64.off B o) ([(8 * sMinv, 8)] ++ [(VG.Proof.Bignum.X86_64.slot wx aOne, 8 * (wx + 2))]) s₄.mem t.mem :=
    (Frm.of_outside o₆ (by simp)).append f₇
  have f₁t := f₁₆.append f₇
  have F := f₁.append f₁t
  have hF : ∀ r ∈ [(8 * Crt.sMaskX, 8)] ++ ([(VG.Proof.Bignum.X86_64.slot wx aN, 8 * (wx + 2))] ++ [(8 * sMinv, 8)] ++
      [(VG.Proof.Bignum.X86_64.slot wx aOne, 8 * (wx + 2))]), 8 * 6 + 8 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega
  have hFw : ∀ i < 32, i ≠ sMinv → i ≠ Crt.sMaskX → VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * i) :=
    fun i hi' h1 h2 => F.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [eMi] at h1; rw [eMX] at h2
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega) (by omega)
  have hFb : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi' =>
    F.word_below (L := VG.Proof.Bignum.X86_64.slot wx 8) (fun r hr => (hF r hr).2) (by omega) (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes at hi; omega)
      (by have := hdr_lt_slot w 8 hi'; omega)
  have K := (k₁.trans K₆).trans k₇
  have hN₄ : ∀ {d k : Nat}, VG.Proof.Bignum.X86_64.slot wx aN ≤ d → d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot wx aN + 8 * (wx + 2) →
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) d k = wv s₄.mem (VG.Proof.Bignum.X86_64.off B o) d k := fun h1 h2 =>
    f₄t.wv_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [eMi] <;> omega) (by omega)
  have hw₀ : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) = if c then VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN) else 3 := by
    rw [f₄t.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [eMi] <;> omega) (by omega), hm₄]
    exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  have hup : ∀ i < wx, i ≠ 0 → VG.Proof.Bignum.X86_64.word s₄.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN + 8 * i) =
      VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aN + 8 * i) &&& VG.Proof.Bignum.X86_64.mask c := fun i hi' hne => by
    rw [hm₄, (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega)).word (Or.inr (by omega)) (by omega), hI.done i hi', hm₂]
  refine ⟨s₅.gpr .r15, ⟨hc.scr.congr K.2.2, (K.gpr (by decide)).trans hc.rdi,
    Arrays.hdr (Arrays.of_outside (List.mem_singleton_self _) ho₇ (Nat.le_refl _) (Nat.le_refl _)) hH₆,
    (hFw _ (by decide) (by decide) (by decide)).trans hc.link, (hFb _ (by decide)).trans hc.nw,
    fun j hj => (hFb _ (by unfold sArr; omega)).trans (hc.narr j hj), hc.lo, hc.hi⟩, ?_, ?_, ?_, ?_, ?_,
    K.mono (by decide)⟩
  · rw [hN₄ (Nat.le_refl _) (by omega)]
    cases c
    · rw [wv_single _ _ _ (i := 0) wx (by omega) fun q hq hne => by
        rw [hup q hq hne, mask_false]; exact BitVec.and_zero, Nat.mul_zero, Nat.add_zero, hm₄, VG.Proof.Bignum.X86_64.word_writeW_self]
      rfl
    · rw [← hX₁]
      refine wv_congr fun i hi' => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [Nat.mul_zero, Nat.add_zero, hm₄, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
      · rw [hup i hi' (by omega), mask_true, BitVec.and_allOnes]
  · rw [hw₀]; exact hinv
  · rw [hone, hdx₆]; rfl
  · rw [f₁t.word_eq (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [eMX, eMi] <;> omega) (by omega)]
    exact hMX₁
  · exact F.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp

/-! ## Products into the modulus' accumulators -/

theorem accs_le (w : Nat) : VG.Proof.Bignum.X86_64.slot w aAcc + 8 * (2 * w + 2) ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have := slot_le (w := w) (show aTmp < 8 by decide)
  simp only [VG.Proof.Bignum.X86_64.slot, aTmp, aAcc] at this ⊢; omega

/-- `zeroAccs`: the `2 w + 2` words from `aAcc` cleared. -/
theorem zeroAccs_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw' : w < 2 ^ 30) :
    WP isa (seqs Crt.zeroAccs) s fun t => (∀ k < 2 * w + 2, VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 8 * k) = 0) ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hA := VG.Proof.Bignum.X86_64.accs_le w
  unfold Crt.zeroAccs
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) ∧
      t.gpr .rbx = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aAcc) (by decide), hl sW (by decide),
      hg.hdr.harr aAcc (by decide), hg.hdr.hw]) rfl) fun s₁ ⟨⟨h8, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroWin_ok (hg.scr.congr k₁.2.2) h8 hbx (by omega) (by omega))
    fun t ⟨hv, ho, k⟩ => ⟨hv, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩

/-- The operands of `mulRows`: `[r11]` the array `ja` of `p`'s workspace
(`r10` its words), `[r9]` `q`'s `aN` (`r12` its words), `r8` the modulus'
accumulator. -/
def rowsHdr (ja : Nat) : List Instr :=
  [.mov .rax (.mem (hdr Crt.sWsP)), .mov .r11 (.mem (Crt.ws .rax (sArr ja))), .mov .r10 (.mem (Crt.ws .rax sW)),
    .mov .rax (.mem (hdr Crt.sWsQ)), .mov .r9 (.mem (Crt.ws .rax (sArr aN))), .mov .r12 (.mem (Crt.ws .rax sW)),
    .mov .r8 (.mem (hdr (sArr aAcc)))]

theorem rowsHdr_ok {s : State} {B : Addr} {Z w op oq wp wq ja : Nat} {A Q : Addr} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hacc : VG.Proof.Bignum.X86_64.word s.mem B (8 * sArr aAcc) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc))
    (hp : VG.Proof.Bignum.X86_64.word s.mem B (8 * Crt.sWsP) = VG.Proof.Bignum.X86_64.off B op) (hq : VG.Proof.Bignum.X86_64.word s.mem B (8 * Crt.sWsQ) = VG.Proof.Bignum.X86_64.off B oq)
    (hpw : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sW) = BitVec.ofNat 64 wp)
    (hqw : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sW) = BitVec.ofNat 64 wq)
    (hpa : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sArr ja) = A) (hqa : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sArr aN) = Q)
    (hja : ja < 8) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op) (hop : op + VG.Proof.Bignum.X86_64.slot wp 8 + VG.Proof.Bignum.X86_64.tabBytes wp ≤ oq) (hoq : oq + VG.Proof.Bignum.X86_64.slot wq 8 + VG.Proof.Bignum.X86_64.tabBytes wq ≤ Z) :
    WP isa (.block (VG.Proof.Bignum.X86_64.rowsHdr ja)) s fun t =>
      t.gpr .r11 = A ∧ t.gpr .r10 = BitVec.ofNat 64 wp ∧ t.gpr .r9 = Q ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h8p := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hlp : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B op) (8 * i)) 8 := fun i hi =>
    (hs.sub (o := op) (n := VG.Proof.Bignum.X86_64.slot wp 8) (by omega) (by omega)).ld (by omega)
  have hlq : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (8 * i)) 8 := fun i hi =>
    (hs.sub (o := oq) (n := VG.Proof.Bignum.X86_64.slot wq 8) (by omega) (by omega)).ld (by omega)
  refine WP.mono (WP.keep [.rax, .r11, .r10, .r9, .r12, .r8] (Q := fun t => t.gpr .r11 = A ∧
      t.gpr .r10 = BitVec.ofNat 64 wp ∧ t.gpr .r9 = Q ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) ∧ t.mem = s.mem)
    (by
      unfold VG.Proof.Bignum.X86_64.rowsHdr
      xrun [State.ea, hdr, Crt.ws, hdi, hdrOff, hl Crt.sWsP (by decide), hl Crt.sWsQ (by decide),
        hl (sArr aAcc) (by decide), hp, hq, hacc, hlp (sArr ja) (by unfold sArr; omega), hlp sW (by decide),
        hlq (sArr aN) (by decide), hlq sW (by decide), hpw, hqw, hpa, hqa]) rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k.mono (by decide)⟩

/-- A word above a change, at an offset workspace. -/
theorem word_above {B : Addr} {a n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside B a n m m') {o d : Nat}
    (ho : a + n ≤ o) (hd : o + d + 8 ≤ 2 ^ 64) : VG.Proof.Bignum.X86_64.word m' (VG.Proof.Bignum.X86_64.off B o) d = VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) d := by
  rw [VG.Proof.Bignum.X86_64.word_off, VG.Proof.Bignum.X86_64.word_off]; exact h.word (Or.inr (by omega)) (by omega)

theorem pqProduct_eq :
    Crt.pqProduct = Crt.zeroAccs ++ ([.block (VG.Proof.Bignum.X86_64.rowsHdr aN), Crt.mulRows] : List (Prog isa)) := rfl

/-- `p q` into the modulus' accumulators (`2 w + 2` words). -/
theorem pqProduct_ok {s : State} {B : Addr} {Z w op oq wp wq : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hw' : w < 2 ^ 29)
    (hp : VG.Proof.Bignum.X86_64.word s.mem B (8 * Crt.sWsP) = VG.Proof.Bignum.X86_64.off B op) (hq : VG.Proof.Bignum.X86_64.word s.mem B (8 * Crt.sWsQ) = VG.Proof.Bignum.X86_64.off B oq)
    (hpw : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sW) = BitVec.ofNat 64 wp)
    (hqw : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sW) = BitVec.ofNat 64 wq)
    (hpa : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sArr aN) = VG.Proof.Bignum.X86_64.off B (op + VG.Proof.Bignum.X86_64.slot wp aN))
    (hqa : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sArr aN) = VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wq aN))
    (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op) (hop : op + VG.Proof.Bignum.X86_64.slot wp 8 + VG.Proof.Bignum.X86_64.tabBytes wp ≤ oq) (hoq : oq + VG.Proof.Bignum.X86_64.slot wq 8 + VG.Proof.Bignum.X86_64.tabBytes wq ≤ Z)
    (hwp : 1 ≤ wp) (hwp' : wp ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs Crt.pqProduct) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) (2 * w + 2) = wv s.mem B (op + VG.Proof.Bignum.X86_64.slot wp aN) wp * wv s.mem B (oq + VG.Proof.Bignum.X86_64.slot wq aN) wq ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA := VG.Proof.Bignum.X86_64.accs_le w
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hpN := slot_le (w := wp) (show aN < 8 by decide)
  have hqN := slot_le (w := wq) (show aN < 8 by decide)
  have hpS := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have hqS := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  rw [VG.Proof.Bignum.X86_64.pqProduct_eq]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [Crt.zeroAccs]) (by simp)
    (WP.mono (VG.Proof.Bignum.X86_64.zeroAccs_ok hg (by omega) (by omega)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have hh : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega)) (by omega)
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.rowsHdr_ok hs₁ ((k₁.gpr (by decide)).trans hg.rdi)
    ((hh _ (by decide)).trans (hg.hdr.harr aAcc (by decide))) ((hh _ (by decide)).trans hp)
    ((hh _ (by decide)).trans hq) ((VG.Proof.Bignum.X86_64.word_above ho₁ (by omega) (by omega)).trans hpw)
    ((VG.Proof.Bignum.X86_64.word_above ho₁ (by omega) (by omega)).trans hqw) ((VG.Proof.Bignum.X86_64.word_above ho₁ (by omega) (by omega)).trans hpa)
    ((VG.Proof.Bignum.X86_64.word_above ho₁ (by omega) (by omega)).trans hqa) (by decide) hlo hop hoq)
    fun s₂ ⟨h11, h10, h9, h12, h8, hm₂, k₂⟩ => ?_)
  have hz₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) (wp + wq + 2) = 0 := by
    rw [hm₂]; exact wv_zero fun k hk => hz₁ k (by omega)
  refine WP.mono (mulRows_ok (hs₁.congr k₂.2.2) h11 h9 h10 h12 h8 hwp hwq (by omega) (by omega) (by omega)
    (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (by rw [hz₂]; exact Nat.two_pow_pos _))
    fun t ⟨hv, ho, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [show 2 * w + 2 = (wp + wq + 2) + (2 * w - wp - wq) by omega, wv_add, hv, hz₂,
      ho.wv (Or.inr (Nat.le_refl _)) (by omega), hm₂, wv_zero (n := 2 * w - wp - wq) fun k hk => by
        rw [Nat.add_assoc, ← Nat.mul_add]; exact hz₁ _ (by omega), Nat.mul_zero, Nat.add_zero, Nat.zero_add,
      ho₁.wv (Or.inr (by omega)) (by omega), ho₁.wv (Or.inr (by omega)) (by omega)]
  · rw [hm₂] at ho
    exact ho₁.trans (ho.mono (Nat.le_refl _) (by omega))

/-- `finish`'s copy of `m_q` (`q`'s `aY`) into the modulus' accumulator. -/
def finishCopy : List Instr :=
  [.mov .rax (.mem (hdr Crt.sWsQ)), .mov .rsi (.mem (Crt.ws .rax (sArr aY))), .mov .r12 (.mem (Crt.ws .rax sW)),
    .mov .rbx (.mem (hdr (sArr aAcc)))]

/-- The first steps of `finish`: `m_q + h q` into the modulus' accumulator. -/
def finishSum : List (Prog isa) :=
  Crt.zeroAccs ++ ([.block VG.Proof.Bignum.X86_64.finishCopy, copyWords, .block (VG.Proof.Bignum.X86_64.rowsHdr aY), Crt.mulRows] : List (Prog isa))

theorem finish_eq : Crt.finish = VG.Proof.Bignum.X86_64.finishSum ++ Crt.finish.drop 6 := rfl

/-- `m_q + h q` (`m_q` in `q`'s `aY`, `h` in `p`'s) into the modulus'
accumulators (`2 w + 2` words). -/
theorem finishSum_ok {s : State} {B : Addr} {Z w op oq wp wq : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hw' : w < 2 ^ 29)
    (hp : VG.Proof.Bignum.X86_64.word s.mem B (8 * Crt.sWsP) = VG.Proof.Bignum.X86_64.off B op) (hq : VG.Proof.Bignum.X86_64.word s.mem B (8 * Crt.sWsQ) = VG.Proof.Bignum.X86_64.off B oq)
    (hpw : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sW) = BitVec.ofNat 64 wp)
    (hqw : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sW) = BitVec.ofNat 64 wq)
    (hpy : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sArr aY) = VG.Proof.Bignum.X86_64.off B (op + VG.Proof.Bignum.X86_64.slot wp aY))
    (hqy : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sArr aY) = VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wq aY))
    (hqa : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sArr aN) = VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wq aN))
    (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op) (hop : op + VG.Proof.Bignum.X86_64.slot wp 8 + VG.Proof.Bignum.X86_64.tabBytes wp ≤ oq) (hoq : oq + VG.Proof.Bignum.X86_64.slot wq 8 + VG.Proof.Bignum.X86_64.tabBytes wq ≤ Z)
    (hwp : 1 ≤ wp) (hwp' : wp ≤ w) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) :
    WP isa (seqs VG.Proof.Bignum.X86_64.finishSum) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) (2 * w + 2) = wv s.mem B (oq + VG.Proof.Bignum.X86_64.slot wq aY) wq +
        wv s.mem B (op + VG.Proof.Bignum.X86_64.slot wp aY) wp * wv s.mem B (oq + VG.Proof.Bignum.X86_64.slot wq aN) wq ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aAcc) (8 * (2 * w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hA := VG.Proof.Bignum.X86_64.accs_le w
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hpY := slot_le (w := wp) (show aY < 8 by decide)
  have hqY := slot_le (w := wq) (show aY < 8 by decide)
  have hqN := slot_le (w := wq) (show aN < 8 by decide)
  have hpS := hdr_lt_slot wp 8 (show 31 < 32 by decide)
  have hqS := hdr_lt_slot wq 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  have eY : sArr aY = 14 := rfl
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [Crt.zeroAccs]) (by simp)
    (WP.mono (VG.Proof.Bignum.X86_64.zeroAccs_ok hg (by omega) (by omega)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have hh : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega)) (by omega)
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hl : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs₁.ld (by omega)
  have hlq : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (8 * i)) 8 := fun i hi =>
    (hs₁.sub (o := oq) (n := VG.Proof.Bignum.X86_64.slot wq 8) (by omega) (by omega)).ld (by omega)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wq aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) ∧ t.mem = s₁.mem)
    (by
      unfold VG.Proof.Bignum.X86_64.finishCopy
      xrun [State.ea, hdr, Crt.ws, hdi₁, hdrOff, hl Crt.sWsQ (by decide), hl (sArr aAcc) (by decide),
        (hh _ (by decide)).trans hq, (hh _ (by decide)).trans (hg.hdr.harr aAcc (by decide)),
        hlq (sArr aY) (by decide), hlq sW (by decide), (VG.Proof.Bignum.X86_64.word_above ho₁ (by omega) (by omega)).trans hqy,
        (VG.Proof.Bignum.X86_64.word_above ho₁ (by omega) (by omega)).trans hqw]) rfl)
    fun s₂ ⟨⟨hsi, h12, hbx, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  refine WP.seq (WP.mono (copyWords_ok hsi hbx h12 hwq (by omega) (by omega)
    (fun j hj => hs₂.ld (by omega)) (fun j hj => hs₂.st (by omega))
    (fun j hj b hb => by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega)) fun s₃ ⟨hc₃, _, ho₃, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  rw [hm₂] at hc₃ ho₃
  have hh₃ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₃.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi =>
    (ho₃.word (Or.inl (by have := hdr_lt_slot w aAcc hi; omega)) (by omega)).trans (hh i hi)
  have hab : ∀ {o d : Nat}, VG.Proof.Bignum.X86_64.slot w 8 ≤ o → o + d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₃.mem (VG.Proof.Bignum.X86_64.off B o) d = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) d :=
    fun ho hd => (VG.Proof.Bignum.X86_64.word_above ho₃ (by omega) hd).trans (VG.Proof.Bignum.X86_64.word_above ho₁ (by omega) hd)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.rowsHdr_ok hs₃ ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))
    ((hh₃ _ (by decide)).trans (hg.hdr.harr aAcc (by decide))) ((hh₃ _ (by decide)).trans hp)
    ((hh₃ _ (by decide)).trans hq) ((hab (by omega) (by omega)).trans hpw)
    ((hab (by omega) (by omega)).trans hqw) ((hab (by omega) (by omega)).trans hpy)
    ((hab (by omega) (by omega)).trans hqa) (by decide) hlo hop hoq)
    fun s₄ ⟨h11, h10, h9, h12', h8', hm₄, k₄⟩ => ?_)
  have hmid : ∀ k < 2 * w + 2 - wq, VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 8 * wq + 8 * k) = 0 := fun k hk => by
    rw [ho₃.word (Or.inr (by omega)) (by omega), Nat.add_assoc, ← Nat.mul_add]; exact hz₁ _ (by omega)
  have hwvab : ∀ {d k : Nat}, VG.Proof.Bignum.X86_64.slot w 8 ≤ d → d + 8 * k ≤ Z → wv s₃.mem B d k = wv s.mem B d k :=
    fun hd hk => (ho₃.wv (Or.inr (by omega)) (by omega)).trans (ho₁.wv (Or.inr (by omega)) (by omega))
  have hz₄ : wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) (wp + wq + 2) = wv s.mem B (oq + VG.Proof.Bignum.X86_64.slot wq aY) wq := by
    rw [hm₄, show wp + wq + 2 = wq + (wp + 2) by omega, wv_add, wv_zero (n := wp + 2) fun k hk => hmid k (by omega),
      Nat.mul_zero, Nat.add_zero, hc₃, ho₁.wv (Or.inr (by omega)) (by omega)]
  have h0 : wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) (wp + wq + 2) < 2 ^ (64 * (wq + 1)) := by
    rw [hz₄]
    exact Nat.lt_of_lt_of_le (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.mono (mulRows_ok (hs₃.congr k₄.2.2) h11 h9 h10 h12' h8' hwp hwq (by omega) (by omega) (by omega)
    (by omega) (Or.inr (by omega)) (Or.inr (by omega)) h0)
    fun t ⟨hv, ho, k₅⟩ => ⟨?_, ?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [show 2 * w + 2 = (wp + wq + 2) + (2 * w - wp - wq) by omega, wv_add, hv, hz₄,
      ho.wv (Or.inr (Nat.le_refl _)) (by omega), hm₄, wv_zero (n := 2 * w - wp - wq) fun k hk => by
        rw [show VG.Proof.Bignum.X86_64.slot w aAcc + 8 * (wp + wq + 2) + 8 * k = VG.Proof.Bignum.X86_64.slot w aAcc + 8 * wq + 8 * (wp + 2 + k) by omega]
        exact hmid _ (by omega), Nat.mul_zero, Nat.add_zero,
      hwvab (by omega) (by omega), hwvab (by omega) (by omega)]
  · rw [hm₄] at ho
    exact (ho₁.trans (ho₃.mono (Nat.le_refl _) (by omega))).trans (ho.mono (Nat.le_refl _) (by omega))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow`. -/
section

/-!
# `vg_rsa_private_crt` on x86-64: `G = 2^E mod n`

`gPow`: `K = ⌈w / w_X⌉` (`kLoop_ok`), `D = 64 ((K + 1) w_X - w)` into
slot `sD` (`gHead_ok`), its top bit into `sCnt`, `Y := R mod n`, then a
squaring and a doubling under each bit of `D` from the top (`gBit_ok`,
`gBits_ok`): `Y ≡ 2^D R = 2^(64 w_X (K + 1))` (`gPow_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64 (Crt.ws Crt.sD Crt.gPow)

/-- `K = ⌈w / w_X⌉`: `w ≤ K w_X < w + w_X`. -/
theorem kBounds {w wx : Nat} (hwx : 1 ≤ wx) :
    w ≤ (w + wx - 1) / wx * wx ∧ (w + wx - 1) / wx * wx < w + wx := by
  have h1 := Nat.div_add_mod (w + wx - 1) wx
  have h2 := Nat.mod_lt (w + wx - 1) (show 0 < wx by omega)
  rw [Nat.mul_comm] at h1
  omega

/-- The loop `rcx += w_X` while `rcx < w`, from `rcx = 0`: `rcx = K w_X`. -/
theorem kLoop_ok {s : State} {w wx : Nat} (hwx : 1 ≤ wx) (hw : 1 ≤ w) (hw' : w + wx < 2 ^ 32)
    (hax : s.gpr .rax = BitVec.ofNat 64 wx) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 0) :
    WP isa (.loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b) s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 ((w + wx - 1) / wx * wx) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rcx] s t := by
  generalize hK : (w + wx - 1) / wx = K
  obtain ⟨hK1, hK2⟩ := VG.Proof.Bignum.X86_64.kBounds (w := w) hwx
  rw [hK] at hK1 hK2
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, Nat.zero_mul] at hK1; omega
    · exact h
  refine WP.loop (M := isa) (fun n t => ∃ k, n = K - k ∧ k < K ∧ t.gpr .rcx = BitVec.ofNat 64 (k * wx) ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rcx] s t) ?_ _ s ⟨0, rfl, hK0, by rw [hcx, Nat.zero_mul], rfl, Keep.refl _ _⟩
  rintro n t ⟨k, rfl, hk, hcx', hm, k₀⟩
  have hle : (k + 1) * wx ≤ K * wx := Nat.mul_le_mul_right _ hk
  have hle' : k * wx + wx ≤ K * wx := by rw [← Nat.succ_mul]; exact hle
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 ((k + 1) * wx) ∧
      t'.cf = some (decide ((k + 1) * wx < w)) ∧ t'.mem = t.mem) (by
    xrun [hcx', (k₀.gpr (by decide)).trans hax, (k₀.gpr (by decide)).trans h12, ← BitVec.ofNat_add]
    rw [Nat.succ_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, rfl⟩) rfl) fun t' ⟨⟨hcx'', hcf, hm'⟩, k'⟩ => ?_
  by_cases hc : (k + 1) * wx < w
  · refine .inr ⟨by simp [VG.X86_64.eval, hcf, hc], K - (k + 1), by omega, k + 1, rfl, ?_, hcx'', hm'.trans hm,
      (k₀.trans k').mono (by decide)⟩
    rcases Nat.lt_or_ge (k + 1) K with h | h
    · exact h
    · have := Nat.mul_le_mul_right wx h; omega
  · have hkK : k + 1 = K := by
      rcases Nat.lt_or_ge (k + 1) K with h | h
      · have := Nat.mul_le_mul_right wx (show k + 2 ≤ K by omega)
        rw [Nat.succ_mul (k + 1)] at this; omega
      · omega
    exact .inl ⟨by simp [VG.X86_64.eval, hcf, hc], by rw [hcx'', hkK], hm'.trans hm, (k₀.trans k').mono (by decide)⟩

/-- `D = 64 ((K + 1) w_X - w)`. -/
def gD (w wx : Nat) : Nat := 64 * ((w + wx - 1) / wx * wx + wx - w)

/-- `gPow`'s first steps: `D` into slot `sD` and `rax`. -/
def gHead (slotWs : Nat) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr slotWs)), .mov .rax (.mem (Crt.ws .rax sW)), .mov .r12 (.mem (hdr sW)),
    .mov32 .rcx (.imm 0)],
  .loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b,
  .block [.alu .add .rcx (.reg .rax), .alu .sub .rcx (.reg .r12), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .store (hdr Crt.sD) .rcx, .mov .rax (.reg .rcx)]]

/-- The steps of `D`. -/
theorem gHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30) {sl : Nat} (hsl' : sl < 32) {Bx : Addr} {wx : Nat}
    (hX : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = Bx) (hXw : VG.Proof.Bignum.X86_64.word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.gHead sl)) s fun t => t.gpr .rax = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.gD w wx) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Crt.sD)) (BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.gD w wx)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .r12] s t := by
  have hs := hg.scr
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .r12, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 wx ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, Crt.ws, hg.rdi, hdrOff, hl sl hsl', hX, hXr, hXw, hl sW (by decide), hg.hdr.hw]) rfl)
    fun t₁ ⟨⟨hax₁, h12₁, hcx₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.kLoop_ok hwx (by omega) (by omega) hax₁ h12₁ hcx₁) fun t₂ ⟨hcx₂, hm₂, k₂⟩ => ?_)
  obtain ⟨hK1, hK2⟩ := VG.Proof.Bignum.X86_64.kBounds (w := w) hwx
  have hD : VG.Proof.Bignum.X86_64.gD w wx = 64 * ((w + wx - 1) / wx * wx + wx - w) := rfl
  generalize (w + wx - 1) / wx * wx = a at hcx₂ hK1 hK2 hD
  have hsub : BitVec.ofNat 64 (a + wx) - BitVec.ofNat 64 w = BitVec.ofNat 64 (a + wx - w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hdi₂ : t₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans hg.rdi
  have hs₂ := hs.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.gD w wx) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Crt.sD)) (BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.gD w wx))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (show 8 * Crt.sD + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega), hcx₂, (k₂.gpr (by decide)).trans hax₁,
      (k₂.gpr (by decide)).trans h12₁, hm₂, hm₁, ← BitVec.ofNat_add, hsub]
    rw [hD]
    generalize a + wx - w = c
    refine ⟨congrArg (BitVec.ofNat 64) ?_,
      congrArg (fun v => s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Crt.sD)) v) (congrArg (BitVec.ofNat 64) ?_)⟩ <;> omega) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, ((k₁.trans k₂).trans k).mono (by decide)⟩

/-! ## The bits of `D` -/

theorem and_pow_beq (D k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 D &&& BitVec.ofNat 64 (2 ^ k) == 0) = decide (D / 2 ^ k % 2 = 0) := by
  have e : BitVec.ofNat 64 (2 ^ k) = BitVec.twoPow 64 k := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_twoPow]
  rw [e, BitVec.and_twoPow, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : D / 2 ^ k % 2 = 0
  · simp [h]
  · have h1 : D / 2 ^ k % 2 = 1 := by omega
    have h2 : BitVec.twoPow 64 k ≠ 0#64 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_twoPow_of_lt hk] at this
      exact absurd this (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k))
    simp [h1, hk, h2]

theorem div_bit (D k : Nat) : 2 * (D / 2 ^ (k + 1)) + D / 2 ^ k % 2 = D / 2 ^ k := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- The loop's body: `Y := Y² R⁻¹`, doubled if the bit is set, and the
next bit. -/
def gBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  mul aY aY aY,
  .block [.mov .rax (.mem (hdr Crt.sD)), .alu .and .rax (.mem (hdr sCnt))],
  .ite .ne (double aN aAcc aTmp aY) (.block []),
  .block [.mov .rax (.mem (hdr sCnt)), .shift .shr .rax 1, .store (hdr sCnt) .rax, .alu .test .rax (.reg .rax)]]

theorem gPow_eq (mul : Nat → Nat → Nat → Prog isa) (slotWs : Nat) : Crt.gPow mul slotWs =
    VG.Proof.Bignum.X86_64.gHead slotWs ++ [topBit, .block [.store (hdr sCnt) .rdx], mul aY aR2 aOne, .loop (seqs (VG.Proof.Bignum.X86_64.gBody mul)) .ne] :=
  rfl

/-- What `gPow` changes. -/
def gRanges (w : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot w aAcc, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aTmp, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aY, 8 * (w + 2)), (8 * Crt.sD, 8),
    (8 * sCnt, 8)]

/-- After the top `j` of the `L + 1` bits of `D`, from `s₀`: `Y ≡ 2^⌊D / 2^(L + 1 - j)⌋ R`. -/
structure GInv (s₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N D L : Nat) (j : Nat) (t : State) :
    Prop where
  good : Good t B Z w minv
  n : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N
  inv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  ylt : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N
  y : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = 2 ^ (D / 2 ^ (L + 1 - j)) * 2 ^ (64 * w) % N
  d : VG.Proof.Bignum.X86_64.word t.mem B (8 * Crt.sD) = BitVec.ofNat 64 D
  c : VG.Proof.Bignum.X86_64.word t.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L + 1 - j) / 2)
  frm : Frm B (VG.Proof.Bignum.X86_64.gRanges w) s₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s₀ t

/-- Bit `L - j` of `D`. -/
theorem gBit_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) {j : Nat} (hj : j < L + 1) (hI : VG.Proof.Bignum.X86_64.GInv s₀ B Z w minv N D L j t) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.gBody M.mm)) t fun t' =>
      t'.zf = some (decide (j + 1 = L + 1)) ∧ VG.Proof.Bignum.X86_64.GInv s₀ B Z w minv N D L (j + 1) t' := by
  have hn := hI.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hc2 : 2 ^ (L + 1 - j) / 2 = 2 ^ (L - j) := by
    rw [show L + 1 - j = (L - j) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
  have hpL : 2 ^ (L - j) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  -- `Y := Y²`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mmN_ok M (o := aY) (a := aY) (b := aY) hI.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.n hI.inv hI.ylt)
    fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  have hY₁ : wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = 2 ^ (2 * (D / 2 ^ (L + 1 - j))) * 2 ^ (64 * w) % N :=
    VG.Proof.Bignum.mont_sq hR hI.y hm₁
  have hd₁ : VG.Proof.Bignum.X86_64.word t₁.mem B (8 * Crt.sD) = BitVec.ofNat 64 D := by rw [ha₁.hslot (by decide)]; exact hI.d
  have hc₁ : VG.Proof.Bignum.X86_64.word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₁.hslot (by decide), hI.c, hc2]
  have hl₁ : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg₁.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- The bit, into ZF.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t₂ => t₂.zf = some (decide (D / 2 ^ (L - j) % 2 = 0)) ∧
      t₂.mem = t₁.mem) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl₁ Crt.sD (by decide), hl₁ sCnt (by decide), hd₁, hc₁,
      VG.Proof.Bignum.X86_64.and_pow_beq D (L - j) (by omega)]) rfl) fun t₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
  have hg₂ : Good t₂ B Z w minv := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, hm₂ ▸ hg₁.hdr⟩
  -- Doubled if it is set.
  have hdbl : WP isa (.ite .ne (double aN aAcc aTmp aY) (.block [])) t₂ fun t₃ => Good t₃ B Z w minv ∧
      wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N ∧
      wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N =
        2 ^ (2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aY] t₂.mem t₃.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t₂ t₃ := by
    by_cases hbit : D / 2 ^ (L - j) % 2 = 0
    · refine WP.ite false (by simp [VG.X86_64.eval, hz₂, hbit]) (by simp) (fun _ => WP.block_nil ⟨hg₂, ?_, ?_,
        fun _ _ => rfl, Keep.refl _ _⟩)
      · rw [hm₂]; exact hlt₁
      · rw [hm₂, hY₁, hbit]; rfl
    · refine WP.ite true (by simp [VG.X86_64.eval, hz₂, hbit]) (fun _ => ?_) (by simp)
      refine WP.mono (double_ok hg₂.scr hg₂.rdi hg₂.hdr hZ hw hw' (mo := aN) (acc := aAcc) (tmp := aTmp)
        (o := aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [hm₂, hn₁]; exact hlt₁)) fun t₃ ⟨hv₃, ha₃, k₃⟩ => ?_
      rw [hm₂, hn₁] at hv₃
      refine ⟨⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, ha₃.hdr hg₂.hdr⟩,
        by rw [hv₃]; exact Nat.mod_lt _ hN0, ?_, ha₃, k₃⟩
      rw [hv₃, Nat.mod_mod, Nat.mul_mod 2 (wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aY) w) N, hY₁, ← Nat.mul_mod,
        show D / 2 ^ (L - j) % 2 = 1 by omega, Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc]
  refine WP.seq (WP.mono hdbl fun t₃ ⟨hg₃, hlt₃, hY₃, ha₃, k₃⟩ => ?_)
  -- The next bit.
  have hc₃ : VG.Proof.Bignum.X86_64.word t₃.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₃.hslot (by decide), hm₂]; exact hc₁
  have hl₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg₃.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₃ : ∀ i < 32, InRegions t₃.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg₃.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₃.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ (L - j) / 2)) ∧ t'.zf = some (decide (2 ^ (L - j) / 2 = 0))) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hl₃ sCnt (by decide), hs₃ sCnt (by decide), hc₃, shr1_ofNat _ hpL,
      BitVec.and_self, ofNat64_beq_zero (show 2 ^ (L - j) / 2 < 2 ^ 64 by omega)]) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ?_
  have o' : VG.Proof.Bignum.X86_64.Outside B (8 * sCnt) 8 t₃.mem t'.mem := by
    rw [hm']; exact VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by unfold sCnt sFn; omega)
  have hkeep : ∀ i < 8, i ≠ aAcc → i ≠ aTmp → i ≠ aY → wv t'.mem B (VG.Proof.Bignum.X86_64.slot w i) w = wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w i) w :=
    fun i hi h1 h2 h3 => by
      rw [hm', hdrStore_wv _ _ _ (by decide) hi hn', ha₃.wv_of_not_mem hi (by simp [h1, h2, h3]) hn', hm₂]
  have hY' : wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w := by
    rw [hm', hdrStore_wv _ _ _ (by decide) (by decide) hn']
  have hle : L + 1 - (j + 1) = L - j := by omega
  refine ⟨?_, ⟨⟨hg₃.scr.congr k'.2.2, (k'.gpr (by decide)).trans hg₃.rdi, by
      rw [hm']; exact Hdr.store hg₃.hdr (by decide) (by decide) _⟩,
    by rw [hkeep aN (by decide) (by decide) (by decide) (by decide)]; exact hn₁,
    by rw [hm', hdrStore_word _ _ _ (by decide) (by decide) hn',
      ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega), hm₂]; exact hinv₁,
    by rw [hY']; exact hlt₃,
    by rw [hY', hY₃, hle, show 2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2 = D / 2 ^ (L - j) by
      rw [show L + 1 - j = L - j + 1 by omega]; exact VG.Proof.Bignum.X86_64.div_bit D (L - j)],
    by rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₃.hslot (by decide), hm₂]; exact hd₁,
    by rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self, hle],
    ?_, (((hI.keep.trans k₁).trans k₂).trans (k₃.trans k')).mono (by decide)⟩⟩
  · rw [hz']; congr 1; refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · rcases Nat.eq_zero_or_pos (L - j) with h0 | h0
      · omega
      · rw [show L - j = (L - j - 1) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)] at h
        exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · rw [show L - j = 0 by omega]; rfl
  · exact (((hI.frm.trans (Frm.of_arrays ha₁ (by simp [VG.Proof.Bignum.X86_64.gRanges]))).trans
      (by rw [hm₂]; exact Frm.refl _ _ _)).trans (Frm.of_arrays ha₃ (by simp [VG.Proof.Bignum.X86_64.gRanges]))).trans
      (Frm.of_outside o' (by simp [VG.Proof.Bignum.X86_64.gRanges]))

/-- The `L + 1` bits of `D`: `Y ≡ 2^D R`. -/
theorem gBits_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) (h0 : VG.Proof.Bignum.X86_64.GInv s₀ B Z w minv N D L 0 t) :
    WP isa (.loop (seqs (VG.Proof.Bignum.X86_64.gBody M.mm)) .ne) t (VG.Proof.Bignum.X86_64.GInv s₀ B Z w minv N D L (L + 1)) :=
  wp_upto (a := 0) (N := L + 1) (by omega) (VG.Proof.Bignum.X86_64.GInv s₀ B Z w minv N D L)
    (fun _ _ hj _ hI => VG.Proof.Bignum.X86_64.gBit_ok M hZ hw hw' hR hN0 hL hj hI) (fun _ h => h) h0

/-! ## `G` -/

theorem gD_bounds {w wx : Nat} (hwx : 1 ≤ wx) (hwx' : wx ≤ w) (hw30 : w < 2 ^ 30) :
    0 < VG.Proof.Bignum.X86_64.gD w wx ∧ VG.Proof.Bignum.X86_64.gD w wx < 2 ^ 62 ∧
      VG.Proof.Bignum.X86_64.gD w wx + 64 * w = 64 * wx * ((w + wx - 1) / wx + 1) := by
  obtain ⟨hK1, hK2⟩ := VG.Proof.Bignum.X86_64.kBounds (w := w) hwx
  unfold VG.Proof.Bignum.X86_64.gD
  rw [Nat.mul_succ, Nat.mul_assoc 64 wx, Nat.mul_comm wx]
  omega

/-- `gPow`: `[aY] ≡ 2^(64 w_X (K + 1)) (mod N)` for `K = ⌈w / w_X⌉`, with `w_X` in
the header of the workspace whose base is in slot `sl`. -/
theorem gPow_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hr2' : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N)
    (hone : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aOne) w = 1)
    {sl : Nat} (hsl' : sl < 32)
    {Bx : Addr} {wx : Nat} (hX : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = Bx)
    (hXw : VG.Proof.Bignum.X86_64.word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (Crt.gPow M.mm sl)) s fun t => Good t B Z w minv ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = 2 ^ (64 * wx * ((w + wx - 1) / wx + 1)) % N ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w aAcc, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aTmp, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aY, 8 * (w + 2)),
        (8 * Crt.sD, 8), (8 * sCnt, 8)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega
  obtain ⟨hD0, hD1, hDE⟩ := VG.Proof.Bignum.X86_64.gD_bounds hwx hwx' hw30
  rw [VG.Proof.Bignum.X86_64.gPow_eq]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.gHead]) (by simp) (WP.mono (VG.Proof.Bignum.X86_64.gHead_ok hg hZ hw hw30 hsl' hX hXw hXr hwx hwx')
    fun t₁ ⟨hax₁, hm₁, k₁⟩ => ?_)
  generalize VG.Proof.Bignum.X86_64.gD w wx = D at hD0 hD1 hDE hax₁ hm₁
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  -- The top bit `L` of `D`.
  refine WP.seq (WP.mono (topBit_ok hax₁ hD0 (by omega)) fun t₂ ⟨hdx₂, _, hm₂, k₂⟩ => ?_)
  have hL : D.log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.seq (WP.mono (WP.keep [] (Q := fun t => t.mem = t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (show 8 * sCnt + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sCnt < 32 by decide); omega), hdx₂]) rfl) fun t₃ ⟨hm₃, k₃⟩ => ?_)
  have hm₃' : t₃.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Crt.sD)) (BitVec.ofNat 64 D)).writeW (VG.Proof.Bignum.X86_64.off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2)) := by rw [hm₃, hm₂, hm₁]
  have hwv₃ : ∀ j < 8, wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w j) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w := fun j hj => by
    rw [hm₃', hdrStore_wv _ _ _ (by decide) hj hn', hdrStore_wv _ _ _ (by decide) hj hn']
  have hg₃ : Good t₃ B Z w minv := ⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, by
    rw [hm₃']; exact Hdr.store (Hdr.store hg.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  -- `Y := R`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mmN_ok M (N := N) (o := aY) (a := aR2) (b := aOne) hg₃ hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₃ aN (by decide)).trans hn)
    (by rw [hm₃', hdrStore_word _ _ _ (by decide) (by decide) hn', hdrStore_word _ _ _ (by decide) (by decide) hn'];
        exact hinv)
    (by rw [hwv₃ aOne (by decide), hone]; exact hN1))
    fun t₄ ⟨hg₄, hn₄, hinv₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hwv₃ aR2 (by decide), hwv₃ aOne (by decide), hone, Nat.mul_one] at hm₄
  have hY₄ : wv t₄.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = 2 ^ (D / 2 ^ (D.log2 + 1 - 0)) * 2 ^ (64 * w) % N := by
    rw [Nat.sub_zero, Nat.div_eq_of_lt Nat.lt_log2_self, Nat.pow_zero, Nat.one_mul]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hr2']
  have hfr₄ : Frm B (VG.Proof.Bignum.X86_64.gRanges w) s.mem t₄.mem := by
    have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem B (BitVec.ofNat 64 D) (d := 8 * Crt.sD) (by unfold Crt.sD sFn; omega)
    have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Crt.sD)) (BitVec.ofNat 64 D)) B
      (BitVec.ofNat 64 (2 ^ D.log2)) (d := 8 * sCnt) (by unfold sCnt sFn; omega)
    rw [← hm₃'] at o2
    exact ((Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.gRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.gRanges]))).trans
      (Frm.of_arrays ha₄ (by simp [VG.Proof.Bignum.X86_64.gRanges]))
  have h0 : VG.Proof.Bignum.X86_64.GInv s B Z w minv N D D.log2 0 t₄ := ⟨hg₄, hn₄, hinv₄, hlt₄, hY₄,
    by rw [ha₄.hslot (by decide), hm₃', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self],
    by rw [ha₄.hslot (by decide), hm₃', VG.Proof.Bignum.X86_64.word_writeW_self, Nat.sub_zero, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)],
    hfr₄, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  -- The bits.
  refine WP.mono (VG.Proof.Bignum.X86_64.gBits_ok M hZ hw hw' hR hN0 (by omega) h0) fun t hI => ⟨hI.good, hI.ylt, ?_, hI.frm, hI.keep⟩
  rw [hI.y, Nat.sub_self, Nat.pow_zero, Nat.div_one, ← Nat.pow_add, hDE]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc`. -/
section

/-!
# RSA with the CRT on x86-64: `x R_X^(-K) mod X`

`redc j`, in a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`):
the number `x` of the modulus' array `j` (`w` words) in chunks of `w_X`
words, `x = Σ x_k R^k`, is reduced as `A := (A R⁻¹ + x_k R⁻¹) mod X` for
each chunk from the lowest: `A R^K ≡ x (mod X)` for `K = ⌈w / w_X⌉`
(`redc_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What `redc` changes in the prime's workspace. -/
def redcRanges (wx : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot wx Public.aAcc, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx Public.aTmp, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx aXc, 8 * (wx + 2)),
    (VG.Proof.Bignum.X86_64.slot wx aChunk, 8 * (wx + 2)), (VG.Proof.Bignum.X86_64.slot wx aT, 8 * (wx + 2)), (8 * sSrc, 8), (8 * sRem, 8)]

theorem redcRanges_ok (wx : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.redcRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by
  have := hdr_lt_slot wx 0 (show 31 < 32 by decide)
  have := slot_le (w := wx) (show 0 < 8 by decide)
  have := slot_le (w := wx) (show Public.aAcc < 8 by decide)
  have := slot_le (w := wx) (show Public.aTmp < 8 by decide)
  have := slot_le (w := wx) (show aXc < 8 by decide)
  have := slot_le (w := wx) (show aChunk < 8 by decide)
  have := slot_le (w := wx) (show aT < 8 by decide)
  have h1 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx Public.aAcc := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have h2 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx Public.aTmp := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have h3 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx aXc := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have h4 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx aChunk := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have h5 : VG.Proof.Bignum.X86_64.slot wx 0 ≤ VG.Proof.Bignum.X86_64.slot wx aT := by unfold VG.Proof.Bignum.X86_64.slot; omega
  simp only [VG.Proof.Bignum.X86_64.redcRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sSrc, sRem, sFn] at * <;> omega

theorem redcRanges_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp)
    (h3 : j ≠ aXc) (h4 : j ≠ aChunk) (h5 : j ≠ aT) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.redcRanges wx, VG.Proof.Bignum.X86_64.slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx j := by
  have := hdr_lt_slot wx j (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) h1
  have s2 := slot_sep (w := wx) h2
  have s3 := slot_sep (w := wx) h3
  have s4 := slot_sep (w := wx) h4
  have s5 := slot_sep (w := wx) h5
  have := hj
  simp only [VG.Proof.Bignum.X86_64.redcRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sSrc, sRem, sFn] at * <;> omega

/-- The prime `X` and the number 1 in its workspace, and `-X⁻¹`. -/
structure XVals (t : State) (B : Addr) (o wx : Nat) (minv : BitVec 64) (X : Nat) : Prop where
  n : wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aN) wx = X
  inv : ((VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  one : wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aOne) wx = 1

theorem XVals.of_frm {s t : State} {B : Addr} {o wx : Nat} {minv : BitVec 64} {X : Nat}
    (h : VG.Proof.Bignum.X86_64.XVals s B o wx minv X) (hn : (VG.Proof.Bignum.X86_64.off B o).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64) (hw : 1 ≤ wx)
    (hf : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) s.mem t.mem) : VG.Proof.Bignum.X86_64.XVals t B o wx minv X := by
  have rN := VG.Proof.Bignum.X86_64.redcRanges_arr wx (j := Public.aN) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have rO := VG.Proof.Bignum.X86_64.redcRanges_arr wx (j := Public.aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have lN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have lO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  exact ⟨by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact h.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact h.inv,
    by rw [hf.wv_eq (fun r hr => by have := rO r hr; omega) (by omega)]; exact h.one⟩

theorem wv_split (m : Mem) (p : Addr) (d : Nat) {n k L : Nat} (h : n + k = L) :
    wv m p d L = wv m p d n + 2 ^ (64 * n) * wv m p (d + 8 * n) k := by
  subst h; exact wv_add m p d n k

/-- The words of `x` read after `k` chunks. -/
def lowW (w wx k : Nat) : Nat := min w (k * wx)

theorem ofNat_add_off (B : Addr) (a d : Nat) : BitVec.ofNat 64 a + VG.Proof.Bignum.X86_64.off B d = VG.Proof.Bignum.X86_64.off B (d + a) := by
  rw [BitVec.add_comm]; simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    exact h this

/-- `redc`'s start: `A := 0`, the source at array `j` of the modulus' and
all `w` words left. -/
theorem redcHead_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) {j : Nat} (hj : j < 8) :
    WP isa (.seq (zeroArr aXc) (.block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax (sArr j))),
        .store (hdr sSrc) .rdx, .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sW)), .store (hdr sRem) .rdx])) s fun t =>
      VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv ∧ wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = 0 ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 w ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hg := hc.good
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have rok := VG.Proof.Bignum.X86_64.redcRanges_ok wx
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.zeroArr_ok hg (Nat.le_refl _) (by omega) (by omega) (show aXc < 8 by decide))
    fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) s.mem s₁.mem := Frm.of_outside ho₁ (by simp [VG.Proof.Bignum.X86_64.redcRanges])
  have hc₁ := hc.of_frm f₁ rok k₁.2.2 (k₁.gpr (by decide))
  have hl : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc₁.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hln : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi' =>
    hc₁.scr.ld (by have := hdr_lt_slot w 8 hi'; omega)
  have hst : ∀ i < 32, InRegions s₁.wr (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc₁.good.scr.st (by have := hdr_lt_slot wx 8 hi'; omega)
  have hA : wv s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun q hq => (wv_eq_zero_iff _ _ _ _).mp hz₁ q (by omega)
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside s₁.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * sSrc) (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) (by decide)
  have hW : (s₁.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc)) (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j))).readW (VG.Proof.Bignum.X86_64.off B (8 * sW)) 64 =
      BitVec.ofNat 64 w :=
    ((Frm.of_outside (rs := [(8 * sSrc, 8)]) o1 (by simp)).word_below (L := VG.Proof.Bignum.X86_64.slot wx 8)
      (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sSrc sFn VG.Proof.Bignum.X86_64.slot hdrBytes; omega) (by omega)
      (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes at hi; omega) (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)).trans
      hc₁.nw
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = (s₁.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc))
      (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j))).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sRem)) (BitVec.ofNat 64 w))
    (by xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hc₁.rdi, hdrOff, hl sLink (by decide), hc₁.link, hln (sArr j) (by unfold sArr; omega),
      hc₁.narr j hj, hst sSrc (by decide), hln sW (by decide), hW, hst sRem (by decide)]) rfl)
    fun t ⟨hm, k₂⟩ => ?_
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (s₁.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc)) (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j))) (VG.Proof.Bignum.X86_64.off B o)
    (d := 8 * sRem) (BitVec.ofNat 64 w) (by decide)
  rw [← hm] at o2
  have f₂ : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) s₁.mem t.mem :=
    (Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.redcRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.redcRanges]))
  have hc₂ := hc₁.of_frm f₂ rok k₂.2.2 (k₂.gpr (by decide))
  refine ⟨hc₂, ?_, ?_, ?_, f₁.trans f₂, (k₁.trans k₂).mono (by decide)⟩
  · have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    rw [o2.wv (by unfold sRem sFn; omega) (by omega), o1.wv (by unfold sSrc sFn; omega) (by omega)]
    exact hA
  · rw [o2.word (by unfold sSrc sRem sFn; omega) (by unfold sSrc sFn; omega)]
    exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · rw [hm]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _

/-- A chunk into its array: at most `w_X` words. -/
def redcLoad : List (Prog isa) := [
  zeroArr aChunk,
  .block [.mov .r12 (.mem (hdr sRem)), .alu .cmp .r12 (.mem (hdr sW))],
  .ite .b (.block []) (.block [.mov .r12 (.mem (hdr sW))]),
  .block [.mov .rsi (.mem (hdr sSrc)), .mov .rbx (.mem (hdr (sArr aChunk)))],
  copyWords]

/-- The words left and the source advanced, and `A := A R⁻¹ + c R⁻¹`. -/
def redcAcc (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sRem)), .alu .sub .rax (.reg .r12), .store (hdr sRem) .rax,
    .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12),
    .alu .add .r12 (.mem (hdr sSrc)), .store (hdr sSrc) .r12],
  mul aXc aXc Public.aOne,
  mul aT aChunk Public.aOne,
  addMod aXc aXc aT,
  .block [.mov .rax (.mem (hdr sRem)), .alu .test .rax (.reg .rax)]]

theorem redc_eq (mul : Nat → Nat → Nat → Prog isa) (j : Nat) :
    redc mul j = [zeroArr aXc,
      .block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax (sArr j))), .store (hdr sSrc) .rdx,
        .mov .rdx (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sW)), .store (hdr sRem) .rdx],
      .loop (seqs (VG.Proof.Bignum.X86_64.redcLoad ++ VG.Proof.Bignum.X86_64.redcAcc mul)) .ne] := rfl

theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a).toNat < (BitVec.ofNat 64 b).toNat) = (a < b) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- A chunk of `r` words left (at least 1), at offset `e` of `B`, into the
chunk array: `min r w_X` words, the rest zero. -/
theorem redcLoad_ok {t : State} {B : Addr} {Z o w wx j : Nat} {minv : BitVec 64}
    (hc : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hj : j < 8)
    {r e : Nat} (hr1 : 1 ≤ r) (hj0 : VG.Proof.Bignum.X86_64.slot w j ≤ e) (hre : e + 8 * r ≤ VG.Proof.Bignum.X86_64.slot w j + 8 * w)
    (hrem : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 r)
    (hsrc : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B e) :
    WP isa (seqs VG.Proof.Bignum.X86_64.redcLoad) t fun t' =>
      VG.Proof.Bignum.X86_64.SubCtx t' B Z o w wx minv ∧ t'.gpr .r12 = BitVec.ofNat 64 (min r wx) ∧
      wv t'.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx = wv t.mem B e (min r wx) ∧
      VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 r ∧ VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B e ∧
      wv t'.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hsl := slot_le (w := w) hj
  have rok := VG.Proof.Bignum.X86_64.redcRanges_ok wx
  have hC := slot_le (w := wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  simp only [VG.Proof.Bignum.X86_64.redcLoad, seqs]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (show aChunk < 8 by decide))
    fun t₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t.mem t₁.mem := Frm.of_outside ho₁ (by simp [VG.Proof.Bignum.X86_64.redcRanges])
  have hc₁ := hc.of_frm f₁ rok k₁.2.2 (k₁.gpr (by decide))
  have hrem₁ : VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 r := by
    rw [ho₁.word (by unfold sRem sFn; omega) (by unfold sRem sFn; omega)]; exact hrem
  have hsrc₁ : VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B e := by
    rw [ho₁.word (by unfold sSrc sFn; omega) (by unfold sSrc sFn; omega)]; exact hsrc
  have hl : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc₁.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  -- `r12 := min r w_X`.
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 r ∧
      t₂.cf = some (decide (r < wx)) ∧ t₂.mem = t₁.mem)
    (by xrun [State.ea, hdr, hc₁.rdi, hdrOff, hl sRem (by decide), hrem₁, hl sW (by decide), hc₁.hdr.hw,
      VG.Proof.Bignum.X86_64.ofNat_lt_ofNat (show r < 2 ^ 64 by omega) (show wx < 2 ^ 64 by omega)]) rfl)
    fun t₂ ⟨⟨h12₂, hcf₂, hm₂⟩, k₂⟩ => ?_)
  have hdi₂ : t₂.gpr .rdi = VG.Proof.Bignum.X86_64.off B o := (k₂.gpr (by decide)).trans hc₁.rdi
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' => by
    rw [k₂.2.1, k₂.2.2]; exact hl i hi'
  have hite : WP isa (.ite .b (.block []) (.block [.mov .r12 (.mem (hdr sW))])) t₂ fun t₃ =>
      t₃.gpr .r12 = BitVec.ofNat 64 (min r wx) ∧ t₃.mem = t₁.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r12] t₂ t₃ := by
    by_cases hrw : r < wx
    · refine WP.ite true (by simp [VG.X86_64.eval, hcf₂, hrw]) (fun _ => WP.block_nil ⟨?_, hm₂, Keep.refl _ _⟩) (by simp)
      rw [h12₂, Nat.min_eq_left (by omega)]
    · refine WP.ite false (by simp [VG.X86_64.eval, hcf₂, hrw]) (by simp) (fun _ => ?_)
      refine WP.mono (WP.keep [.r12] (Q := fun t₃ => t₃.gpr .r12 = BitVec.ofNat 64 (min r wx) ∧
          t₃.mem = t₂.mem)
        (by xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sW (by decide), hm₂, hc₁.hdr.hw, Nat.min_eq_right (show wx ≤ r by omega)])
        rfl) fun t₃ ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2.trans hm₂, k⟩
  refine WP.seq (WP.mono hite fun t₃ ⟨h12₃, hm₃, k₃⟩ => ?_)
  have hdi₃ : t₃.gpr .rdi = VG.Proof.Bignum.X86_64.off B o := (k₃.gpr (by decide)).trans hdi₂
  have hl₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' => by
    rw [k₃.2.1, k₃.2.2]; exact hl₂ i hi'
  refine WP.seq (WP.mono (WP.keep [.rsi, .rbx] (Q := fun t₄ => t₄.gpr .rsi = VG.Proof.Bignum.X86_64.off B e ∧
      t₄.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) ∧ t₄.mem = t₁.mem)
    (by xrun [State.ea, hdr, hdi₃, hdrOff, hl₃ sSrc (by decide), hm₃, hsrc₁, hl₃ (sArr aChunk) (by decide),
      hc₁.hdr.harr aChunk (by decide)]) rfl)
    fun t₄ ⟨⟨hsi₄, hbx₄, hm₄⟩, k₄⟩ => ?_)
  have k14 := (k₂.trans k₃).trans k₄
  have hcnt : 1 ≤ min r wx := by omega
  have hcnt' : min r wx ≤ wx := Nat.min_le_right _ _
  have hcr : min r wx ≤ r := Nat.min_le_left _ _
  have hs₄ := hc₁.scr.congr ((k₄.2.2.trans k₃.2.2).trans k₂.2.2)
  have hgs₄ := hc₁.good.scr.congr ((k₄.2.2.trans k₃.2.2).trans k₂.2.2)
  have hL : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by omega
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  refine WP.mono (copyWords_ok (S := B) (eS := e) (D := VG.Proof.Bignum.X86_64.off B o) (eD := VG.Proof.Bignum.X86_64.slot wx aChunk) (w := min r wx) hsi₄ hbx₄
    ((k₄.gpr (by decide)).trans h12₃) hcnt (by omega) (by omega)
    (fun i hi' => hs₄.ld (by omega)) (fun i hi' => hgs₄.st (by omega))
    (fun i hi' b hb => Or.inr (by
      rcases VG.Proof.Bignum.X86_64.ofs_rebase B (VG.Proof.Bignum.X86_64.off B (e + 8 * i) + BitVec.ofNat 64 b) ho64 with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)] at h1; omega
      · omega))) fun t₅ ⟨hv₅, _, ho₅, k₅⟩ => ?_
  have f₅ : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t₁.mem t₅.mem := by
    rw [← hm₄]; exact Frm.of_outside (ho₅.mono (o' := VG.Proof.Bignum.X86_64.slot wx aChunk) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega))
      (by simp [VG.Proof.Bignum.X86_64.redcRanges])
  have hc₅ := hc₁.of_frm f₅ rok (by rw [k₅.2.2, k₄.2.2, k₃.2.2, k₂.2.2]) ((k14.trans k₅).gpr (by decide))
  refine ⟨hc₅, (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h12₃), ?_, ?_, ?_, ?_, f₁.trans f₅,
    ((k₁.trans k14).trans k₅).mono (by decide)⟩
  · have hz : wv t₅.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk + 8 * min r wx) (wx - min r wx) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
        rw [ho₅.word (by omega) (by omega), hm₄, show VG.Proof.Bignum.X86_64.slot wx aChunk + 8 * min r wx + 8 * q =
          VG.Proof.Bignum.X86_64.slot wx aChunk + 8 * (min r wx + q) by omega]
        exact (wv_eq_zero_iff _ _ _ _).mp hz₁ _ (by omega)
    rw [VG.Proof.Bignum.X86_64.wv_split _ _ _ (show min r wx + (wx - min r wx) = wx by omega), hv₅, hz, Nat.mul_zero, Nat.add_zero, hm₄,
      f₁.wv_below (fun r hr => (rok r hr).2) hL ho64 (by omega)]
  · rw [ho₅.word (by unfold sRem sFn; omega) (by unfold sRem sFn; omega), hm₄]; exact hrem₁
  · rw [ho₅.word (by unfold sSrc sFn; omega) (by unfold sSrc sFn; omega), hm₄]; exact hsrc₁
  · have sp := slot_sep (w := wx) (show aXc ≠ aChunk by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    rw [ho₅.wv (by omega) (by omega), hm₄, ho₁.wv (by omega) (by omega)]

theorem ofNat_dbl (a : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 a = BitVec.ofNat 64 (2 * a) := by
  rw [BitVec.ofNat_add_ofNat, Nat.two_mul]

/-- `M.mm o a 1`, `[o] R ≡ [a]`, in a prime's workspace. -/
theorem mmOne_ok (M : Mont) {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat}
    (hc : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv) (hv : VG.Proof.Bignum.X86_64.XVals t B o wx minv X) (hw2 : 2 ≤ wx) (hw30 : wx < 2 ^ 30)
    (hX1 : 1 < X) {d a : Nat} (hd : d < 8) (ha : a < 8) (d1 : d ≠ Public.aAcc) (d2 : d ≠ Public.aTmp)
    (d3 : a ≠ Public.aAcc) (d5 : a ≠ Public.aTmp) (hr : (VG.Proof.Bignum.X86_64.slot wx d, 8 * (wx + 2)) ∈ VG.Proof.Bignum.X86_64.redcRanges wx) :
    WP isa (M.mm d a Public.aOne) t fun t' => VG.Proof.Bignum.X86_64.SubCtx t' B Z o w wx minv ∧ VG.Proof.Bignum.X86_64.XVals t' B o wx minv X ∧
      wv t'.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx d) wx < X ∧
      wv t'.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx d) wx * 2 ^ (64 * wx) % X = wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx a) wx % X ∧
      Arrays (VG.Proof.Bignum.X86_64.off B o) wx [Public.aAcc, Public.aTmp, d] t.mem t'.mem ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  refine WP.mono (M.mm_ok hc.good (Nat.le_refl _) hw2 (by omega) hd ha (by decide) d1 d2 d3 (by decide) hv.inv
    (by rw [hv.one, hv.n]; exact hX1) d5 (by decide)) fun t' ⟨_, hlt, hm, har, k⟩ => ?_
  rw [hv.n] at hlt hm
  rw [hv.one, Nat.mul_one] at hm
  have hf : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t.mem t'.mem := Frm.of_arrays har fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp [VG.Proof.Bignum.X86_64.redcRanges]
    · simp [VG.Proof.Bignum.X86_64.redcRanges]
    · exact hr
  exact ⟨hc.of_frm hf (VG.Proof.Bignum.X86_64.redcRanges_ok wx) k.2.2 (k.gpr (by decide)), hv.of_frm (by omega) (by omega) hf, hlt, hm,
    har, hf, k⟩

/-- The words left and the source advanced by the chunk's `c` words, and
`A := A R⁻¹ + x_k R⁻¹ mod X`; `ZF` if no words are left. -/
theorem redcAcc_ok (M : Mont) {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat}
    (hc : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv) (hv : VG.Proof.Bignum.X86_64.XVals t B o wx minv X) (hw2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hX1 : 1 < X) {r e c : Nat} (hcr : c ≤ r) (hr : r < 2 ^ 31)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c)
    (hrem : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 r)
    (hsrc : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B e) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.redcAcc M.mm)) t fun t' => VG.Proof.Bignum.X86_64.SubCtx t' B Z o w wx minv ∧ VG.Proof.Bignum.X86_64.XVals t' B o wx minv X ∧
      VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 (r - c) ∧
      VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B (e + 8 * c) ∧ t'.zf = some (decide (r - c = 0)) ∧
      wv t'.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx < X ∧
      (∃ A' T, A' * 2 ^ (64 * wx) % X = wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx % X ∧
        T * 2 ^ (64 * wx) % X = wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx % X ∧
        wv t'.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = (A' + T) % X) ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hi := hc.hi
  have rok := VG.Proof.Bignum.X86_64.redcRanges_ok wx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hst : ∀ i < 32, InRegions t.wr (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi'; omega)
  have hX : ∀ v : BitVec 64, (t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sRem)) v).readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc)) 64 =
      VG.Proof.Bignum.X86_64.off B e := fun v => (hdrStore_hdr t.mem (VG.Proof.Bignum.X86_64.off B o) v (by decide) (by decide) (by decide)).trans hsrc
  simp only [VG.Proof.Bignum.X86_64.redcAcc, seqs]
  -- The words left and the source.
  refine WP.seq (WP.mono (WP.keep [.rax, .r12] (Q := fun t₁ => t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sRem))
      (BitVec.ofNat 64 (r - c))).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc)) (VG.Proof.Bignum.X86_64.off B (e + 8 * c)))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sRem (by decide), hrem, h12, VG.Offset.ofNat_sub_ofNat hcr,
      hst sRem (by decide), VG.Proof.Bignum.X86_64.ofNat_dbl, hX, hl sSrc (by decide), hst sSrc (by decide), VG.Proof.Bignum.X86_64.ofNat_add_off,
      show e + 2 * (2 * (2 * c)) = e + 8 * c by omega]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * sRem) (BitVec.ofNat 64 (r - c)) (by decide)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sRem)) (BitVec.ofNat 64 (r - c))) (VG.Proof.Bignum.X86_64.off B o)
    (d := 8 * sSrc) (VG.Proof.Bignum.X86_64.off B (e + 8 * c)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.redcRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.redcRanges]))
  have hc₁ := hc.of_frm f₁ rok k₁.2.2 (k₁.gpr (by decide))
  have hv₁ := hv.of_frm (by omega) (by omega) f₁
  have hrem₁ : VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 (r - c) := by
    rw [o2.word (by unfold sSrc sRem sFn; omega) (by unfold sRem sFn; omega)]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  have hsrc₁ : VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B (e + 8 * c) := by
    rw [hm₁]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  have hXc₁ : wv t₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx := by
    have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    rw [o2.wv (by unfold sSrc sFn; omega) (by omega), o1.wv (by unfold sRem sFn; omega) (by omega)]
  have hCh₁ : wv t₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx = wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx := by
    have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
    have := slot_le (w := wx) (show aChunk < 8 by decide)
    rw [o2.wv (by unfold sSrc sFn; omega) (by omega), o1.wv (by unfold sRem sFn; omega) (by omega)]
  -- `A' := A R⁻¹`, `T := c R⁻¹`, `A := A' + T mod X`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mmOne_ok M hc₁ hv₁ hw2 (by omega) hX1 (d := aXc) (a := aXc) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [VG.Proof.Bignum.X86_64.redcRanges]))
    fun t₂ ⟨hc₂, hv₂, hlt₂, hm₂, ha₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mmOne_ok M hc₂ hv₂ hw2 (by omega) hX1 (d := aT) (a := aChunk) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp [VG.Proof.Bignum.X86_64.redcRanges]))
    fun t₃ ⟨hc₃, hv₃, hlt₃, hm₃, ha₃, f₃, k₃⟩ => ?_)
  have hn₁ : (VG.Proof.Bignum.X86_64.off B o).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := hn
  have hXc₃ : wv t₃.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = wv t₂.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx :=
    ha₃.wv_of_not_mem (by decide) (by decide) hn₁
  have hCh₂ : wv t₂.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx = wv t₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx :=
    ha₂.wv_of_not_mem (by decide) (by decide) hn₁
  refine WP.seq (WP.mono (addMod_ok hc₃.good.scr hc₃.rdi hc₃.hdr (Nat.le_refl _) hw2 (by omega)
    (o := aXc) (a := aXc) (b := aT) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hv₃.n, hXc₃]; exact hlt₂) (by rw [hv₃.n]; exact hlt₃))
    fun t₄ ⟨hval₄, ha₄, k₄⟩ => ?_)
  rw [hv₃.n] at hval₄
  have f₄ : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t₃.mem t₄.mem := Frm.of_arrays ha₄ fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [VG.Proof.Bignum.X86_64.redcRanges]
  have hc₄ := hc₃.of_frm f₄ rok k₄.2.2 (k₄.gpr (by decide))
  have hv₄ := hv₃.of_frm (by omega) (by omega) f₄
  have hrem₄ : VG.Proof.Bignum.X86_64.word t₄.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 (r - c) := by
    rw [ha₄.hslot (by decide), ha₃.hslot (by decide), ha₂.hslot (by decide)]; exact hrem₁
  have hsrc₄ : VG.Proof.Bignum.X86_64.word t₄.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B (e + 8 * c) := by
    rw [ha₄.hslot (by decide), ha₃.hslot (by decide), ha₂.hslot (by decide)]; exact hsrc₁
  have hl₄ : ∀ i < 32, InRegions (t₄.rd ++ t₄.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc₄.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (r - c = 0)) ∧ t'.mem = t₄.mem)
    (by xrun [State.ea, hdr, hc₄.rdi, hdrOff, hl₄ sRem (by decide), hrem₄, test_eq,
      VG.Proof.Bignum.X86_64.ofNat_beq_zero (show r - c < 2 ^ 64 by omega)]) rfl) fun t' ⟨⟨hz, hm'⟩, k'⟩ => ?_
  have f' : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) t₄.mem t'.mem := by rw [hm']; exact Frm.refl _ _ _
  refine ⟨hc₄.of_frm f' rok k'.2.2 (k'.gpr (by decide)), hv₄.of_frm (by omega) (by omega) f',
    by rw [hm']; exact hrem₄, by rw [hm']; exact hsrc₄, hz, ?_,
    ⟨wv t₂.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx, wv t₃.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aT) wx, ?_, ?_, by rw [hm', hval₄, hXc₃]⟩,
    (((f₁.trans f₂).trans f₃).trans f₄).trans f', ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
  · rw [hm', hval₄]; exact Nat.mod_lt _ (by omega)
  · rw [hm₂, hXc₁]
  · rw [hm₃, hCh₂, hCh₁]

/-- `k < K = ⌈w / w_X⌉` iff the first `k` chunks leave words. -/
theorem lt_chunks {w wx k : Nat} (hwx : 1 ≤ wx) : k < (w + wx - 1) / wx ↔ k * wx < w := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.add_mul, Nat.one_mul]
  omega

/-- After `k` chunks: `A R^k ≡ x mod R^k`. -/
structure RInv (s : State) (B : Addr) (Z o w wx j : Nat) (minv : BitVec 64) (X k : Nat) (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv
  xv : VG.Proof.Bignum.X86_64.XVals t B o wx minv X
  rem : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sRem) = BitVec.ofNat 64 (w - VG.Proof.Bignum.X86_64.lowW w wx k)
  src : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sSrc) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j + 8 * VG.Proof.Bignum.X86_64.lowW w wx k)
  lt : wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx < X
  val : wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx * (2 ^ (64 * wx)) ^ k % X = wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) (VG.Proof.Bignum.X86_64.lowW w wx k) % X
  frm : Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

theorem redcStep_ok (M : Mont) {s t : State} {B : Addr} {Z o w wx j : Nat} {minv : BitVec 64} {X k : Nat}
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) (hX1 : 1 < X) (hj : j < 8)
    (hk : k < (w + wx - 1) / wx) (hI : VG.Proof.Bignum.X86_64.RInv s B Z o w wx j minv X k t) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.redcLoad ++ VG.Proof.Bignum.X86_64.redcAcc M.mm)) t fun t' =>
      t'.zf = some (decide (k + 1 = (w + wx - 1) / wx)) ∧ VG.Proof.Bignum.X86_64.RInv s B Z o w wx j minv X (k + 1) t' := by
  have hkw : k * wx < w := (VG.Proof.Bignum.X86_64.lt_chunks (by omega)).mp hk
  have hk1 : k + 1 = (w + wx - 1) / wx ↔ w ≤ (k + 1) * wx := by
    have := (VG.Proof.Bignum.X86_64.lt_chunks (k := k + 1) (w := w) (wx := wx) (by omega)); omega
  have hlw : VG.Proof.Bignum.X86_64.lowW w wx k = k * wx := Nat.min_eq_right (by omega)
  have hlw1 : VG.Proof.Bignum.X86_64.lowW w wx (k + 1) = k * wx + min (w - k * wx) wx := by
    unfold VG.Proof.Bignum.X86_64.lowW; rw [Nat.add_mul, Nat.one_mul]; omega
  have hn := hI.ctx.scr.nowrap
  have hi := hI.ctx.hi
  have hlo := hI.ctx.lo
  have hsl := slot_le (w := w) hj
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hrem0 := hI.rem
  have hsrc0 := hI.src
  have hval0 := hI.val
  rw [hlw] at hrem0 hsrc0 hval0
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.redcLoad]) (by simp [VG.Proof.Bignum.X86_64.redcAcc])
    (WP.mono (VG.Proof.Bignum.X86_64.redcLoad_ok hI.ctx hw2 hwx hw30 hj (r := w - k * wx) (e := VG.Proof.Bignum.X86_64.slot w j + 8 * (k * wx)) (by omega)
      (by omega) (by omega) hrem0 hsrc0) fun t₁ ⟨hc₁, h12₁, hch₁, hrem₁, hsrc₁, hXc₁, f₁, k₁⟩ => ?_)
  have hv₁ := hI.xv.of_frm (by have := hc₁.good.scr.nowrap; omega) (by omega) f₁
  refine WP.mono (VG.Proof.Bignum.X86_64.redcAcc_ok M hc₁ hv₁ hw2 hwx hw30 hX1 (Nat.min_le_left _ _) (by omega) h12₁ hrem₁ hsrc₁)
    fun t' ⟨hc', hv', hrem', hsrc', hz', hlt', ⟨A', T, hA', hT, hval'⟩, f', k'⟩ => ⟨?_, ?_⟩
  · rw [hz']
    congr 1
    exact decide_eq_decide.mpr (by rw [hk1, Nat.add_mul, Nat.one_mul]; omega)
  have hL : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by omega
  have hsrcv : wv t.mem B (VG.Proof.Bignum.X86_64.slot w j + 8 * (k * wx)) (min (w - k * wx) wx) =
      wv s.mem B (VG.Proof.Bignum.X86_64.slot w j + 8 * (k * wx)) (min (w - k * wx) wx) :=
    hI.frm.wv_below (fun r hr => (VG.Proof.Bignum.X86_64.redcRanges_ok wx r hr).2) hL (by omega) (by omega)
  refine ⟨hc', hv', by rw [hrem', hlw1]; congr 1; omega, by rw [hsrc', hlw1]; congr 1; omega, hlt', ?_,
    hI.frm.trans (f₁.trans f'), ((hI.keep.trans k₁).trans k').mono (by decide)⟩
  rw [hval', hlw1, VG.Proof.Bignum.X86_64.wv_split _ _ _ rfl]
  have hpow : (2 ^ (64 * wx)) ^ k = 2 ^ (64 * (k * wx)) := by
    rw [← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm wx k]
  have := VG.Proof.Bignum.redc_step (k := k) (L := wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) (k * wx)) hA' hT
    (by rw [hXc₁]; exact hval0)
  rw [this, hch₁, hsrcv, hpow, Nat.mul_comm (2 ^ _)]

/-- `redc j`: `A R^K ≡ x (mod X)` for the `w` words `x` of the modulus'
array `j`, `K = ⌈w / w_X⌉`. -/
theorem redc_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X : Nat}
    (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hv : VG.Proof.Bignum.X86_64.XVals s B o wx minv X) (hw2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hX1 : 1 < X) {j : Nat} (hj : j < 8) :
    WP isa (seqs (redc M.mm j)) s fun t => VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv ∧ VG.Proof.Bignum.X86_64.XVals t B o wx minv X ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx < X ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx * 2 ^ (64 * wx * ((w + wx - 1) / wx)) % X =
        wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w % X ∧
      Frm (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.redcRanges wx) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  rw [VG.Proof.Bignum.X86_64.redc_eq]
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.Bignum.X86_64.redcHead_ok hc hw2 hwx hw30 hj)
    fun t₁ ⟨hc₁, hz₁, hsrc₁, hrem₁, f₁, k₁⟩ => ?_))
  have hn := hc.good.scr.nowrap
  have hK : 0 < (w + wx - 1) / wx := (VG.Proof.Bignum.X86_64.lt_chunks (k := 0) (by omega)).mpr (by omega)
  have hl0 : VG.Proof.Bignum.X86_64.lowW w wx 0 = 0 := by simp [VG.Proof.Bignum.X86_64.lowW]
  refine WP.mono (wp_upto (a := 0) (N := (w + wx - 1) / wx) hK (VG.Proof.Bignum.X86_64.RInv s B Z o w wx j minv X)
    (fun k _ hk t hI => VG.Proof.Bignum.X86_64.redcStep_ok M hw2 hwx hw30 hX1 hj hk hI) (fun _ h => h)
    ⟨hc₁, hv.of_frm hn (by omega) f₁, by rw [hl0, Nat.sub_zero]; exact hrem₁,
      by rw [hl0, Nat.mul_zero, Nat.add_zero]; exact hsrc₁, by rw [hz₁]; omega,
      by rw [hz₁, hl0]; rfl, f₁, k₁⟩) fun t hI => ?_
  have hlK : VG.Proof.Bignum.X86_64.lowW w wx ((w + wx - 1) / wx) = w := by
    unfold VG.Proof.Bignum.X86_64.lowW
    have := (VG.Proof.Bignum.X86_64.lt_chunks (k := (w + wx - 1) / wx) (w := w) (wx := wx) (by omega)).not.mp (Nat.lt_irrefl _)
    omega
  have hv' := hI.val
  rw [hlK, ← Nat.pow_mul] at hv'
  exact ⟨hI.ctx, hI.xv, hI.lt, hv', hI.frm, hI.keep⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtWs`. -/
section

/-!
# RSA with the CRT on x86-64: the primes' workspaces

`wsEnd` finds the end of a workspace (`wsEnd_ok`), `wsNew` lays out a new
one there for `max(2, ⌈len / 8⌉)` words, linked back to the modulus'
(`wsNew_ok`), and `loadArr` loads bytes outside the working space into an
array of a prime's workspace (`primeLoad_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The words of a prime's workspace for a length of `len` bytes. -/
def wsWords (len : Nat) : Nat := max 2 ((len + 7) / 8)

theorem sx2 : BitVec.signExtend 64 (2 : BitVec 32) = 2 := by decide

/-- `rax := ` the end of the workspace at `rdx = X`. -/
theorem wsEnd_ok {s : State} {X : Addr} {Z wx : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s X Z) (hdx : s.gpr .rdx = X)
    (hw : VG.Proof.Bignum.X86_64.word s.mem X (8 * sW) = BitVec.ofNat 64 wx)
    (ha : VG.Proof.Bignum.X86_64.word s.mem X (8 * sArr Public.aOne) = VG.Proof.Bignum.X86_64.off X (VG.Proof.Bignum.X86_64.slot wx Public.aOne)) (hZ : VG.Proof.Bignum.X86_64.slot wx 8 ≤ Z) :
    WP isa (.block wsEnd) s fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off X (VG.Proof.Bignum.X86_64.slot wx 8) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off X (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot wx 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (c := .block wsEnd)
    (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off X (VG.Proof.Bignum.X86_64.slot wx 8) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  unfold wsEnd
  xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.ws, hdx, hdrOff, hl (sArr Public.aOne) (by decide), ha, hl sW (by decide), hw, VG.Proof.Bignum.X86_64.sx2]
  rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
  simp only [BitVec.ofNat_add_ofNat, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc]
  congr 2
  unfold VG.Proof.Bignum.X86_64.slot Public.aOne; omega

/-- `rax := ` the end of a prime's workspace at `rdx = X`, past its table. -/
theorem wsEndT_ok {s : State} {X : Addr} {Z wx : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s X Z) (hdx : s.gpr .rdx = X)
    (hw : VG.Proof.Bignum.X86_64.word s.mem X (8 * sW) = BitVec.ofNat 64 wx)
    (ha : VG.Proof.Bignum.X86_64.word s.mem X (8 * sArr Public.aOne) = VG.Proof.Bignum.X86_64.off X (VG.Proof.Bignum.X86_64.slot wx Public.aOne)) (hZ : VG.Proof.Bignum.X86_64.slot wx 8 ≤ Z) :
    WP isa (.block wsEndT) s fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off X (VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off X (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot wx 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (c := .block wsEndT)
    (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off X (VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  unfold wsEndT wsEnd
  simp only [List.cons_append, List.nil_append]
  xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.ws, hdx, hdrOff, hl (sArr Public.aOne) (by decide), ha, hl sW (by decide), hw, VG.Proof.Bignum.X86_64.sx2]
  rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
  simp only [BitVec.ofNat_add_ofNat, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc]
  congr 2
  unfold VG.Proof.Bignum.X86_64.slot VG.Proof.Bignum.X86_64.tabBytes Public.aOne; omega

/-- A change within ranges, each within one of `rs'`, is within `rs'`. -/
theorem Frm.widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' := fun x hx =>
  h x fun r hr' => by
    obtain ⟨r', hr'', h1, h2⟩ := hr r hr'
    have := hx r' hr''
    omega

theorem cf_lt2 {a : Nat} (ha : a < 2 ^ 64) :
    decide ((BitVec.ofNat 64 a).toNat < (2 : BitVec 64).toNat) = decide (a < 2) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; rfl

/-- A new workspace at `off B o` for a number of the length in slot
`slotLen`: its base into slot `slotWs`, its link, `w_X` and the bases of
its arrays. -/
theorem wsNew_ok {s : State} {B : Addr} {Z o len : Nat} {slotWs slotLen : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hax : s.gpr .rax = VG.Proof.Bignum.X86_64.off B o) (hws : slotWs < 32) (hsl : slotLen < 32)
    (hne : slotWs ≠ slotLen) (hlen : VG.Proof.Bignum.X86_64.word s.mem B (8 * slotLen) = BitVec.ofNat 64 len) (hlen' : len < 2 ^ 32)
    (ho : 8 * 32 ≤ o) (hZ : o + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords len) 8 ≤ Z) :
    WP isa (seqs (wsNew slotWs slotLen)) s fun t =>
      VG.Proof.Bignum.X86_64.word t.mem B (8 * slotWs) = VG.Proof.Bignum.X86_64.off B o ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sLink) = B ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sW) = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.wsWords len) ∧
      (∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sArr j) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords len) j)) ∧
      t.gpr .rdi = B ∧ Frm B [(8 * slotWs, 8), (o, 8 * 17)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords len) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hs' : VG.Proof.Bignum.X86_64.Scr s (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords len) 8) := hs.sub hZ (by omega)
  have hX : ∀ v : BitVec 64, (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * slotWs)) v).readW (VG.Proof.Bignum.X86_64.off B (8 * slotLen)) 64 =
      BitVec.ofNat 64 len := fun v => (hdrStore_hdr s.mem B v hws hsl hne).trans hlen
  simp only [wsNew, seqs]
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t₁.cf = some (decide ((len + 7) / 8 < 2)) ∧ t₁.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * slotWs)) (VG.Proof.Bignum.X86_64.off B o))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.st (d := 8 * slotWs) (by omega), hax,
      hs.ld (d := 8 * slotLen) (by omega), hX, VG.Proof.Bignum.X86_64.shr3_w len hlen', VG.Proof.Bignum.X86_64.sx2, VG.Proof.Bignum.X86_64.cf_lt2 (show (len + 7) / 8 < 2 ^ 64 by omega)])
    rfl) fun t₁ ⟨⟨h12₁, hcf₁, hm₁⟩, k₁⟩ => ?_)
  have hite : WP isa (.ite .b (.block [.mov32 .r12 (.imm 2)]) (.block [])) t₁ fun t₂ =>
      t₂.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.wsWords len) ∧ t₂.mem = t₁.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r12] t₁ t₂ := by
    by_cases h2 : (len + 7) / 8 < 2
    · refine WP.ite true (by simp [VG.X86_64.eval, hcf₁, h2]) (fun _ => ?_) (by simp)
      refine WP.mono (WP.keep [.r12] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.wsWords len) ∧
          t₂.mem = t₁.mem) (by
        xrun
        unfold VG.Proof.Bignum.X86_64.wsWords; rw [Nat.max_eq_left (by omega)]; rfl) rfl) fun t₂ ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
    · refine WP.ite false (by simp [VG.X86_64.eval, hcf₁, h2]) (by simp) (fun _ => WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩)
      rw [h12₁]; unfold VG.Proof.Bignum.X86_64.wsWords; rw [Nat.max_eq_right (by omega)]
  refine WP.seq (WP.mono hite fun t₂ ⟨h12₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  have hax₂ : t₂.gpr .rax = VG.Proof.Bignum.X86_64.off B o := (k12.gpr (by decide)).trans hax
  have hs₂' : VG.Proof.Bignum.X86_64.Scr t₂ (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords len) 8) := hs'.congr k12.2.2
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun t₃ => t₃.gpr .rsi = B ∧ t₃.gpr .rdi = VG.Proof.Bignum.X86_64.off B o ∧
      t₃.mem = (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sLink)) B).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sW))
        (BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.wsWords len)))
    (by xrun [State.ea, hdr, hdi₂, hax₂, hdrOff, hs₂'.st (d := 8 * sLink) (by unfold sLink sFn; omega),
      hs₂'.st (d := 8 * sW) (by unfold sW; omega), h12₂]) rfl) fun t₃ ⟨⟨hsi₃, hdi₃, hm₃⟩, k₃⟩ => ?_
  have hs₃' := hs₂'.congr k₃.2.2
  refine WP.mono (setBases_ok hs₃' hdi₃ ((k₃.gpr (by decide)).trans h12₂) (by unfold sArr; omega))
    fun t₄ ⟨harr₄, ho₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₄.mem)
    (by xrun [(k₄.gpr (by decide)).trans hsi₃]) rfl) fun t ⟨⟨hdi', hm'⟩, k'⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem B (d := 8 * slotWs) (VG.Proof.Bignum.X86_64.off B o) (by omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside t₂.mem (VG.Proof.Bignum.X86_64.off B o) (d := 8 * sLink) B (by decide)
  have o3 := VG.Proof.Bignum.X86_64.writeW_outside (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sLink)) B) (VG.Proof.Bignum.X86_64.off B o) (d := 8 * sW)
    (BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.wsWords len)) (by decide)
  rw [← hm₁] at o1
  rw [← hm₃] at o3
  have f₃ : Frm (VG.Proof.Bignum.X86_64.off B o) [(8 * sLink, 8), (8 * sW, 8), (8 * sArr 0, 64)] t₂.mem t.mem := by
    rw [hm']
    exact ((Frm.of_outside o2 (by simp)).trans (Frm.of_outside o3 (by simp))).trans (Frm.of_outside ho₄ (by simp))
  have hL : ∀ r ∈ [(8 * sLink, 8), (8 * sW, 8), (8 * sArr 0, 64)], r.1 + r.2 ≤ 8 * 17 := by
    simp [sLink, sW, sArr, sFn]
  have ho64 : o < 2 ^ 64 := by omega
  have kall := (((k₁.trans k₂).trans k₃).trans k₄).trans k'
  refine ⟨?_, ?_, ?_, fun j hj => by rw [hm']; exact harr₄ j hj, hdi', ?_,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [f₃.word_below hL (by omega) ho64 (by omega), hm₂, hm₁]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · rw [hm', ho₄.word (by unfold sLink sArr sFn; omega) (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · rw [hm', ho₄.word (by unfold sW sArr; omega) (by decide), hm₃]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · have f₁ : Frm B [(8 * slotWs, 8)] s.mem t₂.mem := by rw [hm₂]; exact Frm.of_outside o1 (by simp)
    refine (f₁.append (f₃.rebase ho64 (fun r hr => by have := hL r hr; omega))).widen fun r hr => ?_
    simp only [VG.Proof.Bignum.X86_64.shiftRanges, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    all_goals exact ⟨(o, 8 * 17), by simp, by simp, by simp [sLink, sW, sArr, sFn]⟩
  · by_cases h : r = .rdi
    · subst h; rw [hdi', hdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

/-- `loadArr j sp sl` in a prime's workspace: the bytes whose pointer and
length are in the modulus' header slots `sp` and `sl`, into array `j`. -/
theorem primeLoad_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : VG.Proof.Bignum.X86_64.SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) {j : Nat} (hj : j < 8)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {p : Addr} {bs : List Byte}
    (hp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sp) = p) (hl : VG.Proof.Bignum.X86_64.word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : VG.Proof.Bignum.X86_64.Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hk' : bs.length < 2 ^ 31) (hkw : (bs.length + 7) / 8 ≤ wx) :
    WP isa (seqs (loadArr j sp sl)) s fun t => VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j) wx = Spec.Rsa.os2ip bs ∧
      VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j) (8 * (wx + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h256 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hJ := slot_le (w := wx) hj
  have hJ0 := hdr_lt_slot wx j (show 31 < 32 by decide)
  have ho64 : o < 2 ^ 64 := by omega
  have hr : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot wx j, 8 * (wx + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by
    simp only [List.mem_singleton, forall_eq]; omega
  simp only [loadArr, seqs]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) hj)
    fun t₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx j, 8 * (wx + 2))] s.mem t₁.mem := Frm.of_outside ho₁ (by simp)
  have hc₁ := hc.of_frm f₁ hr k₁.2.2 (k₁.gpr (by decide))
  have hb : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi' =>
    f₁.word_below (fun r hr' => (hr r hr').2) (by omega) ho64 (by omega)
  have hl₁ : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * i)) 8 := fun i hi' =>
    hc₁.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hln : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi' =>
    hc₁.scr.ld (by omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .rcx, .rbx] (Q := fun t₂ => t₂.gpr .rsi = p ∧
      t₂.gpr .rcx = BitVec.ofNat 64 bs.length ∧ t₂.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j) ∧ t₂.mem = t₁.mem)
    (by xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hc₁.rdi, hdrOff, hl₁ sLink (by decide), hc₁.link, hln sp hsp, hb sp hsp, hp,
      hln sl hsl, hb sl hsl, hl, hl₁ (sArr j) (by unfold sArr; omega), hc₁.hdr.harr j hj]) rfl)
    fun t₂ ⟨⟨hsi₂, hcx₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  have hs₂ : VG.Proof.Bignum.X86_64.Scr t₂ (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx 8) := hc₁.good.scr.congr k₂.2.2
  have hsrc₂ : VG.Proof.Bignum.X86_64.Src t₂ B Z p bs := by
    refine hsrc.congrK (rs := mmRegs ++ [.rax, .rsi, .rcx, .rbx]) ?_ (k₁.trans k₂)
    rw [hm₂]
    exact InScr.of_frm (f₁.rebase ho64 fun r hr' => by have := (hr r hr').2; omega) fun r hr' => by
      simp only [VG.Proof.Bignum.X86_64.shiftRanges, List.map_cons, List.map_nil, List.mem_singleton] at hr'
      subst hr'; simp only; omega
  have hw' : (bs.length + 7) / 8 ≤ wx := hkw
  refine WP.mono (loadBE_ok hs₂ hsi₂ hcx₂ hbx₂ rfl hk1 hk' rfl (by omega) (fun i hi' => hsrc₂.rd i hi')
    (fun i hi' => hsrc₂.val i hi') (fun i hi' => Or.inr (by
      have := hsrc₂.out i hi'
      rcases VG.Proof.Bignum.X86_64.ofs_rebase B (p + BitVec.ofNat 64 i) ho64 with ⟨_, h2⟩ | ⟨h1, _⟩
      · omega
      · omega))) fun t ⟨hv, ho, k₃⟩ => ?_
  have f₃ : Frm (VG.Proof.Bignum.X86_64.off B o) [(VG.Proof.Bignum.X86_64.slot wx j, 8 * (wx + 2))] t₂.mem t.mem :=
    Frm.of_outside (ho.mono (o' := VG.Proof.Bignum.X86_64.slot wx j) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  have ho' : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j) (8 * (wx + 2)) s.mem t.mem := by
    intro x hx
    rw [ho x (by omega), hm₂, ho₁ x hx]
  refine ⟨hc₁.of_frm (by rw [← hm₂]; exact f₃) hr (by rw [k₃.2.2, k₂.2.2]) ((k₃.gpr (by decide)).trans
    (k₂.gpr (by decide))), ?_, ho', ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have hz : wv t.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j + 8 * ((bs.length + 7) / 8)) (wx - (bs.length + 7) / 8) = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
      rw [ho.word (by omega) (by omega), hm₂, show VG.Proof.Bignum.X86_64.slot wx j + 8 * ((bs.length + 7) / 8) + 8 * q =
        VG.Proof.Bignum.X86_64.slot wx j + 8 * ((bs.length + 7) / 8 + q) by omega]
      exact (wv_eq_zero_iff _ _ _ _).mp hz₁ _ (by omega)
  rw [VG.Proof.Bignum.X86_64.wv_split _ _ _ (show (bs.length + 7) / 8 + (wx - (bs.length + 7) / 8) = wx by omega), hv, hz,
    Nat.mul_zero, Nat.add_zero]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup`. -/
section

/-!
# RSA with the CRT on x86-64: setting up the primes

`primesSetup`, from the modulus' workspace: the workspaces of `p` and `q`
after it, `p` and `qInv` into `p`'s, and `q` into `q`'s
(`primesSetup_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- A prime's workspace at `off B o`: its header and its link to `B`. -/
structure WsAt (m : Mem) (B : Addr) (o wx : Nat) (minv : BitVec 64) : Prop where
  hdr : Hdr m (VG.Proof.Bignum.X86_64.off B o) wx minv
  link : VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * sLink) = B

/-- Entering a prime's workspace from the modulus'. -/
theorem SubCtx.mk' {t : State} {B : Addr} {Z o w wx : Nat} {minvN minv : BitVec 64}
    (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (hH : Hdr t.mem B w minvN) (hws : VG.Proof.Bignum.X86_64.WsAt t.mem B o wx minv) (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off B o)
    (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o) (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + VG.Proof.Bignum.X86_64.tabBytes wx ≤ Z) : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv :=
  ⟨hs, hdi, hws.hdr, hws.link, hH.hw, hH.harr, hlo, hhi⟩

/-- What a load into an array of the workspace at `off B o` changes, at `B`:
within its arrays. -/
theorem Frm.of_load {B : Addr} {o wx j : Nat} {m m' : Mem} {rs : List (Nat × Nat)}
    (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j) (8 * (wx + 2)) m m') (hj : j < 8) (ho : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64)
    (hr : (o + 256, VG.Proof.Bignum.X86_64.slot wx 8 - 256) ∈ rs) : Frm B rs m m' := by
  have h1 := slot_le (w := wx) hj
  have h2 := hdr_lt_slot wx j (show 31 < 32 by decide)
  have h3 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  refine (Frm.of_outside_off h (by omega) (by omega)).widen fun r hr' => ⟨_, hr, ?_⟩
  rw [List.mem_singleton.mp hr']
  simp only
  omega

theorem SubCtx.ws {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : VG.Proof.Bignum.X86_64.SubCtx t B Z o w wx minv) :
    VG.Proof.Bignum.X86_64.WsAt t.mem B o wx minv :=
  ⟨h.hdr, h.link⟩

theorem WsAt.of_words {m m' : Mem} {B : Addr} {o wx : Nat} {minv : BitVec 64} (h : VG.Proof.Bignum.X86_64.WsAt m B o wx minv)
    (hw : ∀ i < 17, VG.Proof.Bignum.X86_64.word m' (VG.Proof.Bignum.X86_64.off B o) (8 * i) = VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * i)) : VG.Proof.Bignum.X86_64.WsAt m' B o wx minv :=
  ⟨⟨(hw _ (by decide)).trans h.hdr.hw, (hw _ (by decide)).trans h.hdr.hminv,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩, (hw _ (by decide)).trans h.link⟩

/-- The header of the workspace at `off B o` with whatever `-X⁻¹` it holds. -/
theorem hdr_any {m : Mem} {B : Addr} {o wx : Nat} (hw : VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * sW) = BitVec.ofNat 64 wx)
    (ha : ∀ j < 8, VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * sArr j) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx j)) :
    Hdr m (VG.Proof.Bignum.X86_64.off B o) wx (VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * sMinv)) :=
  ⟨hw, rfl, ha⟩

theorem wsWords_le {len w : Nat} (h : len < 8 * w) (hw : 2 ≤ w) : VG.Proof.Bignum.X86_64.wsWords len ≤ w := by
  unfold VG.Proof.Bignum.X86_64.wsWords; omega

/-- The workspaces' layout: `p`'s after the modulus', `q`'s after `p`'s. -/
def offP (w : Nat) : Nat := VG.Proof.Bignum.X86_64.slot w 8
def offQ (w pl : Nat) : Nat := VG.Proof.Bignum.X86_64.slot w 8 + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl)

/-- `primesSetup`: the primes' workspaces, `p` and `qInv` into `p`'s (arrays
`aN` and `aChunk`), and `q` into `q`'s. -/
theorem primesSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {pl ql : Nat} {pp qp ip : Addr}
    {pb qb ib : List Byte} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw30 : w < 2 ^ 28)
    (hZ : VG.Proof.Bignum.X86_64.offQ w pl + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords ql) ≤ Z)
    (hpl : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl) (hql : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql)
    (hpp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sP) = pp) (hqp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQ) = qp) (hip : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQinv) = ip)
    (hpb : VG.Proof.Bignum.X86_64.Src s B Z pp pb) (hqb : VG.Proof.Bignum.X86_64.Src s B Z qp qb) (hib : VG.Proof.Bignum.X86_64.Src s B Z ip ib)
    (hpbl : pb.length = pl) (hqbl : qb.length = ql) (hibl : ib.length = pl)
    (hpl1 : 1 ≤ pl) (hpl2 : pl < 8 * w) (hql1 : 1 ≤ ql) (hql2 : ql < 8 * w) :
    WP isa (seqs primesSetup) s fun t => Good t B Z w minv ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w) ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl) ∧
      (∃ mp, VG.Proof.Bignum.X86_64.WsAt t.mem B (VG.Proof.Bignum.X86_64.offP w) (VG.Proof.Bignum.X86_64.wsWords pl) mp) ∧ (∃ mq, VG.Proof.Bignum.X86_64.WsAt t.mem B (VG.Proof.Bignum.X86_64.offQ w pl) (VG.Proof.Bignum.X86_64.wsWords ql) mq) ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) Public.aN) (VG.Proof.Bignum.X86_64.wsWords pl) = Spec.Rsa.os2ip pb ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) aChunk) (VG.Proof.Bignum.X86_64.wsWords pl) = Spec.Rsa.os2ip ib ∧
      wv t.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) Public.aN) (VG.Proof.Bignum.X86_64.wsWords ql) = Spec.Rsa.os2ip qb ∧
      Frm B [(8 * sWsP, 8), (8 * sWsQ, 8), (VG.Proof.Bignum.X86_64.offP w, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl) + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8)]
        s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hs := hg.scr
  have hpw := VG.Proof.Bignum.X86_64.wsWords_le hpl2 (by omega)
  have hqw := VG.Proof.Bignum.X86_64.wsWords_le hql2 (by omega)
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  unfold VG.Proof.Bignum.X86_64.offQ at hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold primesSetup
  simp only [List.append_assoc]
  -- `p`'s workspace.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp) ?_
  show WP isa (.block (_ ++ wsEnd)) s _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = B ∧ t.mem = s.mem) (by xrun [hg.rdi]) rfl)
    fun s₁ ⟨⟨hdx₁, hm₁⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (VG.Proof.Bignum.X86_64.wsEnd_ok (wx := w) hs₁ hdx₁ (by rw [hm₁]; exact hg.hdr.hw) (by rw [hm₁]; exact hg.hdr.harr _ (by decide))
    (by omega)) fun s₂ ⟨hax₂, hm₂, k₂⟩ => ?_
  have k02 := k₁.trans k₂
  have hm02 : s₂.mem = s.mem := hm₂.trans hm₁
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [wsNew]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.wsNew_ok (o := VG.Proof.Bignum.X86_64.offP w) (len := pl) (hs.congr k02.2.2) ((k02.gpr (by decide)).trans hg.rdi) hax₂
    (by decide) (by decide) (by decide) (by rw [hm02]; exact hpl) (by omega) (by unfold VG.Proof.Bignum.X86_64.offP; omega)
    (by unfold VG.Proof.Bignum.X86_64.offP; omega)) fun s₃ ⟨hWsP₃, hlP₃, hwP₃, haP₃, hdi₃, f₃, k₃⟩ => ?_
  have hs₃ := hs.congr (k02.trans k₃).2.2
  have hb₃ : ∀ i < 32, i ≠ sWsP → VG.Proof.Bignum.X86_64.word s₃.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi hne => by
    rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; unfold sWsP sFn at hne ⊢; omega
      · simp only; unfold VG.Proof.Bignum.X86_64.offP; omega) (by omega), hm02]
  -- `q`'s workspace.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp) ?_
  show WP isa (.block (_ ++ wsEndT)) s₃ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w) ∧ t.mem = s₃.mem)
    (by xrun [State.ea, hdr, hdi₃, hdrOff, hs₃.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hWsP₃]) rfl)
    fun s₄ ⟨⟨hdx₄, hm₄⟩, k₄⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.wsEndT_ok (wx := VG.Proof.Bignum.X86_64.wsWords pl) ((hs.congr ((k02.trans k₃).trans k₄).2.2).sub
    (o := VG.Proof.Bignum.X86_64.offP w) (n := VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8) (by unfold VG.Proof.Bignum.X86_64.offP; omega) (by omega)) hdx₄
    (by rw [hm₄]; exact hwP₃) (by rw [hm₄]; exact haP₃ _ (by decide)) (Nat.le_refl _))
    fun s₅ ⟨hax₅, hm₅, k₅⟩ => ?_
  rw [off_off] at hax₅
  have k05 := ((k02.trans k₃).trans k₄).trans k₅
  have hm35 : s₅.mem = s₃.mem := hm₅.trans hm₄
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [wsNew]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.wsNew_ok (o := VG.Proof.Bignum.X86_64.offQ w pl) (len := ql) (hs.congr k05.2.2) ((k05.gpr (by decide)).trans hg.rdi)
    (by rw [hax₅]; exact congrArg (VG.Proof.Bignum.X86_64.off B) (by unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega)) (by decide) (by decide) (by decide)
    (by rw [hm35, hb₃ _ (by decide) (by decide)]; exact hql) (by omega) (by unfold VG.Proof.Bignum.X86_64.offQ; omega)
    (by unfold VG.Proof.Bignum.X86_64.offQ; omega)) fun s₆ ⟨hWsQ₆, hlQ₆, hwQ₆, haQ₆, hdi₆, f₆, k₆⟩ => ?_
  have k06 := k05.trans k₆
  have hs₆ := hs.congr k06.2.2
  have hoq : VG.Proof.Bignum.X86_64.offP w + 256 ≤ VG.Proof.Bignum.X86_64.offQ w pl := by unfold VG.Proof.Bignum.X86_64.offP VG.Proof.Bignum.X86_64.offQ; omega
  have f36 : Frm B [(8 * sWsQ, 8), (VG.Proof.Bignum.X86_64.offP w + 256, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl) - 256 +
      VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8)] s₃.mem s₆.mem := by
    rw [← hm35]
    refine f₆.widen fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨(VG.Proof.Bignum.X86_64.offP w + 256, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl) - 256 + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8), by simp,
        hoq, ?_⟩
      show VG.Proof.Bignum.X86_64.offQ w pl + 8 * 17 ≤ VG.Proof.Bignum.X86_64.offP w + 256 + (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl) - 256 + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8)
      unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega
  -- Into `p`'s workspace.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp [loadArr]) ?_
  have hWsP₆ : VG.Proof.Bignum.X86_64.word s₆.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w) := by
    rw [f₆.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inl (show 8 * sWsP + 8 ≤ VG.Proof.Bignum.X86_64.offQ w pl by unfold VG.Proof.Bignum.X86_64.offQ; unfold sWsP sFn; omega)) (by unfold sWsP sFn; omega), hm35]
    exact hWsP₃
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w) ∧ t.mem = s₆.mem)
    (by xrun [enterP, State.ea, hdr, hdi₆, hdrOff, hs₆.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hWsP₆]) rfl)
    fun s₇ ⟨⟨hdi₇, hm₇⟩, k₇⟩ => ?_
  have k07 := k06.trans k₇
  have hs₇ := hs.congr k07.2.2
  have hwp2 : 2 ≤ VG.Proof.Bignum.X86_64.wsWords pl := by unfold VG.Proof.Bignum.X86_64.wsWords; omega
  have hwq2 : 2 ≤ VG.Proof.Bignum.X86_64.wsWords ql := by unfold VG.Proof.Bignum.X86_64.wsWords; omega
  -- The modulus' header and `p`'s, as `wsNew` left them.
  have hb₆ : ∀ i < 32, i ≠ sWsP → i ≠ sWsQ → VG.Proof.Bignum.X86_64.word s₇.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hm₇, f36.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * i + 8 ≤ 8 * sWsQ ∨ 8 * sWsQ + 8 ≤ 8 * i
        unfold sWsQ sFn at h2 ⊢; omega
      · exact Or.inl (show 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offP w + 256 by unfold VG.Proof.Bignum.X86_64.offP; omega)) (by omega)]
    exact hb₃ i hi h1
  have hp₆ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₇.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (8 * i) = VG.Proof.Bignum.X86_64.word s₃.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (8 * i) := fun i hi => by
    rw [hm₇, VG.Proof.Bignum.X86_64.word_off, VG.Proof.Bignum.X86_64.word_off, f36.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (show 8 * sWsQ + 8 ≤ VG.Proof.Bignum.X86_64.offP w + 8 * i by unfold VG.Proof.Bignum.X86_64.offP sWsQ sFn; omega)
      · exact Or.inl (show VG.Proof.Bignum.X86_64.offP w + 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offP w + 256 by omega)) (by unfold VG.Proof.Bignum.X86_64.offP; omega)]
  have hHn₇ : Hdr s₇.mem B w minv :=
    ⟨(hb₆ _ (by decide) (by decide) (by decide)).trans hg.hdr.hw,
      (hb₆ _ (by decide) (by decide) (by decide)).trans hg.hdr.hminv,
      fun j hj => (hb₆ _ (by unfold sArr; omega) (by unfold sArr sWsP sFn; omega)
        (by unfold sArr sWsQ sFn; omega)).trans (hg.hdr.harr j hj)⟩
  have hWp₇ : VG.Proof.Bignum.X86_64.WsAt s₇.mem B (VG.Proof.Bignum.X86_64.offP w) (VG.Proof.Bignum.X86_64.wsWords pl) (VG.Proof.Bignum.X86_64.word s₇.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (8 * sMinv)) :=
    ⟨VG.Proof.Bignum.X86_64.hdr_any ((hp₆ _ (by decide)).trans hwP₃) fun j hj => (hp₆ _ (by unfold sArr; omega)).trans (haP₃ j hj),
      (hp₆ _ (by decide)).trans hlP₃⟩
  have hcP₇ := SubCtx.mk' hs₇ hHn₇ hWp₇ hdi₇ (by unfold VG.Proof.Bignum.X86_64.offP; omega) (by unfold VG.Proof.Bignum.X86_64.offP; omega)
  have i07 : VG.Proof.Bignum.X86_64.InScr B Z s.mem s₇.mem := by
    have a := InScr.of_frm (Z := Z) f₃ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * sWsP + 8 ≤ Z; unfold sWsP sFn; omega
      · show VG.Proof.Bignum.X86_64.offP w + 8 * 17 ≤ Z; unfold VG.Proof.Bignum.X86_64.offP; omega)
    have b := InScr.of_frm (Z := Z) f₆ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show 8 * sWsQ + 8 ≤ Z; unfold sWsQ sFn; omega
      · show VG.Proof.Bignum.X86_64.offQ w pl + 8 * 17 ≤ Z; unfold VG.Proof.Bignum.X86_64.offQ; omega)
    rw [hm02] at a
    rw [hm35] at b
    rw [hm₇]; exact a.trans b
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [loadArr]) (by simp [loadArr]) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.primeLoad_ok hcP₇ hwp2 (VG.Proof.Bignum.X86_64.wsWords_le hpl2 (by omega)) (by omega) (j := Public.aN) (by decide)
    (sp := sP) (sl := sPlen) (by decide) (by decide) (by rw [hb₆ _ (by decide) (by decide) (by decide)]; exact hpp)
    (by rw [hb₆ _ (by decide) (by decide) (by decide), hpbl]; exact hpl) (hpb.congrK i07 k07) (by omega)
    (by omega) (by unfold VG.Proof.Bignum.X86_64.wsWords; omega)) fun s₈ ⟨hcP₈, hpv₈, ho₈, k₈⟩ => ?_
  have hPZ : VG.Proof.Bignum.X86_64.offP w + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl) ≤ Z := by unfold VG.Proof.Bignum.X86_64.offP; omega
  have hQZ : VG.Proof.Bignum.X86_64.offQ w pl + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords ql) ≤ Z := by unfold VG.Proof.Bignum.X86_64.offQ; omega
  have fl8 : Frm B [(VG.Proof.Bignum.X86_64.offP w + 256, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 - 256)] s₇.mem s₈.mem :=
    Frm.of_load ho₈ (by decide) (by omega) (by simp)
  have hb₈ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₈.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s₇.mem B (8 * i) := fun i hi =>
    fl8.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offP w + 256 by unfold VG.Proof.Bignum.X86_64.offP; omega)) (by omega)
  have i78 : VG.Proof.Bignum.X86_64.InScr B Z s₇.mem s₈.mem := InScr.of_frm fl8 fun r hr => by
    rw [List.mem_singleton.mp hr]; show VG.Proof.Bignum.X86_64.offP w + 256 + (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 - 256) ≤ Z; omega
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.primeLoad_ok hcP₈ hwp2 (VG.Proof.Bignum.X86_64.wsWords_le hpl2 (by omega)) (by omega) (j := aChunk) (by decide)
    (sp := sQinv) (sl := sPlen) (by decide) (by decide)
    (by rw [hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide)]; exact hip)
    (by rw [hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide), hibl]; exact hpl)
    (hib.congrK (i07.trans i78) (k07.trans k₈)) (by omega) (by omega) (by unfold VG.Proof.Bignum.X86_64.wsWords; omega))
    fun s₉ ⟨hcP₉, hcv₉, ho₉, k₉⟩ => ?_
  have fl9 : Frm B [(VG.Proof.Bignum.X86_64.offP w + 256, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 - 256)] s₈.mem s₉.mem :=
    Frm.of_load ho₉ (by decide) (by omega) (by simp)
  have hb₉ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₉.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s₈.mem B (8 * i) := fun i hi =>
    fl9.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offP w + 256 by unfold VG.Proof.Bignum.X86_64.offP; omega)) (by omega)
  have i89 : VG.Proof.Bignum.X86_64.InScr B Z s₈.mem s₉.mem := InScr.of_frm fl9 fun r hr => by
    rw [List.mem_singleton.mp hr]; show VG.Proof.Bignum.X86_64.offP w + 256 + (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 - 256) ≤ Z; omega
  have hq₉ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₉.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * i) = VG.Proof.Bignum.X86_64.word s₇.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * i) :=
    fun i hi => by
      rw [VG.Proof.Bignum.X86_64.word_off, VG.Proof.Bignum.X86_64.word_off, (fl8.trans fl9).word_eq (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Or.inr (show VG.Proof.Bignum.X86_64.offP w + 256 + (VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 - 256) ≤ VG.Proof.Bignum.X86_64.offQ w pl + 8 * i by
          unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega)) (by unfold VG.Proof.Bignum.X86_64.offQ; omega)]
  -- Into `q`'s workspace.
  have hWsQ₉ : VG.Proof.Bignum.X86_64.word s₉.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl) := by
    rw [hb₉ _ (by decide), hb₈ _ (by decide), hm₇]; exact hWsQ₆
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp) (by simp [loadArr]) ?_
  have hl₉ : ∀ i < 32, InRegions (s₉.rd ++ s₉.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hcP₉.scr.ld (by omega)
  have hlp₉ : InRegions (s₉.rd ++ s₉.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (8 * sLink)) 8 :=
    hcP₉.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl) ∧ t.mem = s₉.mem)
    (by xrun [leave, enterQ, State.ea, hdr, hcP₉.rdi, hdrOff, hlp₉, hcP₉.link, hl₉ sWsQ (by decide), hWsQ₉]) rfl)
    fun s₁₀ ⟨⟨hdi₁₀, hm₁₀⟩, k₁₀⟩ => ?_
  have k010 := ((k07.trans k₈).trans k₉).trans k₁₀
  have hs₁₀ := hs.congr k010.2.2
  have hHn₁₀ : Hdr s₁₀.mem B w minv := by
    rw [hm₁₀]
    exact ⟨(hb₉ _ (by decide)).trans ((hb₈ _ (by decide)).trans hHn₇.hw),
      (hb₉ _ (by decide)).trans ((hb₈ _ (by decide)).trans hHn₇.hminv),
      fun j hj => (hb₉ _ (by unfold sArr; omega)).trans ((hb₈ _ (by unfold sArr; omega)).trans (hHn₇.harr j hj))⟩
  have hqs₇ : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₇.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * i) = VG.Proof.Bignum.X86_64.word s₆.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * i) :=
    fun i _ => by rw [hm₇]
  have hWq₁₀ : VG.Proof.Bignum.X86_64.WsAt s₁₀.mem B (VG.Proof.Bignum.X86_64.offQ w pl) (VG.Proof.Bignum.X86_64.wsWords ql) (VG.Proof.Bignum.X86_64.word s₁₀.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * sMinv)) := by
    rw [hm₁₀]
    exact ⟨VG.Proof.Bignum.X86_64.hdr_any ((hq₉ _ (by decide)).trans ((hqs₇ _ (by decide)).trans hwQ₆))
      fun j hj => (hq₉ _ (by unfold sArr; omega)).trans ((hqs₇ _ (by unfold sArr; omega)).trans (haQ₆ j hj)),
      (hq₉ _ (by decide)).trans ((hqs₇ _ (by decide)).trans hlQ₆)⟩
  have hcQ₁₀ := SubCtx.mk' hs₁₀ hHn₁₀ hWq₁₀ hdi₁₀ (by unfold VG.Proof.Bignum.X86_64.offQ; omega) hQZ
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.primeLoad_ok hcQ₁₀ hwq2 (VG.Proof.Bignum.X86_64.wsWords_le hql2 (by omega)) (by omega) (j := Public.aN) (by decide)
    (sp := sQ) (sl := sQlen) (by decide) (by decide)
    (by rw [hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide)]; exact hqp)
    (by rw [hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hb₆ _ (by decide) (by decide) (by decide), hqbl]; exact hql)
    (hqb.congrK ((i07.trans i78).trans (by rw [hm₁₀]; exact i89)) k010) (by omega) (by omega)
    (by unfold VG.Proof.Bignum.X86_64.wsWords; omega)) fun s₁₁ ⟨hcQ₁₁, hqv₁₁, ho₁₁, k₁₁⟩ => ?_
  have hl₁₁ : InRegions (s₁₁.rd ++ s₁₁.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * sLink)) 8 :=
    hcQ₁₁.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₁₁.mem)
    (by xrun [leave, State.ea, hdr, hcQ₁₁.rdi, hdrOff, hl₁₁, hcQ₁₁.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  have fl11 : Frm B [(VG.Proof.Bignum.X86_64.offQ w pl + 256, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8 - 256)] s₁₀.mem t.mem := by
    rw [hm]; exact Frm.of_load ho₁₁ (by decide) (by omega) (by simp)
  have hbt : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s₁₀.mem B (8 * i) := fun i hi =>
    fl11.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offQ w pl + 256 by unfold VG.Proof.Bignum.X86_64.offQ; omega))
      (by omega)
  have hpt : ∀ i < 17, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (8 * i) = VG.Proof.Bignum.X86_64.word s₇.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offP w)) (8 * i) := fun i hi => by
    rw [VG.Proof.Bignum.X86_64.word_off, VG.Proof.Bignum.X86_64.word_off, fl11.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show VG.Proof.Bignum.X86_64.offP w + 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offQ w pl + 256 by unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega)) (by unfold VG.Proof.Bignum.X86_64.offP; omega),
      hm₁₀, (fl8.trans fl9).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (show VG.Proof.Bignum.X86_64.offP w + 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offP w + 256 by omega))
      (by unfold VG.Proof.Bignum.X86_64.offP; omega)]
  have hqt : ∀ i < 17, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * i) = VG.Proof.Bignum.X86_64.word s₁₀.mem (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.offQ w pl)) (8 * i) :=
    fun i hi => by
      rw [VG.Proof.Bignum.X86_64.word_off, VG.Proof.Bignum.X86_64.word_off, fl11.word_eq (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Or.inl (show VG.Proof.Bignum.X86_64.offQ w pl + 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.offQ w pl + 256 by omega))
        (by unfold VG.Proof.Bignum.X86_64.offQ; omega)]
  have kall := ((k010.trans k₁₁).trans k')
  refine ⟨⟨hs.congr kall.2.2, hdi, ?_⟩, ?_, ?_, ⟨_, hWp₇.of_words hpt⟩, ⟨_, hWq₁₀.of_words hqt⟩, ?_, ?_, ?_, ?_,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · exact ⟨(hbt _ (by decide)).trans hHn₁₀.hw, (hbt _ (by decide)).trans hHn₁₀.hminv,
      fun j hj => (hbt _ (by unfold sArr; omega)).trans (hHn₁₀.harr j hj)⟩
  · rw [hbt _ (by decide), hm₁₀, hb₉ _ (by decide), hb₈ _ (by decide), hm₇]; exact hWsP₆
  · rw [hbt _ (by decide), hm₁₀]; exact hWsQ₉
  · have := slot_le (w := VG.Proof.Bignum.X86_64.wsWords pl) (show Public.aN < 8 by decide)
    have := slot_sep (w := VG.Proof.Bignum.X86_64.wsWords pl) (show Public.aN ≠ aChunk by decide)
    rw [VG.Proof.Bignum.X86_64.wv_off, fl11.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show VG.Proof.Bignum.X86_64.offP w + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) Public.aN + 8 * VG.Proof.Bignum.X86_64.wsWords pl ≤ VG.Proof.Bignum.X86_64.offQ w pl + 256 by
        unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega)) (by unfold VG.Proof.Bignum.X86_64.offP; omega), hm₁₀, ← VG.Proof.Bignum.X86_64.wv_off,
      ho₉.wv (by omega) (by omega)]
    exact hpv₈
  · have := slot_le (w := VG.Proof.Bignum.X86_64.wsWords pl) (show aChunk < 8 by decide)
    rw [VG.Proof.Bignum.X86_64.wv_off, fl11.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Or.inl (show VG.Proof.Bignum.X86_64.offP w + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) aChunk + 8 * VG.Proof.Bignum.X86_64.wsWords pl ≤ VG.Proof.Bignum.X86_64.offQ w pl + 256 by
        unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega)) (by unfold VG.Proof.Bignum.X86_64.offP; omega), hm₁₀, ← VG.Proof.Bignum.X86_64.wv_off]
    exact hcv₉
  · rw [hm]; exact hqv₁₁
  · have f02 : Frm B [(8 * sWsP, 8), (VG.Proof.Bignum.X86_64.offP w, 8 * 17)] s.mem s₃.mem := by rw [← hm02]; exact f₃
    have f36' : Frm B [(8 * sWsQ, 8), (VG.Proof.Bignum.X86_64.offQ w pl, 8 * 17)] s₃.mem s₆.mem := by rw [← hm35]; exact f₆
    have f710 : Frm B [(VG.Proof.Bignum.X86_64.offP w + 256, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 - 256)] s₆.mem s₁₀.mem := by
      rw [hm₁₀, ← hm₇]; exact fl8.trans fl9
    refine (((f02.append f36').append f710).append fl11).widen fun r hr => ?_
    have hP : (VG.Proof.Bignum.X86_64.offP w, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl) + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8) ∈
        [(8 * sWsP, 8), (8 * sWsQ, 8), (VG.Proof.Bignum.X86_64.offP w, VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords pl) 8 + VG.Proof.Bignum.X86_64.tabBytes (VG.Proof.Bignum.X86_64.wsWords pl) + VG.Proof.Bignum.X86_64.slot (VG.Proof.Bignum.X86_64.wsWords ql) 8)] := by
      simp
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hP, Nat.le_refl _, show VG.Proof.Bignum.X86_64.offP w + 8 * 17 ≤ _ by omega⟩
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hP, show VG.Proof.Bignum.X86_64.offP w ≤ VG.Proof.Bignum.X86_64.offQ w pl by unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega,
        show VG.Proof.Bignum.X86_64.offQ w pl + 8 * 17 ≤ _ by unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega⟩
    · exact ⟨_, hP, show VG.Proof.Bignum.X86_64.offP w ≤ VG.Proof.Bignum.X86_64.offP w + 256 by omega, show VG.Proof.Bignum.X86_64.offP w + 256 + _ ≤ _ by omega⟩
    · exact ⟨_, hP, show VG.Proof.Bignum.X86_64.offP w ≤ VG.Proof.Bignum.X86_64.offQ w pl + 256 by unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega,
        show VG.Proof.Bignum.X86_64.offQ w pl + 256 + _ ≤ _ by unfold VG.Proof.Bignum.X86_64.offQ VG.Proof.Bignum.X86_64.offP; omega⟩
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PcMain`. -/
section

/-!
# `vg_rsa_public_precompute` on x86-64: the computation for a valid modulus

`main`, from the header that `entry` leaves, for a valid modulus `m` of `w`
words: `m` and `R² mod m` to `pre`, 1 returned, and the saved registers
restored (`pcMain_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- `m` into its array, and `-m⁻¹`. -/
def pcLoad : List (Prog isa) := [.block head, loadBE,
  .block ([.mov .r10 (.reg .rbx), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .rbx))] ++
    minv ++ [.store (hdr sMinv) .r15])]

/-- `m` and `R² mod m` to `pre`, and 1 returned. -/
def pcOut : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))), .mov .rbx (.mem (hdr sOut))],
  copyWords,
  .block (eightW ++ [.alu .add .rbx (.reg .rax), .mov .rsi (.mem (hdr (sArr aR2)))]),
  copyWords,
  .block ([.mov32 .rax (.imm 1)] ++ exit)]

theorem seqs_one (c : Prog isa) : seqs [c] = c := rfl

theorem pcMain_eq (M : Mont) : Precompute.main M.mm = seqs (VG.Proof.Bignum.X86_64.pcLoad ++ (VG.Proof.Bignum.X86_64.r2Steps M ++ VG.Proof.Bignum.X86_64.pcOut)) := rfl

/-- What the load changes. -/
def pcLoadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (VG.Proof.Bignum.X86_64.slot w aN, 8 * (w + 2)), (8 * sMinv, 8)]

theorem pcLoadRanges_fixed (w : Nat) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.pcLoadRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h1 : VG.Proof.Bignum.X86_64.slot w 0 ≤ VG.Proof.Bignum.X86_64.slot w aN := by unfold VG.Proof.Bignum.X86_64.slot; omega
  simp only [VG.Proof.Bignum.X86_64.pcLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv] at * <;> omega

theorem pcLoadRanges_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.pcLoadRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  simp only [VG.Proof.Bignum.X86_64.pcLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv] at * <;> omega

/-- The load: `w`, the bases, `m`, and `-m⁻¹` for the odd `m`. -/
theorem pcLoad_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * sN) = np)
    (hnb : VG.Proof.Bignum.X86_64.Src s B Z np nb) (hnl : nb.length = k) (hodd : Spec.Rsa.os2ip nb % 2 = 1) :
    WP isa (seqs VG.Proof.Bignum.X86_64.pcLoad) s fun t => ∃ minv, Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ∧
      Frm B (VG.Proof.Bignum.X86_64.pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have hsl : ∀ r ∈ VG.Proof.Bignum.X86_64.pcLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr =>
    (VG.Proof.Bignum.X86_64.pcLoadRanges_le _ r hr).trans hZ
  unfold VG.Proof.Bignum.X86_64.pcLoad
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.setupHead_ok hs hdi hZ (by omega) hK hN)
    fun t₁ ⟨h12, hcx, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (VG.Proof.Bignum.X86_64.pcLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [VG.Proof.Bignum.X86_64.pcLoadRanges])
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.loadArr_ok hs₁ (by decide) hZ (hnb.congrK (InScr.of_frm hf₁' hsl) k₁) hnl (by omega)
    hk hsi hcx hbx) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hf₂ : Frm B (VG.Proof.Bignum.X86_64.pcLoadRanges ((k + 7) / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays1 ha₂ (by simp [VG.Proof.Bignum.X86_64.pcLoadRanges]))
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have hb₂ : ∀ j < 8, VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) := fun j hj => by
    rw [ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj
  have hW₂ : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ha₂.hslot (by decide)]; exact hW₁
  have hodd₀ : (VG.Proof.Bignum.X86_64.word t₂.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN)).toNat % 2 = 1 := by
    rw [← VG.Proof.Bignum.X86_64.wv_mod64 _ _ _ (show 1 ≤ (k + 7) / 8 by omega), Nat.mod_mod_of_dvd _ (by decide), hv₂, hodd]
  have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  have hbx₂ : t₂.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) := (k₂.gpr (by decide)).trans hbx
  rw [VG.Proof.Bignum.X86_64.seqs_one, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r10, .r12, .rbx] (Q := fun t => t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.word t₂.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ∧
      t.mem = t₂.mem) (by
    xrun [State.ea, hdr, at0, hdi₂, hdrOff, hl sW (by decide), hbx₂, hW₂,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs₂.ld (d := VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) (by omega)])
    rfl) fun t₃ ⟨⟨h10₃, h12₃, hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [hbx₃] at hinv
  have hs₄ := (hs₂.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by omega)]) rfl) fun t ⟨hm, k₅⟩ => ?_
  have hm' : t.mem = t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMinv)) (t₄.gpr .r15) := by rw [hm, hm₄, hm₃]
  have hwo : VG.Proof.Bignum.X86_64.Outside B (8 * sMinv) 8 t₂.mem t.mem := by rw [hm']; exact VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)
  refine ⟨t₄.gpr .r15, ⟨hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄, ⟨?_, ?_, fun j hj => ?_⟩⟩, ?_, ?_,
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h12₃),
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10₃),
    hf₂.trans (Frm.of_outside hwo (by simp [VG.Proof.Bignum.X86_64.pcLoadRanges])),
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [hwo.word (by omega) (by omega)]; exact hW₂
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hwo.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega)]; exact hb₂ j hj
  · rw [hwo.wv (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega) (by omega)]
    exact hv₂
  · rw [hwo.word (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega) (by omega)]
    exact hinv

/-! ## The result to `pre` -/

/-- An address outside the working space is past the `n` bytes of a buffer
outside it, from that buffer's start. -/
theorem le_ofs_of_sep {B op x : Addr} {Z n : Nat} (hsep : ∀ i < n, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 i))
    (hx : VG.Proof.Bignum.X86_64.ofs B x < Z) : n ≤ VG.Proof.Bignum.X86_64.ofs op x := by
  rcases Nat.lt_or_ge (VG.Proof.Bignum.X86_64.ofs op x) n with h | h
  · have := hsep (VG.Proof.Bignum.X86_64.ofs op x) h
    rw [show op + BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.ofs op x) = x by
      rw [VG.Proof.Bignum.X86_64.ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]] at this
    omega
  · exact h

/-- A word of a number, as `toWords` gives it. -/
theorem word_eq_ofNat (m : Mem) (B : Addr) (ed w : Nat) {q : Nat} (hq : q < w) :
    VG.Proof.Bignum.X86_64.word m B (ed + 8 * q) = BitVec.ofNat 64 (wv m B ed w / 2 ^ (64 * q)) := by
  apply BitVec.eq_of_toNat_eq
  rw [word_of_wv m B ed w hq, BitVec.toNat_ofNat]

/-- The `2 w` words at `op`: two numbers of `w` words. -/
theorem wordsAt_two {m : Mem} {op : Addr} {w : Nat} {x y : Nat}
    (hx : ∀ i < w, VG.Proof.Bignum.X86_64.word m op (8 * i) = BitVec.ofNat 64 (x / 2 ^ (64 * i)))
    (hy : ∀ i < w, VG.Proof.Bignum.X86_64.word m op (8 * w + 8 * i) = BitVec.ofNat 64 (y / 2 ^ (64 * i))) :
    Spec.Rsa.wordsAt m op (2 * w) = Spec.Rsa.toWords x w ++ Spec.Rsa.toWords y w := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, show 2 * w = w + w by omega, List.range_add,
    List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun i hi => hx i (List.mem_range.mp hi)
  · refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply]
    rw [show 8 * (w + i) = 8 * w + 8 * i by omega]
    exact hy i (List.mem_range.mp hi)

/-- What `main` (and `fail`) leave: the words `ws` to `pre`, the flag `c`
returned, the saved registers restored, and memory outside the working space
and `pre` unchanged. -/
structure PcPost (s t : State) (B : Addr) (Z w : Nat) (op : Addr) (ws : List (BitVec 64)) (c : Bool) :
    Prop where
  words : Spec.Rsa.wordsAt t.mem op (2 * w) = ws
  rax : t.gpr .rax = BitVec.ofNat 64 c.toNat
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i)
  frame : ∀ x, Z ≤ VG.Proof.Bignum.X86_64.ofs B x → 16 * w ≤ VG.Proof.Bignum.X86_64.ofs op x → t.mem x = s.mem x
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

/-- `pcOut`: the arrays of `m` and `R² mod m` to `pre`, 1 returned, and the
saved registers restored. -/
theorem pcOut_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {op : Addr} {N R : Nat}
    (hg : Good s B Z w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30)
    (hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = op) (hn : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N)
    (hr : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aR2) w = R)
    (hpw : ∀ i < 2 * w, InRegions s.wr (VG.Proof.Bignum.X86_64.off op (8 * i)) 8)
    (hps : ∀ i < 16 * w, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 i)) :
    WP isa (seqs VG.Proof.Bignum.X86_64.pcOut) s fun t => VG.Proof.Bignum.X86_64.PcPost s t B Z w op (Spec.Rsa.toWords N w ++ Spec.Rsa.toWords R w) true := by
  have hs := hg.scr
  have hnw := hs.nowrap
  have h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := w) (show 0 < 8 by decide)
  have hsN := slot_le (w := w) (show aN < 8 by decide)
  have hsR := slot_le (w := w) (show aR2 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  -- A byte of the working space is past `pre`'s `16 w` bytes.
  have hsep : ∀ x, VG.Proof.Bignum.X86_64.ofs B x < Z → 16 * w ≤ VG.Proof.Bignum.X86_64.ofs op x := fun x hx => VG.Proof.Bignum.X86_64.le_ofs_of_sep hps hx
  have hsepw : ∀ e, e + 8 * w ≤ Z → ∀ j < w, ∀ b < 8,
      16 * w ≤ VG.Proof.Bignum.X86_64.ofs op (VG.Proof.Bignum.X86_64.off B (e + 8 * j) + BitVec.ofNat 64 b) := fun e he j hj b hb =>
    hsep _ (by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega)
  unfold VG.Proof.Bignum.X86_64.pcOut
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off op 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hl sOut (by decide),
      hg.hdr.hw, hg.hdr.harr aN (by decide), hO]) rfl) fun t₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyWords_ok hsi hbx h12 hw (by omega) (by omega)
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact hs.ld (by omega))
    (fun j hj => by rw [k₁.2.2, Nat.zero_add]; exact hpw j (by omega))
    (fun j hj b hb => Or.inr (by have := hsepw (VG.Proof.Bignum.X86_64.slot w aN) (by omega) j hj b hb; omega)))
    fun t₂ ⟨_, hc₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at hc₂ ho₂
  -- The working space is as it was.
  have hin₂ : ∀ x, VG.Proof.Bignum.X86_64.ofs B x < Z → t₂.mem x = s.mem x := fun x hx =>
    ho₂ x (Or.inr (by have := hsep x hx; omega))
  have hword₂ : ∀ d, d + 8 ≤ Z → VG.Proof.Bignum.X86_64.word t₂.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hin₂ _ (by rw [VG.Proof.Bignum.X86_64.ofs_off B (d := d) (i := b) (by omega)]; omega)
  have k12 := k₁.trans k₂
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hbx₂ : t₂.gpr .rbx = op := by rw [(k₂.gpr (by decide)).trans hbx]; simp [VG.Proof.Bignum.X86_64.off]
  have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 w → r + r + (r + r) + (r + r + (r + r)) =
      BitVec.ofNat 64 (8 * w) := by
    rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
  refine WP.seq (WP.mono (WP.keep [.rax, .rbx, .rsi] (Q := fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off op (8 * w) ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aR2) ∧ t.mem = t₂.mem) (by
    unfold eightW
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ (sArr aR2) (by decide), hword₂ _ (show 8 * sArr aR2 + 8 ≤ Z by
      unfold sArr aR2; omega), hg.hdr.harr aR2 (by decide), h12₂, hbx₂, hax8 _ rfl]) rfl)
    fun t₃ ⟨⟨hbx₃, hsi₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans h12₂
  refine WP.seq (WP.mono (copyWords_ok hsi₃ hbx₃ h12₃ hw (by omega) (by omega)
    (fun j hj => by rw [k13.2.1, k13.2.2]; exact hs.ld (by omega))
    (fun j hj => by
      rw [k13.2.2, show 8 * w + 8 * j = 8 * (w + j) by omega]; exact hpw (w + j) (by omega))
    (fun j hj b hb => Or.inr (by have := hsepw (VG.Proof.Bignum.X86_64.slot w aR2) (by omega) j hj b hb; omega)))
    fun t₄ ⟨_, hc₄, ho₄, k₄⟩ => ?_)
  rw [hm₃] at hc₄ ho₄
  have hin₄ : ∀ x, VG.Proof.Bignum.X86_64.ofs B x < Z → t₄.mem x = s.mem x := fun x hx =>
    (ho₄ x (Or.inr (by have := hsep x hx; omega))).trans (hin₂ x hx)
  have hword₄ : ∀ d, d + 8 ≤ Z → VG.Proof.Bignum.X86_64.word t₄.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hin₄ _ (by rw [VG.Proof.Bignum.X86_64.ofs_off B (d := d) (i := b) (by omega)]; omega)
  have k14 := k13.trans k₄
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans hg.rdi
  have hl₄ : ∀ i < 32, InRegions (t₄.rd ++ t₄.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => by
    rw [k14.2.1, k14.2.2]; exact hl i hi
  rw [VG.Proof.Bignum.X86_64.seqs_one, VG.Proof.Bignum.X86_64.exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (8 * 0) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.word s.mem B (8 * 1) ∧ t.gpr .r12 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 2) ∧
      t.gpr .r13 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 3) ∧ t.gpr .r14 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 4) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 5) ∧ t.mem = t₄.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₄, hdrOff, hl₄ 0 (by decide), hl₄ 1 (by decide), hl₄ 2 (by decide),
      hl₄ 3 (by decide), hl₄ 4 (by decide), hl₄ 5 (by decide), hword₄ (8 * 0) (by omega),
      hword₄ (8 * 1) (by omega), hword₄ (8 * 2) (by omega), hword₄ (8 * 3) (by omega),
      hword₄ (8 * 4) (by omega), hword₄ (8 * 5) (by omega)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₅⟩ => ⟨?_, hax, ?_, ?_, (k14.trans k₅).mono (by decide)⟩
  · rw [hm]
    refine VG.Proof.Bignum.X86_64.wordsAt_two (fun i hi => ?_) (fun i hi => ?_)
    · have h := hc₂ i hi
      rw [Nat.zero_add] at h
      rw [ho₄.word (by omega) (by omega), h, ← hn]
      exact VG.Proof.Bignum.X86_64.word_eq_ofNat _ _ _ _ hi
    · rw [hc₄ i hi, hword₂ _ (by omega), ← hr]
      exact VG.Proof.Bignum.X86_64.word_eq_ofNat _ _ _ _ hi
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm, ho₄ x (Or.inr (by omega)), ho₂ x (Or.inr (by omega))]

/-- The precomputed values of a valid modulus. -/
theorem publicPrecompute_some {nb : List Byte} {k : Nat} (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.toWords (Spec.Rsa.os2ip nb) ((k + 7) / 8) ++
      Spec.Rsa.toWords (2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb) ((k + 7) / 8)) := by
  simp only [Spec.Rsa.publicPrecompute, hnl, hv, ite_true]; rfl

/-- `main`, for a valid modulus `m`: `m` and `R² mod m` to `pre`, and 1
returned. -/
theorem pcMain_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np : Addr} {nb : List Byte} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = op) (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * sN) = np) (hnb : VG.Proof.Bignum.X86_64.Src s B Z np nb) (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hpw : ∀ i < 2 * ((k + 7) / 8), InRegions s.wr (VG.Proof.Bignum.X86_64.off op (8 * i)) 8)
    (hps : ∀ i < 16 * ((k + 7) / 8), Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 i)) :
    WP isa (Precompute.main M.mm) s fun t => ∃ ws, Spec.Rsa.publicPrecompute nb = some ws ∧
      VG.Proof.Bignum.X86_64.PcPost s t B Z ((k + 7) / 8) op ws true := by
  obtain ⟨hodd, hN1, hlo⟩ := VG.Proof.Bignum.X86_64.valid_facts hv hk1
  have hn := hs.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  rw [VG.Proof.Bignum.X86_64.pcMain_eq M]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.pcLoad]) (by simp [VG.Proof.Bignum.X86_64.r2Steps])
    (WP.mono (VG.Proof.Bignum.X86_64.pcLoad_ok hs hdi hZ (by omega) (by omega) hK hN hnb hnl hodd)
      fun t₁ ⟨minv, hg₁, hn₁, hinv₁, h12₁, h10₁, f₁, k₁⟩ => ?_)
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.r2Steps]) (by simp [VG.Proof.Bignum.X86_64.pcOut])
    (WP.mono (VG.Proof.Bignum.X86_64.r2_ok M hg₁ hZ (by omega) (by omega) hn₁ hinv₁ h12₁ h10₁ hodd hlo)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have x₁₂ := (Fixed.of_frm f₁ (VG.Proof.Bignum.X86_64.pcLoadRanges_fixed _)).trans (Fixed.of_frm f₂ (VG.Proof.Bignum.X86_64.r2Ranges_fixed _))
  have i₁₂ : VG.Proof.Bignum.X86_64.InScr B Z s.mem t₂.mem := (InScr.of_frm f₁ fun r hr => (VG.Proof.Bignum.X86_64.pcLoadRanges_le _ r hr).trans hZ).trans
    (InScr.of_frm f₂ fun r hr => (VG.Proof.Bignum.X86_64.r2Ranges_le _ r hr).trans hZ)
  have k₁₂ := k₁.trans k₂
  have hR : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) ((k + 7) / 8) =
      2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    rw [← Nat.mod_eq_of_lt hlt₂, hr₂, ← Nat.pow_add]; congr 2; omega
  refine WP.mono (VG.Proof.Bignum.X86_64.pcOut_ok hg₂ hZ (by omega) (by omega) (by rw [x₁₂ sOut (by decide)]; exact hO)
    (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hn₁) hR
    (fun i hi => by rw [k₁₂.2.2]; exact hpw i hi) hps)
    fun t hp => ⟨_, VG.Proof.Bignum.X86_64.publicPrecompute_some hnl hv, hp.words, hp.rax,
      fun i hi => by rw [hp.saved i hi]; exact x₁₂ i (by omega),
      fun x hx hx' => by rw [hp.frame x hx hx', i₁₂ x hx], (k₁₂.trans hp.keep).mono (by decide)⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PdMain`. -/
section

/-!
# `vg_rsa_public_precomputed` on x86-64: the computation

The load of `m` and `R² mod m` from `pre`, and the checks that refuse values
no modulus has (`pdLoad_ok`); then the input, `-m⁻¹`, the exponentiation and
the result, for any values that pass the checks (`pdRest_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Precomputed
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## The load and the checks -/

theorem check_eq (a top : BitVec 64) (c : Bool) :
    (a &&& 1 &&& VG.Proof.Bignum.X86_64.mask c &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (top.toNat < BitVec.toNat (1 : BitVec 64)))) + 1 &&&
      (a &&& 1 &&& VG.Proof.Bignum.X86_64.mask c &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (top.toNat < BitVec.toNat (1 : BitVec 64)))) + 1)
      == 0) = !(decide (a.toNat % 2 = 1) && c && decide (top ≠ 0)) := by
  have h1 : a &&& 1 = BitVec.ofNat 64 (a.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat]
    omega
  have h2 : decide (top.toNat < BitVec.toNat (1 : BitVec 64)) = decide (top = 0) :=
    decide_eq_decide.mpr ⟨fun h => BitVec.eq_of_toNat_eq (by
      rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at h; rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
      omega),
      fun h => by subst h; decide⟩
  rw [h1, h2, decide_not]
  generalize decide (top = 0) = z
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h | h <;> rw [h] <;> cases c <;> cases z <;> decide

/-- The checks' last block: ZF clear iff `m` (at `r10`, `w` words) is odd, its
top word is not zero, and `rbp` is the mask of a true `c`. -/
theorem checkBlk_ok {t : State} {B : Addr} {Z w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (h10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN))
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {c : Bool}
    (hbp : t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (.block [.mov .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .and .rax (.reg .rbp),
      .mov .rdx (.mem (ix .r10 .r12 (-8))), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
      .alu .add .rdx (.imm 1), .alu .and .rax (.reg .rdx), .alu .test .rax (.reg .rax)]) t fun t' =>
      t'.zf = some (!(decide ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1) && c &&
        decide (VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1)) ≠ 0))) ∧ t'.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] t t' := by
  have hn := hs.nowrap
  have := slot_le (w := w) (show aN < 8 by decide)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.zf = some (!(decide ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat % 2 = 1) && c &&
        decide (VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1)) ≠ 0))) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩
  xrun [State.ea, ix, at0, addrm8 (b := VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN)) rfl h12 (by omega), h10, hbp,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    hs.ld (show VG.Proof.Bignum.X86_64.slot w aN + 8 * (w - 1) + 8 ≤ Z by omega), hs.ld (show VG.Proof.Bignum.X86_64.slot w aN + 8 ≤ Z by omega)]
  rw [VG.Proof.Bignum.X86_64.check_eq]

/-- What the load changes. -/
def pdLoadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (VG.Proof.Bignum.X86_64.slot w aN, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aR2, 8 * (w + 2))]

theorem pdLoadRanges_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.pdLoadRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  have := slot_le (w := w) (show aR2 < 8 by decide)
  simp only [VG.Proof.Bignum.X86_64.pdLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr] at * <;> omega

theorem pdLoadRanges_fixed (w : Nat) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.pdLoadRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h1 : VG.Proof.Bignum.X86_64.slot w 0 ≤ VG.Proof.Bignum.X86_64.slot w aN := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have h2 : VG.Proof.Bignum.X86_64.slot w 0 ≤ VG.Proof.Bignum.X86_64.slot w aR2 := by unfold VG.Proof.Bignum.X86_64.slot; omega
  simp only [VG.Proof.Bignum.X86_64.pdLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr] at * <;> omega

/-- The load: `w`, the bases, `m` and `R² mod m` from `pre` (at `pp`, the
`2 w` words outside the working space), and ZF clear iff they pass the
checks. -/
theorem pdLoad_ok {s : State} {B : Addr} {Z k : Nat} {pp : Addr} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * sN) = pp)
    (hpr : ∀ i < 2 * ((k + 7) / 8), InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off pp (8 * i)) 8)
    (hps : ∀ j < 16 * ((k + 7) / 8), Z ≤ VG.Proof.Bignum.X86_64.ofs B (pp + BitVec.ofNat 64 j)) :
    WP isa (seqs Precomputed.load) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j)) ∧
      t.zf = some (!(decide ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN)).toNat % 2 = 1) &&
        decide (wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) ((k + 7) / 8) < wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ((k + 7) / 8)) &&
        decide (VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 - 1)) ≠ 0))) ∧
      Frm B (VG.Proof.Bignum.X86_64.pdLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  have hsR := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide)
  have hNR : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 + 2) ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2 := by
    unfold VG.Proof.Bignum.X86_64.slot aN aR2; omega
  have h0N : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 0 ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have hsl : ∀ r ∈ VG.Proof.Bignum.X86_64.pdLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => (VG.Proof.Bignum.X86_64.pdLoadRanges_le _ r hr).trans hZ
  -- A word of `pre` is outside the working space.
  have hpsep : ∀ e, e + 8 * ((k + 7) / 8) ≤ 16 * ((k + 7) / 8) → ∀ j < (k + 7) / 8, ∀ b < 8,
      Z ≤ VG.Proof.Bignum.X86_64.ofs B (VG.Proof.Bignum.X86_64.off pp (e + 8 * j) + BitVec.ofNat 64 b) := fun e he j hj b hb => by
    have := hps (e + 8 * j + b) (by omega)
    rwa [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  unfold Precomputed.load
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.setupHead_ok hs hdi hZ (by omega) hK hN)
    fun t₁ ⟨h12, _, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (VG.Proof.Bignum.X86_64.pdLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [VG.Proof.Bignum.X86_64.pdLoadRanges])
  have hi₁ := InScr.of_frm hf₁' hsl
  -- `m`.
  refine WP.seq (WP.mono (copyWords_ok (S := pp) (eS := 0) (by rw [hsi]; simp [VG.Proof.Bignum.X86_64.off]) hbx h12 (by omega) (by omega)
    (by omega) (fun j hj => by rw [k₁.2.1, k₁.2.2, Nat.zero_add]; exact hpr j (by omega))
    (fun j hj => by rw [k₁.2.2]; exact hs.st (by omega))
    (fun j hj b hb => Or.inr (by have := hpsep 0 (by omega) j hj b hb; omega))) fun t₂ ⟨hv₂, _, ho₂, k₂⟩ => ?_)
  have hm₂ : wv t₁.mem pp 0 ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) :=
    wv_congr fun i hi => Mem.readW_congr fun b hb => hi₁ _ (hpsep 0 (by omega) i hi b (by omega))
  rw [hm₂] at hv₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  have hW₂ : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₂.word (by omega) (by omega)]; exact hW₁
  have hb₂ : ∀ j < 8, VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₂.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega)]; exact hb₁ j hj
  have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 ((k + 7) / 8) → r + r + (r + r) + (r + r + (r + r)) =
      BitVec.ofNat 64 (8 * ((k + 7) / 8)) := by
    rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
  -- `R² mod m`'s registers.
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = VG.Proof.Bignum.X86_64.off pp (8 * ((k + 7) / 8)) ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) ∧ t.mem = t₂.mem) (by
    unfold eightW
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega), hb₂ aR2 (by decide),
      (k₂.gpr (by decide)).trans h12, (k₂.gpr (by decide)).trans hsi, hax8 _ rfl]) rfl)
    fun t₃ ⟨⟨hsi₃, hbx₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  -- `R² mod m`.
  refine WP.seq (WP.mono (copyWords_ok hsi₃ hbx₃ ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))
    (by omega) (by omega) (by omega)
    (fun j hj => by rw [k13.2.1, k13.2.2, show 8 * ((k + 7) / 8) + 8 * j = 8 * ((k + 7) / 8 + j) by omega]
                    exact hpr _ (by omega))
    (fun j hj => by rw [k13.2.2]; exact hs.st (by omega))
    (fun j hj b hb => Or.inr (by have := hpsep (8 * ((k + 7) / 8)) (by omega) j hj b hb; omega)))
    fun t₄ ⟨hv₄, _, ho₄, k₄⟩ => ?_)
  have hm₄ : wv t₃.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) := by
    rw [hm₃]
    exact wv_congr fun i hi => Mem.readW_congr fun b hb => (ho₂ _ (Or.inr (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega) i hi b (by omega); omega))).trans (hi₁ _ (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega) i hi b (by omega); omega))
  rw [hm₄] at hv₄
  have k14 := k13.trans k₄
  have hs₄ := hs.congr k14.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans hdi
  have hN₄ : wv t₄.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) := by
    rw [ho₄.wv (by omega) (by omega), hm₃]; exact hv₂
  have hb₄ : ∀ j < 8, VG.Proof.Bignum.X86_64.word t₄.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₄.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega), hm₃]; exact hb₂ j hj
  have hW₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₄.word (by omega) (by omega), hm₃]; exact hW₂
  have h12₄ : t₄.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) :=
    (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))
  have hbx₄ : t₄.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) := (k₄.gpr (by decide)).trans hbx₃
  -- The comparison's registers.
  refine WP.seq (WP.mono (WP.keep [.r10, .rbp] (Q := fun t => t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = t₄.mem) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.ld (d := 8 * sArr aN) (by unfold sArr aN; omega), hb₄ aN (by decide)])
    rfl) fun t₅ ⟨⟨h10₅, hbp₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  refine WP.seq (WP.mono (cmpLoop_ok hs₅ ((k₅.gpr (by decide)).trans hbx₄) h10₅ ((k₅.gpr (by decide)).trans h12₄)
    hbp₅ (by omega) (by omega) (by omega) (by omega)) fun t₆ ⟨hbp₆, hm₆, k₆⟩ => ?_)
  rw [hm₅] at hbp₆
  have hs₆ := hs₅.congr k₆.2.2
  rw [VG.Proof.Bignum.X86_64.seqs_one]
  refine WP.mono (VG.Proof.Bignum.X86_64.checkBlk_ok hs₆ ((k₆.gpr (by decide)).trans h10₅)
    ((k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans h12₄)) (by omega) hZ hbp₆) fun t ⟨hz, hm, k₇⟩ => ?_
  have hmm : t.mem = t₄.mem := by rw [hm, hm₆, hm₅]
  refine ⟨by rw [hmm]; exact hN₄, by rw [hmm]; exact hv₄, by rw [hmm]; exact hW₄,
    fun j hj => by rw [hmm]; exact hb₄ j hj, by rw [hz, hm₆, hm₅, hmm], ?_,
    ((((k14.trans k₅).trans k₆).trans k₇)).mono (by decide)⟩
  rw [hmm]
  have f₂ : Frm B (VG.Proof.Bignum.X86_64.pdLoadRanges ((k + 7) / 8)) t₁.mem t₂.mem :=
    Frm.of_outside (ho₂.mono (o' := VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega))
      (by simp [VG.Proof.Bignum.X86_64.pdLoadRanges])
  have f₄ : Frm B (VG.Proof.Bignum.X86_64.pdLoadRanges ((k + 7) / 8)) t₃.mem t₄.mem :=
    Frm.of_outside (ho₄.mono (o' := VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega))
      (by simp [VG.Proof.Bignum.X86_64.pdLoadRanges])
  rw [hm₃] at f₄
  exact (hf₁'.trans f₂).trans f₄

/-! ## The computation -/

/-- The input's load. -/
def pdIn : List (Prog isa) :=
  [.block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))], loadBE]

/-- `X = input R`, the exponentiation and `Y R⁻¹`. -/
def pdExp (M : Mont) : List (Prog isa) := [M.mm aXm aX aR2, Precomputed.expLoop M.mm, Precomputed.finish M.mm]

theorem pdRest_eq (M : Mont) : Precomputed.rest M.mm = seqs ((VG.Proof.Bignum.X86_64.pdIn ++ VG.Proof.Bignum.X86_64.restSteps) ++ (VG.Proof.Bignum.X86_64.pdExp M ++ VG.Proof.Bignum.X86_64.outSteps)) := rfl

/-- What `rest` starts from: the header `entry` leaves, `m` and `R² mod m`
(here any `R < N`) in their arrays, as the checks accepted them. -/
structure PdPre (s : State) (B : Addr) (Z k : Nat) (op ep ip : Addr) (L : Nat) (eb xb : List Byte) (N R : Nat) :
    Prop where
  scr : VG.Proof.Bignum.X86_64.Scr s B Z
  rdi : s.gpr .rdi = B
  z : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sOut) = op
  hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hE : VG.Proof.Bignum.X86_64.word s.mem B (8 * sE) = ep
  hL : VG.Proof.Bignum.X86_64.word s.mem B (8 * sElen) = BitVec.ofNat 64 L
  hIn : VG.Proof.Bignum.X86_64.word s.mem B (8 * sIn) = ip
  hW : VG.Proof.Bignum.X86_64.word s.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8)
  hb : ∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j)
  n : wv s.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aN) ((k + 7) / 8) = N
  r : wv s.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R
  odd : N % 2 = 1
  n1 : 1 < N
  rlt : R < N
  x : VG.Proof.Bignum.X86_64.Src s B Z ip xb
  e : VG.Proof.Bignum.X86_64.Src s B Z ep eb
  xl : xb.length = k
  el : eb.length = L
  L1 : 1 ≤ L
  L2 : L ≤ k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 j)

/-- `x` with `x R ≡ X`, for `R` invertible modulo `N > 1`. -/
theorem exists_mont {R N : Nat} (hR : Nat.Coprime R N) (hN1 : 1 < N) (X : Nat) :
    ∃ x, X % N = x * R % N := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hN1
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

/-- The input into its array. -/
theorem pdIn_ok {s : State} {B : Addr} {Z k : Nat} {ip : Addr} {xb : List Byte} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hIn : VG.Proof.Bignum.X86_64.word s.mem B (8 * sIn) = ip)
    (hb : ∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j)) (hx : VG.Proof.Bignum.X86_64.Src s B Z ip xb)
    (hxl : xb.length = k) :
    WP isa (seqs VG.Proof.Bignum.X86_64.pdIn) s fun t => wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      Arrays B ((k + 7) / 8) [aX] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eIn : sIn = 21 := rfl
  have eAX : sArr aX = 9 := rfl
  unfold VG.Proof.Bignum.X86_64.pdIn
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = ip ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sIn) (by omega), hs.ld (d := 8 * sK) (by omega),
      hs.ld (d := 8 * sArr aX) (by omega), hIn, hK, hb aX (by decide)]) rfl)
    fun t₁ ⟨⟨hsi, hcx, hbx, hm₁⟩, k₁⟩ => ?_)
  rw [VG.Proof.Bignum.X86_64.seqs_one]
  refine WP.mono (VG.Proof.Bignum.X86_64.loadArr_ok (hs.congr k₁.2.2) (by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hxl (by omega) hk hsi hcx hbx)
    fun t ⟨hv, ha, k₂⟩ => ⟨hv, by rw [hm₁] at ha; exact ha, (k₁.trans k₂).mono (by decide)⟩

/-- What `rest` changes. -/
def pdAll (w : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot w aX, 8 * (w + 2)), (8 * sMinv, 8), (8 * sMask, 8), (VG.Proof.Bignum.X86_64.slot w aOne, 8 * (w + 2)),
    (VG.Proof.Bignum.X86_64.slot w aXm, 8 * (w + 2))] ++ pExpRanges w

theorem pdAll_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.pdAll w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have := slot_le (w := w) (show aX < 8 by decide)
  have := slot_le (w := w) (show aOne < 8 by decide)
  have := slot_le (w := w) (show aXm < 8 by decide)
  have := slot_le (w := w) (show aAcc < 8 by decide)
  have := slot_le (w := w) (show aTmp < 8 by decide)
  have := slot_le (w := w) (show aY < 8 by decide)
  simp only [VG.Proof.Bignum.X86_64.pdAll, pExpRanges, pBitRanges, bitRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sMinv, sMask, VG.Impl.Bignum.X86_64.Public.sI, VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, sStarted, sFn] at * <;> omega

theorem pdAll_fixed (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.pdAll w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aX (show 31 < 32 by decide)
  have := hdr_lt_slot w aOne (show 31 < 32 by decide)
  have := hdr_lt_slot w aXm (show 31 < 32 by decide)
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aY (show 31 < 32 by decide)
  simp only [VG.Proof.Bignum.X86_64.pdAll, pExpRanges, pBitRanges, bitRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sMinv, sMask, VG.Impl.Bignum.X86_64.Public.sI, VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, sStarted, sFn] at * <;> omega

/-- The input, the mask of `input < N`, `-m⁻¹` and the number 1. -/
theorem pdSetup_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : VG.Proof.Bignum.X86_64.PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (seqs (VG.Proof.Bignum.X86_64.pdIn ++ VG.Proof.Bignum.X86_64.restSteps)) s fun t => ∃ minv,
      VG.Proof.Bignum.X86_64.SetupOut t B Z ((k + 7) / 8) minv N (Spec.Rsa.os2ip xb) ∧ Frm B (VG.Proof.Bignum.X86_64.pdAll ((k + 7) / 8)) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep mmRegs s t ∧ wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  -- The input.
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.pdIn]) (by simp [VG.Proof.Bignum.X86_64.restSteps])
    (WP.mono (VG.Proof.Bignum.X86_64.pdIn_ok hs h.rdi hZ (by omega) (by omega) h.hK h.hIn h.hb h.x h.xl) fun t₁ ⟨hX₁, ha₁, k₁⟩ => ?_)
  have f₁ : Frm B (VG.Proof.Bignum.X86_64.pdAll ((k + 7) / 8)) s.mem t₁.mem := Frm.of_arrays ha₁ (by simp [VG.Proof.Bignum.X86_64.pdAll])
  -- The mask, `-m⁻¹` and 1.
  refine WP.mono (VG.Proof.Bignum.X86_64.setupRest_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h.rdi) hZ (by omega) (by omega)
      (by rw [ha₁.hslot (by decide)]; exact h.hW) (fun j hj => by rw [ha₁.hslot (by unfold sArr; omega)]; exact h.hb j hj)
      (by rw [ha₁.wv_of_not_mem (by decide) (by decide) hn']; exact h.n) hX₁ h.odd)
      fun t₂ ⟨minv, so, f₂', k₂⟩ => ⟨minv, so, f₁.trans (f₂'.mono (by simp [VG.Proof.Bignum.X86_64.pdAll])), (k₁.trans k₂).mono (by decide), ?_⟩
  rw [f₂'.wv_eq (fun r hr => by
      have := hdr_lt_slot ((k + 7) / 8) aR2 (show 31 < 32 by decide)
      have := slot_sep (w := (k + 7) / 8) (show aR2 ≠ aOne by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sMinv, sMask, sFn] at * <;> omega)
      (by have := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide); omega),
    ha₁.wv_of_not_mem (by decide) (by decide) hn']
  exact h.r

/-- `rest`, for values the checks accepted: `x^e mod N` (or zeros, if the
input is not below `N`) to `out`, for the `x` with `x R ≡ input R² R⁻¹`,
which is the input if `R ≡ R²`. -/
theorem pdRest_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : VG.Proof.Bignum.X86_64.PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (Precomputed.rest M.mm) s fun t => ∃ x : Nat,
      (R % N = 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N → x % N = Spec.Rsa.os2ip xb % N) ∧
      VG.Proof.Bignum.X86_64.MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then x ^ Spec.Rsa.os2ip eb % N else 0)
        (decide (Spec.Rsa.os2ip xb < N)) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hw : 2 ≤ (k + 7) / 8 := by omega
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) N := VG.Proof.Bignum.coprime_pow2 h.odd _
  have hle := VG.Proof.Bignum.X86_64.pdAll_le ((k + 7) / 8)
  have hle' : ∀ r ∈ VG.Proof.Bignum.X86_64.pdAll ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => (hle r hr).trans hZ
  rw [VG.Proof.Bignum.X86_64.pdRest_eq]
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.pdIn]) (by simp [VG.Proof.Bignum.X86_64.pdExp])
    (WP.mono (VG.Proof.Bignum.X86_64.pdSetup_ok h) fun t₂ ⟨minv, so, f₂, k₂, hR₂⟩ => ?_)
  refine VG.Proof.Bignum.X86_64.wp_seqs_append (by simp [VG.Proof.Bignum.X86_64.pdExp]) (by simp [VG.Proof.Bignum.X86_64.outSteps, VG.Proof.Bignum.X86_64.outStepsArr]) ?_
  unfold VG.Proof.Bignum.X86_64.pdExp
  -- `X = input R`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mmN_ok M (o := aXm) (a := aX) (b := aR2) so.good hZ hw (by omega) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) so.n so.inv (by rw [hR₂]; exact h.rlt))
    fun t₃ ⟨hg₃, hn₃, hinv₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [so.x, hR₂] at hm₃
  have f₃ : Frm B (VG.Proof.Bignum.X86_64.pdAll ((k + 7) / 8)) t₂.mem t₃.mem := Frm.of_arrays ha₃ (by simp [VG.Proof.Bignum.X86_64.pdAll, pExpRanges, pBitRanges, bitRanges])
  have f₁₃ := f₂.trans f₃
  have x₁₃ := Fixed.of_frm f₁₃ (VG.Proof.Bignum.X86_64.pdAll_fixed _)
  obtain ⟨x, hx⟩ := VG.Proof.Bignum.X86_64.exists_mont hR h.n1 (wv t₃.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aXm) ((k + 7) / 8))
  have he₃ := h.e.congrK (InScr.of_frm f₁₃ hle') (k₂.trans k₃)
  -- The exponentiation.
  refine WP.seq (WP.mono (pExpLoop_ok (x := x) ⟨hg₃, hn₃, hinv₃, rfl⟩ hZ hw (by omega) hR hlt₃ hx
    (by rw [x₁₃ sE (by decide)]; exact h.hE) (by rw [x₁₃ sElen (by decide)]; exact h.hL) h.el h.L1 (by omega)
    (fun i hi => he₃.rd i (by rw [h.el]; exact hi)) (fun i hi => he₃.val i (by rw [h.el]; exact hi))
    (fun i hi => he₃.out i (by rw [h.el]; exact hi)))
    fun t₄ ⟨hc₄, hy₄, f₄', k₄⟩ => ?_)
  have f₄ : Frm B (VG.Proof.Bignum.X86_64.pdAll ((k + 7) / 8)) t₃.mem t₄.mem := f₄'.mono fun _ hr => List.mem_append_right _ hr
  have hone₄ : wv t₄.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aOne) ((k + 7) / 8) = 1 := by
    rw [f₄'.wv_eq (fun r hr => by
        have := hdr_lt_slot ((k + 7) / 8) aOne (show 31 < 32 by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aAcc by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aTmp by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aY by decide)
        simp only [pExpRanges, pBitRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [VG.Impl.Bignum.X86_64.Public.sI, VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, sStarted, sFn] at * <;>
          omega)
        (by have := slot_le (w := (k + 7) / 8) (show aOne < 8 by decide); omega),
      ha₃.wv_of_not_mem (by decide) (by decide) hn']
    exact so.one
  rw [VG.Proof.Bignum.X86_64.seqs_one]
  refine WP.mono (pFinish_ok hc₄ hZ hw (by omega) hR h.n1 hone₄ hy₄) fun t₅ ⟨hg₅, hY₅, f₅', k₅⟩ => ?_
  have f₅ : Frm B (VG.Proof.Bignum.X86_64.pdAll ((k + 7) / 8)) t₄.mem t₅.mem :=
    f₅'.mono (by simp [finRanges, VG.Proof.Bignum.X86_64.pdAll, pExpRanges, pBitRanges, bitRanges])
  have f₁₅ := (f₁₃.trans f₄).trans f₅
  have x₁₅ := Fixed.of_frm f₁₅ (VG.Proof.Bignum.X86_64.pdAll_fixed _)
  have k₁₅ := ((k₂.trans k₃).trans k₄).trans k₅
  have hM₅ : VG.Proof.Bignum.X86_64.word t₅.mem B (8 * sMask) = VG.Proof.Bignum.X86_64.mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [f₅'.word_eq (fun r hr => by
        have := hdr_lt_slot ((k + 7) / 8) aAcc (show sMask < 32 by decide)
        have := hdr_lt_slot ((k + 7) / 8) aTmp (show sMask < 32 by decide)
        have := hdr_lt_slot ((k + 7) / 8) aY (show sMask < 32 by decide)
        simp only [finRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega) (by unfold sMask sFn; omega),
      f₄'.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega),
      ha₃.hslot (by decide)]
    exact so.mask
  refine WP.mono (VG.Proof.Bignum.X86_64.outPhase_ok hg₅ hZ (by omega) (by omega) hY₅ (by rw [x₁₅ sOut (by decide)]; exact h.hO)
    (by rw [x₁₅ sK (by decide)]; exact h.hK) hM₅ (fun j hj => by rw [k₁₅.2.2]; exact h.out j hj) h.outSep)
    fun t ⟨hb, hax, hsv, hfr, k₆⟩ => ⟨x, fun hRR => ?_, ⟨?_, hax, fun i hi => by rw [hsv i hi]; exact x₁₅ i (by omega),
      fun y hy hy' => by rw [hfr y hy', InScr.of_frm f₁₅ hle' y hy], (k₁₅.trans k₆).mono (by decide)⟩⟩
  · apply VG.Proof.Bignum.mont_cancel hR
    apply VG.Proof.Bignum.mont_cancel hR
    calc x * 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N
        = x * 2 ^ (64 * ((k + 7) / 8)) % N * 2 ^ (64 * ((k + 7) / 8)) % N := (Nat.mod_mul_mod _ _ _).symm
      _ = wv t₃.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) aXm) ((k + 7) / 8) % N * 2 ^ (64 * ((k + 7) / 8)) % N := by rw [hx]
      _ = Spec.Rsa.os2ip xb * R % N := by rw [Nat.mod_mul_mod, hm₃]
      _ = Spec.Rsa.os2ip xb * (R % N) % N := (Nat.mul_mod_mod _ _ _).symm
      _ = Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N := by
        rw [hRR, Nat.mul_mod_mod, Nat.mul_assoc]
  · rw [hb]
    by_cases hc : Spec.Rsa.os2ip xb < N <;> simp [hc]

end VG.Proof.Bignum.X86_64

end
