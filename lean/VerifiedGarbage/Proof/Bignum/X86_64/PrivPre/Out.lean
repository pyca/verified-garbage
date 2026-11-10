module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_private_precompute` on x86-64: the masked copies

`copyMasked` copies `w` words from `rsi` to `rbx`, each and-ed with `r15`
(`copyMasked_ok`); `outArr j` copies the current workspace's array `j` so to
`rbx`, and moves `rbx` past it (`outArr_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (copyMasked outArr outAt out)
open VG.Impl.Rsa.X86_64 (eightW)

/-- After copying `j` words from `S + eS` to `D + eD`, each and-ed with
`v`. -/
structure MCopyInv (s₀ : State) (S D : Addr) (eS eD : Nat) (v : BitVec 64) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, word t.mem D (eD + 8 * i) = word s₀.mem S (eS + 8 * i) &&& v
  frame : Outside D eD (8 * j) s₀.mem t.mem

theorem copyMaskedStep_ok {s₀ : State} {S D : Addr} {eS eD w : Nat} {v : BitVec 64}
    (hsi : s₀.gpr .rsi = off S eS) (hbx : s₀.gpr .rbx = off D eD) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (h15 : s₀.gpr .r15 = v) (hw : w < 2 ^ 32) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s₀.rd ++ s₀.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < w) {t : State} (hI : MCopyInv s₀ S D eS eD v j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax] :
        List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ MCopyInv s₀ S D eS eD v (j + 1) t' := by
  have tsi : t.gpr .rsi = off S eS := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off D eD := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have t15 : t.gpr .r15 = v := (hI.keep.gpr (by decide)).trans h15
  have hld : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.2.2]; exact hwr j hj
  have hv : word t.mem S (eS + 8 * j) = word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (word s₀.mem S (eS + 8 * j) &&& v)) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tsi hI.r14, addr0 tbx hI.r14, hld, hst, hv, t15]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), h14, fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- `copyMasked`: the `w` words at `S + eS`, each and-ed with `v` (in
`r15`), to `D + eD`, which they do not overlap, changing only those. -/
theorem copyMasked_ok {s : State} {S D : Addr} {eS eD w : Nat} {v : BitVec 64}
    (hsi : s.gpr .rsi = off S eS) (hbx : s.gpr .rbx = off D eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (h15 : s.gpr .r15 = v) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s.rd ++ s.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa copyMasked s fun t =>
      (∀ i < w, word t.mem D (eD + 8 * i) = word s.mem S (eS + 8 * i) &&& v) ∧
      Outside D eD (8 * w) s.mem t.mem ∧ Keep [.rax, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      MCopyInv s S D eS eD v 0 t := fun t h14 hm k _ =>
    ⟨k.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (MCopyInv s S D eS eD v) h0
    (fun j _ hj t hI => copyMaskedStep_ok hsi hbx h12 h15 (by omega) hD hrd hwr hsep hj hI)) fun t hI => ?_
  exact ⟨hI.done, hI.frame, hI.keep⟩
/-- `x = p + (x - p)`. -/
theorem eq_add_ofs (p x : Addr) : x = p + BitVec.ofNat 64 (ofs p x) := by
  unfold ofs
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- A byte of a workspace at `o` is one of the working space. -/
theorem ofs_lt_of_sub {B x : Addr} {o n Z : Nat} (ho : o + n ≤ Z) (hZ : B.toNat + Z ≤ 2 ^ 64)
    (hx : ofs (off B o) x < n) : ofs B x < Z := by
  have e := eq_add_ofs (off B o) x
  generalize ofs (off B o) x = m at hx e
  rw [e, ofs_off B (by omega)]; omega

theorem off_add_ofNat (D : Addr) (e a : Nat) : off D e + BitVec.ofNat 64 a = off D (e + a) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- `outArr j`: the array `j` of the workspace at `X`, each word and-ed with
`v` (in `r15`), to `D + eD`, and `rbx` past it. -/
theorem outArr_ok {s : State} {X D : Addr} {Zx wx eD : Nat} {mx v : BitVec 64} {j : Nat}
    (hg : Good s X Zx wx mx) (hZ : slot wx 8 ≤ Zx) (hj : j < 8) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hbx : s.gpr .rbx = off D eD) (h15 : s.gpr .r15 = v) (hD : eD + 8 * wx ≤ 2 ^ 64)
    (hwr : ∀ i < wx, InRegions s.wr (off D (eD + 8 * i)) 8)
    (hsep : ∀ i < wx, ∀ b < 8, ofs D (off X (slot wx j + 8 * i) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * wx ≤ ofs D (off X (slot wx j + 8 * i) + BitVec.ofNat 64 b)) :
    WP isa (seqs (outArr j)) s fun t =>
      (∀ i < wx, word t.mem D (eD + 8 * i) = word s.mem X (slot wx j + 8 * i) &&& v) ∧
      Outside D eD (8 * wx) s.mem t.mem ∧ t.gpr .rbx = off D (eD + 8 * wx) ∧
      Keep [.rax, .r14, .r12, .rsi, .rbx] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off X (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  have sj := Nat.le_trans (slot_le (w := wx) hj) hZ
  unfold outArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rsi = off X (slot wx j) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr j) (by unfold sArr; omega),
      hg.hdr.hw, hg.hdr.harr j hj]) rfl) fun s₁ ⟨⟨h12, hsi, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyMasked_ok (S := X) (eS := slot wx j) hsi ((k₁.gpr (by decide)).trans hbx) h12
    ((k₁.gpr (by decide)).trans h15) hw hw' hD
    (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact hg.scr.ld (d := slot wx j + 8 * i) (by omega))
    (fun i hi => by rw [k₁.2.2]; exact hwr i hi) hsep) fun s₂ ⟨hd₂, ho₂, k₂⟩ => ?_)
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 wx := (k₂.gpr (by decide)).trans h12
  have hbx₂ : s₂.gpr .rbx = off D eD := ((k₁.trans k₂).gpr (by decide)).trans hbx
  refine WP.mono (WP.keep [.rax, .rbx] (Q := fun t => t.gpr .rbx = off D (eD + 8 * wx) ∧ t.mem = s₂.mem)
    (by
      xrun [eightW, List.cons_append, List.nil_append, h12₂, hbx₂, eight_w _ h12₂, off_add_ofNat]
      rw [eight_w _ rfl, off_add_ofNat]; congr 2; omega) rfl) fun t ⟨⟨hbx', hm⟩, k₃⟩ => ?_
  refine ⟨fun i hi => by rw [hm, hd₂ i hi, hm₁], by rw [hm, ← hm₁]; exact ho₂, hbx',
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A word of the working space's array is outside `pre`, which nothing
of the working space overlaps. -/
theorem sep_of {B D : Addr} {Z L8 eD n o d : Nat} (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x)
    (hn : eD + n ≤ L8) (hd : o + d + 8 ≤ Z) (hZ : B.toNat + Z ≤ 2 ^ 64) :
    ∀ b < 8, ofs D (off (off B o) d + BitVec.ofNat 64 b) < eD ∨
      eD + n ≤ ofs D (off (off B o) d + BitVec.ofNat 64 b) := fun b hb => by
  have := hS (off (off B o) d + BitVec.ofNat 64 b) (by rw [off_off, ofs_off B (by omega)]; omega)
  omega

/-- `outAt sl`: into the prime's workspace (its base in slot `sl`), its
`aY` masked to `D + eD`, and back. -/
theorem outAt_ok {s : State} {B D : Addr} {Z w o wx eD L8 : Nat} {minv mx v : BitVec 64} {sl : Nat}
    (hg : Good s B Z w minv) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 ≤ Z) (hwx : 1 ≤ wx) (hwx' : wx < 2 ^ 31)
    (hsl : sl < 32) (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hbx : s.gpr .rbx = off D eD) (h15 : s.gpr .r15 = v) (hD : eD + 8 * wx ≤ L8) (hL : D.toNat + L8 ≤ 2 ^ 64)
    (hwr : (⟨D, L8⟩ : Region) ∈ s.wr) (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x) :
    WP isa (seqs (outAt sl)) s fun t =>
      (∀ i < wx, word t.mem D (eD + 8 * i) = word s.mem (off B o) (slot wx aY + 8 * i) &&& v) ∧
      Outside D eD (8 * wx) s.mem t.mem ∧ t.gpr .rbx = off D (eD + 8 * wx) ∧ t.gpr .rdi = B ∧
      t.gpr .r15 = v ∧ Keep [.rax, .r14, .r12, .rsi, .rbx, .rdi] s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have lY := slot_le (w := wx) (show aY < 8 by decide)
  unfold outAt
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [outArr]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl) fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ (off B o) (slot wx 8) wx mx :=
    ⟨(hs.congr k₁.2.2).sub (by omega) (by omega), hdi₁, by rw [hm₁]; exact hws.hdr⟩
  refine wp_seqs_append (by simp [outArr]) (by simp) ?_
  refine WP.mono (outArr_ok hg₁ (Nat.le_refl _) (show aY < 8 by decide) hwx hwx' (D := D) (eD := eD)
    ((k₁.gpr (by decide)).trans hbx) ((k₁.gpr (by decide)).trans h15) (by omega)
    (fun i hi => ⟨_, by rw [k₁.2.2]; exact hwr, Offset.contains_base D (by omega) (by omega)⟩)
    (fun i hi => sep_of hS (by omega) (by omega) hn)) fun s₂ ⟨hd₂, ho₂, hbx₂, k₂⟩ => ?_
  have hl₂ : InRegions (s₂.rd ++ s₂.wr) (off (off B o) (8 * sLink)) 8 := by
    rw [k₂.2.1, k₂.2.2]; exact hg₁.scr.ld (by unfold sLink sFn; omega)
  have hlk : word s₂.mem (off B o) (8 * sLink) = B := by
    refine Eq.trans ?_ hws.link
    rw [← hm₁]
    exact Mem.readW_congr fun b hb => ho₂ _ (by
      have := hS (off (off B o) (8 * sLink) + BitVec.ofNat 64 b) (by rw [off_off, ofs_off B (by unfold sLink sFn; omega)]; unfold sLink sFn; omega)
      omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₂.mem)
    (by xrun [Crt.leave, State.ea, hdr, (k₂.gpr (by decide)).trans hdi₁, hdrOff, hl₂, hlk]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  refine ⟨fun i hi => by rw [hm, hd₂ i hi, hm₁], by rw [hm, ← hm₁]; exact ho₂,
    by rw [k₃.gpr (by decide)]; exact hbx₂, hdi, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact h15

/-- Memory that changes only within `pre` keeps the working space. -/
theorem scr_of_outside {B D : Addr} {Z L8 e n : Nat} {m m' : Mem} (h : Outside D e n m m')
    (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x) (hn : e + n ≤ L8) : ∀ x, ofs B x < Z → m' x = m x :=
  fun x hx => h x (Or.inr (by have := hS x hx; omega))

theorem word_of_scr {B : Addr} {Z d : Nat} {m m' : Mem} (h : ∀ x, ofs B x < Z → m' x = m x)
    (hd : d + 8 ≤ Z) (hZ : B.toNat + Z ≤ 2 ^ 64) : word m' B d = word m B d :=
  Mem.readW_congr fun i hi => h _ (by rw [ofs_off B (d := d) (i := i) (by omega)]; omega)

theorem Good.of_scr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hm : ∀ x, ofs B x < Z → t.mem x = s.mem x) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = B) : Good t B Z w minv := by
  have hn := hg.scr.nowrap
  have hh : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    word_of_scr hm (by have := hdr_lt_slot w 8 hi; omega) hn
  exact ⟨hg.scr.congr hwr, hdi, ⟨ (hh _ (by decide)).trans hg.hdr.hw,
    (hh _ (by decide)).trans hg.hdr.hminv, fun j hj => (hh _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩

/-- What `out` leaves: `pre`'s four parts, each word and-ed with the mask,
the mask's low bit returned and the saved registers restored. -/
structure OutPost (t u : State) (B D : Addr) (w wp wq L8 : Nat) (op oq : Nat) (M : Bool) : Prop where
  segN : ∀ i < w, word u.mem D (8 * i) = word t.mem B (slot w aN + 8 * i) &&& mask M
  segR : ∀ i < w, word u.mem D (8 * w + 8 * i) = word t.mem B (slot w aR2 + 8 * i) &&& mask M
  segP : ∀ i < wp, word u.mem D (16 * w + 8 * i) = word t.mem (off B op) (slot wp aY + 8 * i) &&& mask M
  segQ : ∀ i < wq, word u.mem D (16 * w + 8 * wp + 8 * i) =
    word t.mem (off B oq) (slot wq aY + 8 * i) &&& mask M
  rax : u.gpr .rax = BitVec.ofNat 64 M.toNat
  saved : ∀ i < 6, u.gpr (saved.getD i .rax) = word t.mem B (8 * i)
  frame : ∀ x, L8 ≤ ofs D x → u.mem x = t.mem x
  rsp : u.gpr .rsp = t.gpr .rsp

/-- `out`, from what `r2Phase` leaves, with `pre` (`L8` bytes at `D`, apart
from the working space) in `sOut`. -/
theorem out_ok {σ t : State} {B D : Addr} {Z w pl ql L8 : Nat} {minv mp mq : BitVec 64} {N P Q : Nat}
    {M : Bool} (hR : R2Done σ t B Z w pl ql minv mp mq N P Q M) (hw : 1 ≤ w) (hw' : w < 2 ^ 20)
    (hpl : pl < 2 ^ 20) (hql : ql < 2 ^ 20)
    (hZq : offQ w pl + slot (wsWords ql) 8 + wsTab (wsWords ql) ≤ Z) (hO : word t.mem B (8 * sOut) = D)
    (hL8 : L8 = 8 * (2 * w + wsWords pl + wsWords ql)) (hL : D.toNat + L8 ≤ 2 ^ 64)
    (hwr : (⟨D, L8⟩ : Region) ∈ t.wr) (hS : ∀ x, ofs B x < Z → L8 ≤ ofs D x) :
    WP isa (seqs out) t fun u => OutPost t u B D w (wsWords pl) (wsWords ql) L8 (offP w) (offQ w pl) M := by
  have hg := hR.good
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hwp : wsWords pl < 2 ^ 20 := by unfold wsWords; omega
  have hwq : wsWords ql < 2 ^ 20 := by unfold wsWords; omega
  have hZ : slot w 8 ≤ Z := by unfold offQ at hZq; omega
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have hhiP : offP w + slot (wsWords pl) 8 ≤ Z := by unfold offQ at hZq; unfold offP; omega
  have hhiQ : offQ w pl + slot (wsWords ql) 8 ≤ Z := by omega
  have hloQ : slot w 8 ≤ offQ w pl := by unfold offQ; omega
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold out
  simp only [List.append_assoc]
  -- `rbx := pre`, `r15 := ` the mask.
  refine wp_seqs_append (by simp) (by simp [outArr]) ?_
  refine WP.mono (WP.keep [.rbx, .r15] (Q := fun u => u.gpr .rbx = off D 0 ∧ u.gpr .r15 = mask M ∧ u.mem = t.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sOut (by decide), hl sMask (by decide), hO, hR.msk]) rfl)
    fun s₀ ⟨⟨hbx₀, h15₀, hm₀⟩, k₀⟩ => ?_
  have hg₀ : Good s₀ B Z w minv := Good.of_scr hg hZ (fun x _ => by rw [hm₀]) k₀.2.2 ((k₀.gpr (by decide)).trans hg.rdi)
  have hwr₀ : (⟨D, L8⟩ : Region) ∈ s₀.wr := by rw [k₀.2.2]; exact hwr
  -- `n`.
  refine wp_seqs_append (by simp [outArr]) (by simp [outArr]) ?_
  refine WP.mono (outArr_ok hg₀ hZ (show aN < 8 by decide) hw (by omega) hbx₀ h15₀ (by omega)
    (fun i hi => ⟨_, hwr₀, Offset.contains_base D (by omega) (by omega)⟩)
    (fun i hi => by
      have := slot_le (w := w) (show aN < 8 by decide)
      have := sep_of (o := 0) (d := slot w aN + 8 * i) hS (eD := 0) (n := 8 * w) (by omega) (by omega) hn
      simpa [off_off] using this)) fun s₁ ⟨hd₁, ho₁, hbx₁, k₁⟩ => ?_
  have hsc₁ := scr_of_outside ho₁ hS (by omega)
  have hg₁ := Good.of_scr hg₀ hZ hsc₁ k₁.2.2 ((k₁.gpr (by decide)).trans hg₀.rdi)
  have hwr₁ : (⟨D, L8⟩ : Region) ∈ s₁.wr := by rw [k₁.2.2]; exact hwr₀
  have h15₁ : s₁.gpr .r15 = mask M := (k₁.gpr (by decide)).trans h15₀
  -- `R² mod n`.
  refine wp_seqs_append (by simp [outArr]) (by simp [outAt]) ?_
  refine WP.mono (outArr_ok hg₁ hZ (show aR2 < 8 by decide) hw (by omega) (eD := 0 + 8 * w) hbx₁ h15₁ (by omega)
    (fun i hi => ⟨_, hwr₁, Offset.contains_base D (by omega) (by omega)⟩)
    (fun i hi => by
      have := slot_le (w := w) (show aR2 < 8 by decide)
      have := sep_of (o := 0) (d := slot w aR2 + 8 * i) hS (eD := 0 + 8 * w) (n := 8 * w) (by omega) (by omega) hn
      simpa [off_off] using this)) fun s₂ ⟨hd₂, ho₂, hbx₂, k₂⟩ => ?_
  have hsc₂ := scr_of_outside ho₂ hS (by omega)
  have hg₂ := Good.of_scr hg₁ hZ hsc₂ k₂.2.2 ((k₂.gpr (by decide)).trans hg₁.rdi)
  have hwr₂ : (⟨D, L8⟩ : Region) ∈ s₂.wr := by rw [k₂.2.2]; exact hwr₁
  have h15₂ : s₂.gpr .r15 = mask M := (k₂.gpr (by decide)).trans h15₁
  have hsc02 : ∀ x, ofs B x < Z → s₂.mem x = t.mem x := fun x hx => by rw [hsc₂ x hx, hsc₁ x hx, hm₀]
  have hwd : ∀ d, d + 8 ≤ Z → word s₂.mem B d = word t.mem B d := fun d hd => word_of_scr hsc02 hd hn
  -- `R_p² mod p`.
  refine wp_seqs_append (by simp [outAt]) (by simp [outAt]) ?_
  refine WP.mono (outAt_ok hg₂ (Nat.le_refl _) hhiP (by omega) (by omega) (by decide)
    (by rw [hwd _ (by unfold sWsP sFn; omega)]; exact hR.wsP)
    (hR.pws.of_words fun i hi => by rw [word_off, word_off]; exact hwd _ (by unfold offP; omega))
    (eD := 0 + 8 * w + 8 * w) (by rw [hbx₂]) h15₂ (by omega) hL hwr₂ hS) fun s₃ ⟨hd₃, ho₃, hbx₃, hdi₃, h15₃, k₃⟩ => ?_
  have hsc₃ := scr_of_outside ho₃ hS (by omega)
  have hg₃ := Good.of_scr hg₂ hZ hsc₃ k₃.2.2 hdi₃
  have hwr₃ : (⟨D, L8⟩ : Region) ∈ s₃.wr := by rw [k₃.2.2]; exact hwr₂
  have hsc03 : ∀ x, ofs B x < Z → s₃.mem x = t.mem x := fun x hx => by rw [hsc₃ x hx, hsc02 x hx]
  have hwd₃ : ∀ d, d + 8 ≤ Z → word s₃.mem B d = word t.mem B d := fun d hd => word_of_scr hsc03 hd hn
  -- `R_q² mod q`.
  refine wp_seqs_append (by simp [outAt]) (by simp) ?_
  refine WP.mono (outAt_ok hg₃ hloQ hhiQ (by omega) (by omega) (by decide)
    (by rw [hwd₃ _ (by unfold sWsQ sFn; omega)]; exact hR.wsQ)
    (hR.qws.of_words fun i hi => by rw [word_off, word_off]; exact hwd₃ _ (by omega))
    (eD := 0 + 8 * w + 8 * w + 8 * wsWords pl) (by rw [hbx₃]) h15₃ (by omega) hL hwr₃ hS)
    fun s₄ ⟨hd₄, ho₄, _, hdi₄, _, k₄⟩ => ?_
  have hsc₄ := scr_of_outside ho₄ hS (by omega)
  have hsc04 : ∀ x, ofs B x < Z → s₄.mem x = t.mem x := fun x hx => by rw [hsc₄ x hx, hsc03 x hx]
  have hwd₄ : ∀ d, d + 8 ≤ Z → word s₄.mem B d = word t.mem B d := fun d hd => word_of_scr hsc04 hd hn
  have hl₄ : ∀ i < 32, InRegions (s₄.rd ++ s₄.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k₄.2.1, k₄.2.2, k₃.2.1, k₃.2.2, k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2, k₀.2.1, k₀.2.2]; exact hl i hi
  -- The result and the saved registers.
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun u =>
      u.gpr .rax = BitVec.ofNat 64 M.toNat ∧ u.gpr .rbx = word t.mem B (8 * 0) ∧
      u.gpr .rbp = word t.mem B (8 * 1) ∧ u.gpr .r12 = word t.mem B (8 * 2) ∧
      u.gpr .r13 = word t.mem B (8 * 3) ∧ u.gpr .r14 = word t.mem B (8 * 4) ∧
      u.gpr .r15 = word t.mem B (8 * 5) ∧ u.mem = s₄.mem) (by
    xrun [exit_eq, List.cons_append, List.nil_append, State.ea, hdr, hdi₄, hdrOff, hl₄ sMask (by decide),
      hwd₄ (8 * sMask) (by unfold sMask sFn; omega), hR.msk, mask_and1, hl₄ 0 (by decide), hl₄ 1 (by decide),
      hl₄ 2 (by decide), hl₄ 3 (by decide), hl₄ 4 (by decide), hl₄ 5 (by decide), hwd₄ (8 * 0) (by omega),
      hwd₄ (8 * 1) (by omega), hwd₄ (8 * 2) (by omega), hwd₄ (8 * 3) (by omega), hwd₄ (8 * 4) (by omega),
      hwd₄ (8 * 5) (by omega)]) rfl)
    fun u ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₅⟩ => ?_
  -- Each part of `pre`, kept by the later copies.
  have o12 := ho₂
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hax, fun i hi => ?_, fun x hx => ?_, ?_⟩
  · rw [hm, ho₄.word (by omega) (by omega), ho₃.word (by omega) (by omega), ho₂.word (by omega) (by omega),
      show 8 * i = 0 + 8 * i by omega, hd₁ i hi, hm₀, Nat.zero_add]
  · rw [hm, ho₄.word (by omega) (by omega), ho₃.word (by omega) (by omega),
      show 8 * w + 8 * i = 0 + 8 * w + 8 * i by omega, hd₂ i hi, word_of_scr (fun x hx => by rw [hsc₁ x hx, hm₀])
        (by have := slot_le (w := w) (show aR2 < 8 by decide); omega) hn]
  · rw [hm, ho₄.word (by omega) (by omega), show 16 * w + 8 * i = 0 + 8 * w + 8 * w + 8 * i by omega, hd₃ i hi,
      word_off, word_off, hwd _ (by have := slot_le (w := wsWords pl) (show aY < 8 by decide); have := hhiP; simp only [offP] at *; omega)]
    rfl
  · rw [hm, show 16 * w + 8 * wsWords pl + 8 * i = 0 + 8 * w + 8 * w + 8 * wsWords pl + 8 * i by omega, hd₄ i hi,
      word_off, word_off, hwd₃ _ (by have := slot_le (w := wsWords ql) (show aY < 8 by decide); omega)]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · rw [hm, ho₄ x (Or.inr (by omega)), ho₃ x (Or.inr (by omega)), ho₂ x (Or.inr (by omega)),
      ho₁ x (Or.inr (by omega)), hm₀]
  · have kk := (((k₀.trans k₁).trans k₂).trans k₃).trans (k₄.trans k₅)
    exact kk.gpr (by decide)

end VG.Proof.Bignum.X86_64.PrivPre
