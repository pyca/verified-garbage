module

public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
import VerifiedGarbage.Proof.Dsa.AArch64.SharedStore
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # One digit of the shared exponentiation: a bucket times the base's power

The secret digit's bucket is read by the scan of every entry and written
back under a mask; the public digit's is read and written directly. Each
lemma says which bucket becomes its product with `[aXc]`, and that the
other buckets, the arrays and the header's slots are as they were. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower

/-! ## What each kind of change keeps -/

/-- The header's slots through a selection. -/
theorem sel_hdr {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (selRanges wx) m m') {k : Nat} (hk : k < 32)
    (h1 : k ≠ Crt.sEnt) (h2 : k ≠ Crt.sJ) : word m' P (8 * k) = word m P (8 * k) :=
  hf.word_eq (fun r hr => by
    have := hdr_lt_slot wx Crt.aT hk
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only; omega_arith
    · simp only [Crt.sEnt, sFn] at h1 ⊢; omega_arith
    · simp only [Crt.sJ, sFn] at h2 ⊢; omega_arith) (by omega_arith)

/-- The table's entries through a window's changes. -/
theorem win_ent {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (crtWinRanges wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  hf.wv_eq (fun r hr => by have := crtWinRanges_ent wx j r hr; omega_arith)
    (by have := ent_le wx hj; omega_arith)

/-- An array a window does not use, through its changes. -/
theorem win_arr {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (crtWinRanges wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp)
    (h3 : j ≠ aY) (h4 : j ≠ Crt.aT) : wv m' P (slot wx j) wx = wv m P (slot wx j) wx :=
  hf.wv_eq (fun r hr => by
    have := crtExpRanges_arr wx hj h1 h2 h3 h4 16 r (crtWinRanges_sub wx r hr); omega_arith)
    (by have := slot_le (w := wx) hj; omega_arith)

/-- The table's entries through changes to arrays. -/
theorem arr_ent {m m' : Mem} {P : Addr} {wx : Nat} {js : List Nat} (hf : Arrays P wx js m m')
    (hjs : ∀ a ∈ js, a < 8) (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  hf.wv_eq (fun a ha => Or.inr (by
    have := slot_le (w := wx) (hjs a ha)
    have := slot_mono wx (show 8 ≤ 8 + j by omega_arith)
    omega_arith)) (by have := ent_le wx hj; omega_arith)

/-- Another entry through a store to one. -/
theorem ent_ent {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) (hjv : j ≠ v) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  hf.wv (by have := slot_sep (w := wx) (show 8 + j ≠ 8 + v by omega_arith); omega_arith)
    (by have := ent_le wx hj; omega_arith)

/-- An array through a store to an entry. -/
theorem ent_arr {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 8) :
    wv m' P (slot wx j) wx = wv m P (slot wx j) wx :=
  hf.wv (Or.inl (by
    have := slot_le (w := wx) hj
    have := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
    omega_arith)) (by have := slot_le (w := wx) hj; omega_arith)

/-- A header slot through a store to an entry. -/
theorem ent_hdr {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    {k : Nat} (hk : k < 32) : word m' P (8 * k) = word m P (8 * k) :=
  hf.word (Or.inl (hdr_lt_slot wx (8 + v) hk)) (by omega_arith)

/-- A store to an entry is within the workspace's mutable region. -/
theorem ent_work {m m' : Mem} {P : Addr} {wx v : Nat} (hf : Outside P (slot wx (8 + v)) (8 * wx) m m')
    (hv : v < 16) : Frm P (workRanges wx) m m' := by
  intro x hx
  apply hf x
  obtain h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  have := ent_le wx hv
  have := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  omega_arith

/-- A window's changes are within the workspace's mutable region. -/
theorem win_work {m m' : Mem} {P : Addr} {wx : Nat} (hf : Frm P (crtWinRanges wx) m m') :
    Frm P (workRanges wx) m m' := by
  intro x hx
  apply hf x
  intro r hr
  obtain ho := crtWinRanges_ok wx r hr
  obtain h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  omega_arith

/-- A store to one of the header's slots for the functions' own use. -/
theorem fn_outside (m : Mem) (P : Addr) {i : Nat} (v : BitVec 64) (hi : 17 ≤ i) (hi' : i < 32) :
    Outside P 136 120 m (m.writeW (off P (8 * i)) v) :=
  (writeW_outside m P v (by omega_arith)).mono (by omega_arith) (by omega_arith)

/-- The context through changes to the header's slots for the functions' own use. -/
theorem ctx_of_fn {s t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (ho : Outside P 136 120 s.mem t.mem) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : CExpCtx t P wx minv N Xc := by
  have hn := hc.scrT.nowrap
  obtain h256 : 256 ≤ slot wx 0 := by unfold slot hdrBytes; omega_arith
  obtain hh : ∀ i < 17, word t.mem P (8 * i) = word s.mem P (8 * i) := fun i hi =>
    ho.word (Or.inl (by omega_arith)) (by omega_arith)
  obtain ha : ∀ j < 8, wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx := fun j hj =>
    ho.wv (Or.inr (by have := slot_mono wx (show 0 ≤ j by omega_arith); omega_arith))
      (by have := slot_le (w := wx) hj; omega_arith)
  exact ⟨⟨hc.good.scr.congr hwr, h0.trans hc.good.x0,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩, hc.scrT.congr hwr,
    (ha _ (by decide)).trans hc.n,
    by rw [ho.word (Or.inr (by have := slot_mono wx (show 0 ≤ aN by decide); omega_arith))
      (by have := slot_le (w := wx) (show aN < 8 by decide); omega_arith)]; exact hc.inv,
    (ha _ (by decide)).trans hc.x⟩

/-- The table's entries through changes to those slots. -/
theorem fn_ent {m m' : Mem} {P : Addr} {wx : Nat} (ho : Outside P 136 120 m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 16) :
    wv m' P (slot wx (8 + j)) wx = wv m P (slot wx (8 + j)) wx :=
  ho.wv (Or.inr (by
    have : 256 ≤ slot wx 0 := by unfold slot hdrBytes; omega_arith
    have := slot_mono wx (show 0 ≤ 8 + j by omega_arith)
    omega_arith)) (by have := ent_le wx hj; omega_arith)

/-- An array through changes to those slots. -/
theorem fn_arr {m m' : Mem} {P : Addr} {wx : Nat} (ho : Outside P 136 120 m m')
    (hn : P.toNat + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64) {j : Nat} (hj : j < 8) :
    wv m' P (slot wx j) wx = wv m P (slot wx j) wx :=
  ho.wv (Or.inr (by
    have : 256 ≤ slot wx 0 := by unfold slot hdrBytes; omega_arith
    have := slot_mono wx (show 0 ≤ j by omega_arith)
    omega_arith)) (by have := slot_le (w := wx) hj; omega_arith)

/-- Changes to those slots are within the workspace's mutable region. -/
theorem fn_work {m m' : Mem} {P : Addr} {wx : Nat} (ho : Outside P 136 120 m m') :
    Frm P (workRanges wx) m m' := by
  intro x hx
  apply ho x
  obtain h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  omega_arith

/-! ## The secret digit's bucket -/

theorem secretDigit_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc V : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) :
    WP isa (.block secretDigit) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (V % 8)) ∧ Keep [.x3, .x4] s t := by
  refine WP.keep [.x3, .x4] ?_ rfl rfl rfl
  brun [secretDigit, hc.good.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
    hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sNib) (by decide), hV]
  exact congrArg (s.mem.writeW _) (BlockedRedc.mask7_ofNat hV')

/-- The secret digit `V mod 8`'s bucket becomes its product with `[aXc]`:
by the scan of every entry, the multiplication and the masked store. -/
theorem secretBucket_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc V : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64)
    (hA : Xc < N) :
    WP isa (seqs [.block secretDigit, Crt.select, M.mm Crt.aT Crt.aT Crt.aXc, store]) s fun t =>
      CExpCtx t P wx minv N Xc ∧ wv t.mem P (slot wx (8 + V % 8)) wx < N ∧
      wv t.mem P (slot wx (8 + V % 8)) wx * 2 ^ (64 * wx) % N =
        wv s.mem P (slot wx (8 + V % 8)) wx * Xc % N ∧
      (∀ j < 16, j ≠ V % 8 → wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  obtain hv8 : V % 8 < 8 := Nat.mod_lt _ (by decide)
  obtain hv16 : V % 8 < 16 := by omega_using [hv8]
  simp only [seqs]
  refine WP.seq (WP.mono (secretDigit_ok hc hV hV') fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain o₁ := writeW_outside s.mem P (d := 8 * Crt.sNib) (BitVec.ofNat 64 (V % 8)) (by decide)
  rw [← hm₁] at o₁
  obtain f₁ : Frm P (crtWinRanges wx) s.mem s₁.mem := Frm.of_outside o₁ (by simp [crtWinRanges])
  obtain hc₁ := hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide))
  obtain hh₁ : ∀ k < 32, k ≠ Crt.sNib → word s₁.mem P (8 * k) = word s.mem P (8 * k) := fun k hk h => by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h)]
  refine WP.seq (WP.mono (WindowVector.select_ok (Or.inl rfl)
    (fun hu tab nib => tabSel_ok hu (by omega_using [hw]) hw' hv16 tab nib) hc₁ hw' hv16
    (by rw [hh₁ _ (by decide) (by decide)]; exact ht) (by rw [hm₁, word_writeW_self]))
    fun s₂ ⟨hc₂, hT₂, f₂, k₂⟩ => ?_)
  obtain f₂' : Frm P (crtWinRanges wx) s₁.mem s₂.mem := f₂.mono (selRanges_sub wx)
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc₂.good (Nat.le_refl _)
    (by omega_using [hw]) (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc₂.inv (by rw [hc₂.n, hc₂.x]; exact hA)) fun s₃ ⟨_, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [hc₂.n] at hlt₃ hm₃
  obtain f₃ : Frm P (crtWinRanges wx) s₂.mem s₃.mem := Frm.of_arrays ha₃ (by simp [crtWinRanges])
  obtain hc₃ := hc₂.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide))
  obtain tab₃ : word s₃.mem P (8 * Crt.sTab) = off P (slot wx 8) := by
    rw [ha₃.hslot (by decide), sel_hdr f₂ (by decide) (by decide) (by decide), hh₁ _ (by decide) (by decide)]
    exact ht
  obtain nib₃ : word s₃.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (V % 8) := by
    rw [ha₃.hslot (by decide), sel_hdr f₂ (by decide) (by decide) (by decide), hm₁, word_writeW_self]
  refine WP.mono (store_ok hc₃ hw hw' hd hv8 tab₃ nib₃) fun t ⟨hct, hE, o₄, k₄⟩ => ?_
  obtain f03 : Frm P (crtWinRanges wx) s.mem s₃.mem := (f₁.trans f₂').trans f₃
  refine ⟨hct, by rw [hE]; exact hlt₃, ?_, fun j hj hjv => ?_, fun j hj h1 h2 h3 h4 => ?_,
    fun k hk h1 h2 h3 => ?_, (win_work f03).trans (ent_work o₄ hv16),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [hE, hm₃, hT₂, hc₂.x, win_ent f₁ hn hv16]
  · rw [ent_ent o₄ hn hj hjv, win_ent f03 hn hj]
  · rw [ent_arr o₄ hn hj, win_arr f03 hn hj h1 h2 h3 h4]
  · rw [ent_hdr o₄ hk, ha₃.hslot hk, sel_hdr f₂ hk h2 h3, hh₁ k hk h1]

/-! ## The public digit's bucket -/

/-- `T_v := [aT]` for the public `v` in `sNib`. -/
theorem put_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc v : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa put s fun t => CExpCtx t P wx minv N Xc ∧
      wv t.mem P (slot wx (8 + v)) wx = wv s.mem P (slot wx Crt.aT) wx ∧
      Outside P (slot wx (8 + v)) (8 * wx) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  obtain hE := ent_le wx hv
  obtain hE0 := slot_mono wx (show 8 ≤ 8 + v by omega_arith)
  have hz := hc.scrT.nowrap
  unfold put
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (PublicPower.selectHead_ok hc hw' hv ht hn) fun u ⟨⟨h12, h16, h17, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun a => a.gpr .x16 = u.gpr .x17 ∧
    a.gpr .x17 = u.gpr .x16 ∧ a.mem = u.mem) (by brun []) rfl rfl rfl) fun a ⟨⟨a16, a17, am⟩, ka⟩ => ?_
  obtain hs := hc.scrT.congr (hk.trans ka).wr
  refine WP.mono (copyWords_ok (S := P) (D := P) (eS := slot wx Crt.aT) (eD := slot wx (8 + v))
    (a16.trans h17) (a17.trans h16) ((ka.gpr .x12 (by decide)).trans h12) (by omega_using [hw])
    (by omega_using [hw']) (by omega_using [hE, hz])
    (fun i hi => hs.ld (by omega_using [hT, hi])) (fun i hi => hs.st (by omega_using [hE, hi]))
    (fun i hi b hb => by rw [ofs_off P (by omega_using [hT, hz, hi, hb])]; omega_using [hT, hE0, hi, hb]))
    fun t ⟨hval, _, hf, _, _, hkt⟩ => ?_
  rw [am, hm] at hf hval
  obtain k := ((hk.trans ka).trans hkt).mono (rs' := mmRegs) (by decide)
  exact ⟨hc.of_frm (Frm.of_outside (hf.mono (o' := slot wx 8) (n' := tabBytes wx) hE0 (by omega_using [hE]))
    (by simp [crtExpRanges])) k.wr (k.gpr .x0 (by decide)), hval, hf, k⟩

theorem publicDigit_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc Q : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64) :
    WP isa (.block publicDigit) s fun t =>
      (t.gpr .x3 = BitVec.ofNat 64 (Q % 8) ∧ t.mem = s.mem) ∧ Keep [.x3, .x4] s t := by
  refine WP.keep [.x3, .x4] ?_ rfl rfl rfl
  brun [publicDigit, hc.good.x0, hdr_enc (show Crt.sMaskX < 32 by decide), hc.ld (i := Crt.sMaskX) (by decide), hQ]
  exact BlockedRedc.mask7_ofNat hQ'

/-- The public digit `d`'s bucket, entry `8 + d`, becomes its product with
`[aXc]`, read and written directly. -/
theorem publicBucket_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc d : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hd : d < 8)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8)) (h3 : s.gpr .x3 = BitVec.ofNat 64 d)
    (hA : Xc < N) :
    WP isa (publicBucket M.mm) s fun t =>
      CExpCtx t P wx minv N Xc ∧ wv t.mem P (slot wx (8 + (8 + d))) wx < N ∧
      wv t.mem P (slot wx (8 + (8 + d))) wx * 2 ^ (64 * wx) % N =
        wv s.mem P (slot wx (8 + (8 + d))) wx * Xc % N ∧
      (∀ j < 16, j ≠ 8 + d → wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  obtain hv16 : 8 + d < 16 := by omega_using [hd]
  obtain hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  unfold publicBucket
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off P (8 * Crt.sNib))
      (BitVec.ofNat 64 (8 + d))) (by
    brun [hc.good.x0, hdr_enc (show Crt.sNib < 32 by decide), hc.st (i := Crt.sNib) (by decide), h3,
      ofNat_add_ofNat]
    rw [Nat.add_comm]) rfl rfl rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_)
  obtain o₁ := writeW_outside s.mem P (d := 8 * Crt.sNib) (BitVec.ofNat 64 (8 + d)) (by decide)
  rw [← hm₁] at o₁
  obtain f₁ : Frm P (crtWinRanges wx) s.mem s₁.mem := Frm.of_outside o₁ (by simp [crtWinRanges])
  obtain hc₁ := hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide))
  obtain hh₁ : ∀ k < 32, k ≠ Crt.sNib → word s₁.mem P (8 * k) = word s.mem P (8 * k) := fun k hk h => by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h)]
  refine WP.seq (WP.mono (PublicPower.select_ok hc₁ hw hw' hv16
    (by rw [hh₁ _ (by decide) (by decide)]; exact ht) (by rw [hm₁, word_writeW_self]))
    fun s₂ ⟨hc₂, hT₂, o₂, k₂⟩ => ?_)
  obtain f₂ : Frm P (crtWinRanges wx) s₁.mem s₂.mem :=
    Frm.of_outside (o₂.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (by omega_arith) (by omega_arith))
      (by simp [crtWinRanges])
  obtain hh₂ : ∀ k < 32, word s₂.mem P (8 * k) = word s₁.mem P (8 * k) := fun k hk =>
    o₂.word (Or.inl (hdr_lt_slot wx Crt.aT hk)) (by omega_arith)
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc₂.good (Nat.le_refl _)
    hw (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc₂.inv (by rw [hc₂.n, hc₂.x]; exact hA)) fun s₃ ⟨_, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [hc₂.n] at hlt₃ hm₃
  obtain f₃ : Frm P (crtWinRanges wx) s₂.mem s₃.mem := Frm.of_arrays ha₃ (by simp [crtWinRanges])
  obtain hc₃ := hc₂.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide))
  obtain tab₃ : word s₃.mem P (8 * Crt.sTab) = off P (slot wx 8) := by
    rw [ha₃.hslot (by decide), hh₂ _ (by decide), hh₁ _ (by decide) (by decide)]
    exact ht
  obtain nib₃ : word s₃.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (8 + d) := by
    rw [ha₃.hslot (by decide), hh₂ _ (by decide), hm₁, word_writeW_self]
  refine WP.mono (put_ok hc₃ hw hw' hv16 tab₃ nib₃) fun t ⟨hct, hE, o₄, k₄⟩ => ?_
  obtain f03 : Frm P (crtWinRanges wx) s.mem s₃.mem := (f₁.trans f₂).trans f₃
  refine ⟨hct, by rw [hE]; exact hlt₃, ?_, fun j hj hjv => ?_, fun j hj h1 h2 h3 h4 => ?_,
    fun k hk h1 _ _ => ?_, (win_work f03).trans (ent_work o₄ hv16),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [hE, hm₃, hT₂, hc₂.x, win_ent f₁ hn hv16]
  · rw [ent_ent o₄ hn hj hjv, win_ent f03 hn hj]
  · rw [ent_arr o₄ hn hj, win_arr f03 hn hj h1 h2 h3 h4]
  · rw [ent_hdr o₄ hk, ha₃.hslot hk, hh₂ k hk, hh₁ k hk h1]

/-- The public digit `Q mod 8`: its bucket becomes its product with `[aXc]`
unless it is zero, when nothing changes. -/
theorem publicHalf_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc Q : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64) (hA : Xc < N) :
    WP isa (seqs [.block publicDigit, .ite (.zero .x .x3) (.block []) (publicBucket M.mm)]) s fun t =>
      CExpCtx t P wx minv N Xc ∧
      (Q % 8 ≠ 0 → wv t.mem P (slot wx (8 + (8 + Q % 8))) wx < N ∧
        wv t.mem P (slot wx (8 + (8 + Q % 8))) wx * 2 ^ (64 * wx) % N =
          wv s.mem P (slot wx (8 + (8 + Q % 8))) wx * Xc % N) ∧
      (∀ j < 16, j ≠ 8 + Q % 8 ∨ Q % 8 = 0 →
        wv t.mem P (slot wx (8 + j)) wx = wv s.mem P (slot wx (8 + j)) wx) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain hd8 : Q % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (publicDigit_ok hc hQ hQ') fun u ⟨⟨h3, hm⟩, hk⟩ => ?_)
  obtain hf : Frm P (crtWinRanges wx) s.mem u.mem := hm ▸ Frm.refl _ _ _
  obtain hu := hc.of_win hf hk.wr (hk.gpr .x0 (by decide))
  obtain hz := PublicPower.eval_zero_x3 h3 (show Q % 8 < 2 ^ 64 by omega_arith)
  by_cases hzero : Q % 8 = 0
  · refine WP.ite true (by rw [hz, hzero]; rfl) (fun _ => WP.block_nil ?_) (by simp)
    exact ⟨hu, fun h => absurd hzero h, fun _ _ _ => by rw [hm], fun _ _ _ _ _ _ => by rw [hm],
      fun _ _ _ _ _ => by rw [hm], win_work hf, hk.mono (by decide)⟩
  · refine WP.ite false (by rw [hz]; simp [hzero]) (by simp) (fun _ => ?_)
    refine WP.mono (publicBucket_ok M hu hw hw' hd8 (hm ▸ ht) h3 hA)
      fun t ⟨hct, hlt, hval, hoth, harr, hhdr, hfrm, hkt⟩ => ?_
    rw [hm] at hval hoth harr hhdr hfrm
    exact ⟨hct, fun _ => ⟨hlt, hval⟩, fun j hj h => hoth j hj (h.resolve_right hzero), harr, hhdr,
      hfrm, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.SharedPower
