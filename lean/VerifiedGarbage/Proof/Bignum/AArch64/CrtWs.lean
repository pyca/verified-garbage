import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

/-!
# RSA with the CRT on AArch64: the primes' workspaces

`wsEnd` finds the end of a workspace (`wsEnd_ok`), `wsNew` lays out a new
one there for `max(2, ⌈len / 8⌉)` words, linked back to the modulus'
(`wsNew_ok`), and `loadArr` loads bytes outside the working space into an
array of a prime's workspace (`primeLoad_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A left shift of a small number. -/
theorem shl_ofNat {n k : Nat} (h : n * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · decide
      · exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right n (Nat.two_pow_pos k)) h),
    Nat.mod_eq_of_lt h]

/-- A right shift of a number. -/
theorem shr_ofNat {n k : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

/-- `x4 := ` the end of the workspace at `x5 = X`, `x6 := 8 (w_X + 2)`. -/
theorem wsEnd_ok {s : State} {X : Addr} {Z wx : Nat} (hs : Scr s X Z) (h5 : s.gpr .x5 = X)
    (hw : word s.mem X (8 * sW) = BitVec.ofNat 64 wx) (hwx : wx < 2 ^ 30)
    (ha : word s.mem X (8 * sArr Public.aOne) = off X (slot wx Public.aOne)) (hZ : slot wx 8 ≤ Z) :
    WP isa (.block wsEnd) s fun t => (t.gpr .x4 = off X (slot wx 8) ∧
      t.gpr .x6 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ t.mem = s.mem) ∧ Keep [.x4, .x6] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off X (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot wx 8 hi; omega)
  refine WP.keep [.x4, .x6] ?_ (by decide) (by decide) (by decide +kernel)
  unfold wsEnd
  brun [ldw, h5, hdr_enc (sArr_lt (show Public.aOne < 8 by decide)), hdr_enc (show sW < 32 by decide),
    hl _ (sArr_lt (show Public.aOne < 8 by decide)), ha, hl sW (by decide), hw, ofNat_add_ofNat,
    shl_ofNat (show (wx + 2) * 2 ^ 3 < 2 ^ 64 by omega)]
  refine ⟨?_, by rw [Nat.mul_comm]; rfl⟩
  refine congrArg (off X) ?_
  rw [show (2 : Nat) ^ 3 = 8 from rfl]
  unfold slot Public.aOne; omega

/-- `x4 := ` the end of a prime's workspace at `x5 = X`, past its table. -/
theorem wsEndT_ok {s : State} {X : Addr} {Z wx : Nat} (hs : Scr s X Z) (h5 : s.gpr .x5 = X)
    (hw : word s.mem X (8 * sW) = BitVec.ofNat 64 wx) (hwx : wx < 2 ^ 30)
    (ha : word s.mem X (8 * sArr Public.aOne) = off X (slot wx Public.aOne)) (hZ : slot wx 8 ≤ Z) :
    WP isa (.block wsEndT) s fun t => (t.gpr .x4 = off X (slot wx 8 + tabBytes wx) ∧ t.mem = s.mem) ∧
      Keep [.x4, .x6] s t := by
  unfold wsEndT
  rw [WP.block_append_iff]
  refine WP.mono (wsEnd_ok hs h5 hw hwx ha hZ) fun t₁ ⟨⟨h4, h6, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x4, .x6] (Q := fun t => t.gpr .x4 = off X (slot wx 8 + tabBytes wx) ∧ t.mem = t₁.mem)
    (by brun [h4, h6, shl_ofNat (show 8 * (wx + 2) * 2 ^ 4 < 2 ^ 64 by omega)]; refine congrArg (off X) ?_
        rw [show (2 : Nat) ^ 4 = 16 from rfl]; unfold tabBytes; omega)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h4', hm⟩, k⟩ =>
      ⟨⟨h4', hm.trans hm₁⟩, (k₁.trans k).mono (by decide)⟩

/-- `subs` and `csel` of a number and 2: the larger. -/
theorem csel_max2 {a : Nat} (ha : a < 2 ^ 64) :
    (if decide (2 ^ 64 ≤ (BitVec.ofNat 64 a).toNat + (~~~BitVec.setWidth 64 (2#16)).toNat + (true).toNat) = true
      then BitVec.ofNat 64 a else BitVec.setWidth 64 (2#16)) = BitVec.ofNat 64 (max 2 a) := by
  have e : (~~~BitVec.setWidth 64 (2#16)).toNat = 2 ^ 64 - 3 := by decide
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Bool.toNat_true,
    show BitVec.setWidth 64 (2#16) = BitVec.ofNat 64 2 by decide]
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> congr 1 <;> omega

/-- A new workspace at `off B o` for a number of the length in slot
`slotLen`: its base into slot `slotWs`, its link, `w_X` and the bases of
its arrays. -/
theorem wsNew_ok {s : State} {B : Addr} {Z o len : Nat} {slotWs slotLen : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h4 : s.gpr .x4 = off B o) (hws : slotWs < 32) (hsl : slotLen < 32)
    (hne : slotWs ≠ slotLen) (hlen : word s.mem B (8 * slotLen) = BitVec.ofNat 64 len) (hlen' : len < 2 ^ 32)
    (ho : 8 * 32 ≤ o) (hZ : o + slot (wsWords len) 8 ≤ Z) :
    WP isa (.block (wsNew slotWs slotLen)) s fun t =>
      word t.mem B (8 * slotWs) = off B o ∧ word t.mem (off B o) (8 * sLink) = B ∧
      word t.mem (off B o) (8 * sW) = BitVec.ofNat 64 (wsWords len) ∧
      (∀ j < 8, word t.mem (off B o) (8 * sArr j) = off (off B o) (slot (wsWords len) j)) ∧
      t.gpr .x0 = B ∧ Frm B [(8 * slotWs, 8), (o, 8 * 17)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h256 : 256 ≤ slot (wsWords len) 8 := by unfold slot hdrBytes; omega
  have hs' : Scr s (off B o) (slot (wsWords len) 8) := hs.sub hZ (by omega)
  have hX : ∀ v : BitVec 64, (s.mem.writeW (off B (8 * slotWs)) v).readW (off B (8 * slotLen)) 64 =
      BitVec.ofNat 64 len := fun v => (hdrStore_hdr s.mem B v hws hsl hne).trans hlen
  have hst : ∀ i < 32, InRegions s.wr (off B (o + 8 * i)) 8 := fun i hi =>
    hs.st (by have := hdr_lt_slot (wsWords len) 8 hi; omega)
  unfold wsNew
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x0, .x1, .x5, .x6, .x12] (Q := fun t => t.gpr .x0 = off B o ∧ t.gpr .x1 = B ∧
      t.gpr .x12 = BitVec.ofNat 64 (wsWords len) ∧
      t.mem = ((s.mem.writeW (off B (8 * slotWs)) (off B o)).writeW (off (off B o) (8 * sLink)) B).writeW
        (off (off B o) (8 * sW)) (BitVec.ofNat 64 (wsWords len)))
    (by brun [h0, h4, hdr_enc hws, hdr_enc hsl, hdr_enc (show sLink < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs.st (d := 8 * slotWs) (by omega), hs.ld (d := 8 * slotLen) (by omega), hX, ofNat_add_ofNat,
      shr_ofNat (show len + 7 < 2 ^ 64 by omega), csel_max2 (show (len + 7) / 2 ^ 3 < 2 ^ 64 by omega),
      hst sLink (by decide), hst sW (by decide), off_off]; unfold wsWords; exact ⟨rfl, rfl⟩) rfl rfl rfl)
    fun t₃ ⟨⟨h0₃, h1₃, h12₃, hm₃⟩, k₃⟩ => ?_
  have hs₃' := hs'.congr k₃.wr
  refine WP.mono (setBases_ok hs₃' h0₃ h12₃ (by unfold sArr; omega)) fun t₄ ⟨harr₄, ho₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = t₄.mem)
    (by brun [(k₄.gpr .x1 (by decide)).trans h1₃]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h0', hm'⟩, k'⟩ => ?_
  have o1 := writeW_outside s.mem B (d := 8 * slotWs) (off B o) (by omega)
  have o2 := writeW_outside (s.mem.writeW (off B (8 * slotWs)) (off B o)) (off B o) (d := 8 * sLink) B (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off B (8 * slotWs)) (off B o)).writeW (off (off B o) (8 * sLink)) B)
    (off B o) (d := 8 * sW) (BitVec.ofNat 64 (wsWords len)) (by decide)
  rw [← hm₃] at o3
  have f₃ : Frm (off B o) [(8 * sLink, 8), (8 * sW, 8), (8 * sArr 0, 64)]
      (s.mem.writeW (off B (8 * slotWs)) (off B o)) t.mem := by
    rw [hm']
    exact ((Frm.of_outside o2 (by simp)).trans (Frm.of_outside o3 (by simp))).trans (Frm.of_outside ho₄ (by simp))
  have hL : ∀ r ∈ [(8 * sLink, 8), (8 * sW, 8), (8 * sArr 0, 64)], r.1 + r.2 ≤ 8 * 17 := by
    simp [sLink, sW, sArr, sFn]
  have ho64 : o < 2 ^ 64 := by omega
  have kall := (k₃.trans k₄).trans k'
  refine ⟨?_, ?_, ?_, fun j hj => by rw [hm']; exact harr₄ j hj, h0', ?_,
    ⟨fun r hr => ?_, kall.rd, kall.wr, kall.sp, kall.vcs⟩⟩
  · rw [f₃.word_below hL (by omega) ho64 (by omega)]; exact word_writeW_self _ _ _ _
  · rw [hm', ho₄.word (by unfold sLink sArr sFn; omega) (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm', ho₄.word (by unfold sW sArr; omega) (by decide), hm₃]; exact word_writeW_self _ _ _ _
  · have f₁ : Frm B [(8 * slotWs, 8)] s.mem (s.mem.writeW (off B (8 * slotWs)) (off B o)) :=
      Frm.of_outside o1 (by simp)
    refine (f₁.append (f₃.rebase ho64 (fun r hr => by have := hL r hr; omega))).widen fun r hr => ?_
    simp only [shiftRanges, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    all_goals exact ⟨(o, 8 * 17), by simp, by simp, by simp [sLink, sW, sArr, sFn]⟩
  · by_cases h : r = .x0
    · subst h; rw [h0', h0]
    · exact kall.gpr r (by revert hr h; cases r <;> decide)

/-- `loadArr j sp sl` in a prime's workspace: the bytes whose pointer and
length are in the modulus' header slots `sp` and `sl`, into array `j`. -/
theorem primeLoad_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30) {j : Nat} (hj : j < 8)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {p : Addr} {bs : List Byte}
    (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hk' : bs.length < 2 ^ 31) (hkw : (bs.length + 7) / 8 ≤ wx) :
    WP isa (seqs (loadArr j sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx j) wx = Spec.Rsa.os2ip bs ∧
      Outside (off B o) (slot wx j) (8 * (wx + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hJ := slot_le (w := wx) hj
  have hJ0 := hdr_lt_slot wx j (show 31 < 32 by decide)
  have ho64 : o < 2 ^ 64 := by omega
  have hr : ∀ r ∈ [(slot wx j, 8 * (wx + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
    simp only [List.mem_singleton, forall_eq]; omega
  simp only [loadArr, seqs]
  refine WP.seq (WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) hj)
    fun t₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (off B o) [(slot wx j, 8 * (wx + 2))] s.mem t₁.mem := Frm.of_outside ho₁ (by simp)
  have hc₁ := hc.of_frm f₁ hr k₁.wr (k₁.gpr .x0 (by decide))
  have hb : ∀ i < 32, word t₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    f₁.word_below (fun r hr' => (hr r hr').2) (by omega) ho64 (by omega)
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x5, .x8] (Q := fun t₂ => t₂.gpr .x1 = p ∧
      t₂.gpr .x2 = BitVec.ofNat 64 bs.length ∧ t₂.gpr .x8 = off (off B o) (slot wx j) ∧ t₂.mem = t₁.mem)
    (by brun [ldw, hc₁.x0, hdr_enc (show sLink < 32 by decide), hdr_enc hsp, hdr_enc hsl, hdr_enc (sArr_lt hj),
      hc₁.ld' (show sLink < 32 by decide), hc₁.link', hc₁.ldn hsp, hb sp hsp, hp, hc₁.ldn hsl, hb sl hsl, hl,
      hc₁.ld' (sArr_lt hj), hc₁.harr' hj, off_off]) rfl rfl rfl)
    fun t₂ ⟨⟨h1₂, h2₂, h8₂, hm₂⟩, k₂⟩ => ?_)
  have hs₂ : Scr t₂ (off B o) (slot wx 8) := hc₁.good.scr.congr k₂.wr
  have hsrc₂ : Src t₂ B Z p bs := by
    refine hsrc.congrK (rs := mmRegs ++ [.x1, .x2, .x5, .x8]) ?_ (k₁.trans k₂)
    rw [hm₂]
    exact InScr.of_frm (f₁.rebase ho64 fun r hr' => by have := (hr r hr').2; omega) fun r hr' => by
      simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_singleton] at hr'
      subst hr'; simp only; omega
  refine WP.mono (loadBE_ok hs₂ h1₂ h2₂ h8₂ rfl hk1 hk' rfl (by omega) (fun i hi' => hsrc₂.rd i hi')
    (fun i hi' => hsrc₂.val i hi') (fun i hi' => Or.inr (by
      have := hsrc₂.out i hi'
      rcases ofs_rebase B (p + BitVec.ofNat 64 i) ho64 with ⟨_, h2⟩ | ⟨h1, _⟩
      · omega
      · omega))) fun t ⟨hv, ho, k₃⟩ => ?_
  have f₃ : Frm (off B o) [(slot wx j, 8 * (wx + 2))] t₂.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot wx j) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  have ho' : Outside (off B o) (slot wx j) (8 * (wx + 2)) s.mem t.mem := by
    intro x hx
    rw [ho x (by omega), hm₂, ho₁ x hx]
  refine ⟨hc₁.of_frm (by rw [← hm₂]; exact f₃) hr (by rw [k₃.wr, k₂.wr]) ((k₃.gpr .x0 (by decide)).trans
    (k₂.gpr .x0 (by decide))), ?_, ho', ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have hz : wv t.mem (off B o) (slot wx j + 8 * ((bs.length + 7) / 8)) (wx - (bs.length + 7) / 8) = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
      rw [ho.word (by omega) (by omega), hm₂, show slot wx j + 8 * ((bs.length + 7) / 8) + 8 * q =
        slot wx j + 8 * ((bs.length + 7) / 8 + q) by omega]
      exact (wv_eq_zero_iff _ _ _ _).mp hz₁ _ (by omega)
  rw [wv_split _ _ _ (show (bs.length + 7) / 8 + (wx - (bs.length + 7) / 8) = wx by omega), hv, hz,
    Nat.mul_zero, Nat.add_zero]

end VG.Proof.Bignum.AArch64
