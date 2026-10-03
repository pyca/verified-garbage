import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

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
theorem wsEnd_ok {s : State} {X : Addr} {Z wx : Nat} (hs : Scr s X Z) (hdx : s.gpr .rdx = X)
    (hw : word s.mem X (8 * sW) = BitVec.ofNat 64 wx)
    (ha : word s.mem X (8 * sArr Public.aOne) = off X (slot wx Public.aOne)) (hZ : slot wx 8 ≤ Z) :
    WP isa (.block wsEnd) s fun t => t.gpr .rax = off X (slot wx 8) ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off X (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot wx 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (c := .block wsEnd)
    (Q := fun t => t.gpr .rax = off X (slot wx 8) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  unfold wsEnd
  xrun [State.ea, ws, hdx, hdrOff, hl (sArr Public.aOne) (by decide), ha, hl sW (by decide), hw, sx2]
  rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
  simp only [BitVec.ofNat_add_ofNat, off, BitVec.add_assoc]
  congr 2
  unfold slot Public.aOne; omega

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
theorem wsNew_ok {s : State} {B : Addr} {Z o len : Nat} {slotWs slotLen : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hax : s.gpr .rax = off B o) (hws : slotWs < 32) (hsl : slotLen < 32)
    (hne : slotWs ≠ slotLen) (hlen : word s.mem B (8 * slotLen) = BitVec.ofNat 64 len) (hlen' : len < 2 ^ 32)
    (ho : 8 * 32 ≤ o) (hZ : o + slot (wsWords len) 8 ≤ Z) :
    WP isa (seqs (wsNew slotWs slotLen)) s fun t =>
      word t.mem B (8 * slotWs) = off B o ∧ word t.mem (off B o) (8 * sLink) = B ∧
      word t.mem (off B o) (8 * sW) = BitVec.ofNat 64 (wsWords len) ∧
      (∀ j < 8, word t.mem (off B o) (8 * sArr j) = off (off B o) (slot (wsWords len) j)) ∧
      t.gpr .rdi = B ∧ Frm B [(8 * slotWs, 8), (o, 8 * 17)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h256 : 256 ≤ slot (wsWords len) 8 := by unfold slot hdrBytes; omega
  have hs' : Scr s (off B o) (slot (wsWords len) 8) := hs.sub hZ (by omega)
  have hX : ∀ v : BitVec 64, (s.mem.writeW (off B (8 * slotWs)) v).readW (off B (8 * slotLen)) 64 =
      BitVec.ofNat 64 len := fun v => (hdrStore_hdr s.mem B v hws hsl hne).trans hlen
  simp only [wsNew, seqs]
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t₁.cf = some (decide ((len + 7) / 8 < 2)) ∧ t₁.mem = s.mem.writeW (off B (8 * slotWs)) (off B o))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.st (d := 8 * slotWs) (by omega), hax,
      hs.ld (d := 8 * slotLen) (by omega), hX, shr3_w len hlen', sx2, cf_lt2 (show (len + 7) / 8 < 2 ^ 64 by omega)])
    rfl) fun t₁ ⟨⟨h12₁, hcf₁, hm₁⟩, k₁⟩ => ?_)
  have hite : WP isa (.ite .b (.block [.mov32 .r12 (.imm 2)]) (.block [])) t₁ fun t₂ =>
      t₂.gpr .r12 = BitVec.ofNat 64 (wsWords len) ∧ t₂.mem = t₁.mem ∧ Keep [.r12] t₁ t₂ := by
    by_cases h2 : (len + 7) / 8 < 2
    · refine WP.ite true (by simp [eval, hcf₁, h2]) (fun _ => ?_) (by simp)
      refine WP.mono (WP.keep [.r12] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 (wsWords len) ∧
          t₂.mem = t₁.mem) (by
        xrun
        unfold wsWords; rw [Nat.max_eq_left (by omega)]; rfl) rfl) fun t₂ ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
    · refine WP.ite false (by simp [eval, hcf₁, h2]) (by simp) (fun _ => WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩)
      rw [h12₁]; unfold wsWords; rw [Nat.max_eq_right (by omega)]
  refine WP.seq (WP.mono hite fun t₂ ⟨h12₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  have hax₂ : t₂.gpr .rax = off B o := (k12.gpr (by decide)).trans hax
  have hs₂' : Scr t₂ (off B o) (slot (wsWords len) 8) := hs'.congr k12.2.2
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun t₃ => t₃.gpr .rsi = B ∧ t₃.gpr .rdi = off B o ∧
      t₃.mem = (t₂.mem.writeW (off (off B o) (8 * sLink)) B).writeW (off (off B o) (8 * sW))
        (BitVec.ofNat 64 (wsWords len)))
    (by xrun [State.ea, hdr, hdi₂, hax₂, hdrOff, hs₂'.st (d := 8 * sLink) (by unfold sLink sFn; omega),
      hs₂'.st (d := 8 * sW) (by unfold sW; omega), h12₂]) rfl) fun t₃ ⟨⟨hsi₃, hdi₃, hm₃⟩, k₃⟩ => ?_
  have hs₃' := hs₂'.congr k₃.2.2
  refine WP.mono (setBases_ok hs₃' hdi₃ ((k₃.gpr (by decide)).trans h12₂) (by unfold sArr; omega))
    fun t₄ ⟨harr₄, ho₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₄.mem)
    (by xrun [(k₄.gpr (by decide)).trans hsi₃]) rfl) fun t ⟨⟨hdi', hm'⟩, k'⟩ => ?_
  have o1 := writeW_outside s.mem B (d := 8 * slotWs) (off B o) (by omega)
  have o2 := writeW_outside t₂.mem (off B o) (d := 8 * sLink) B (by decide)
  have o3 := writeW_outside (t₂.mem.writeW (off (off B o) (8 * sLink)) B) (off B o) (d := 8 * sW)
    (BitVec.ofNat 64 (wsWords len)) (by decide)
  rw [← hm₁] at o1
  rw [← hm₃] at o3
  have f₃ : Frm (off B o) [(8 * sLink, 8), (8 * sW, 8), (8 * sArr 0, 64)] t₂.mem t.mem := by
    rw [hm']
    exact ((Frm.of_outside o2 (by simp)).trans (Frm.of_outside o3 (by simp))).trans (Frm.of_outside ho₄ (by simp))
  have hL : ∀ r ∈ [(8 * sLink, 8), (8 * sW, 8), (8 * sArr 0, 64)], r.1 + r.2 ≤ 8 * 17 := by
    simp [sLink, sW, sArr, sFn]
  have ho64 : o < 2 ^ 64 := by omega
  have kall := (((k₁.trans k₂).trans k₃).trans k₄).trans k'
  refine ⟨?_, ?_, ?_, fun j hj => by rw [hm']; exact harr₄ j hj, hdi', ?_,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [f₃.word_below hL (by omega) ho64 (by omega), hm₂, hm₁]; exact word_writeW_self _ _ _ _
  · rw [hm', ho₄.word (by unfold sLink sArr sFn; omega) (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm', ho₄.word (by unfold sW sArr; omega) (by decide), hm₃]; exact word_writeW_self _ _ _ _
  · have f₁ : Frm B [(8 * slotWs, 8)] s.mem t₂.mem := by rw [hm₂]; exact Frm.of_outside o1 (by simp)
    refine (f₁.append (f₃.rebase ho64 (fun r hr => by have := hL r hr; omega))).widen fun r hr => ?_
    simp only [shiftRanges, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
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
  refine WP.seq (WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) hj)
    fun t₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have f₁ : Frm (off B o) [(slot wx j, 8 * (wx + 2))] s.mem t₁.mem := Frm.of_outside ho₁ (by simp)
  have hc₁ := hc.of_frm f₁ hr k₁.2.2 (k₁.gpr (by decide))
  have hb : ∀ i < 32, word t₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    f₁.word_below (fun r hr' => (hr r hr').2) (by omega) ho64 (by omega)
  have hl₁ : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    hc₁.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hln : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off B (8 * i)) 8 := fun i hi' =>
    hc₁.scr.ld (by omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .rcx, .rbx] (Q := fun t₂ => t₂.gpr .rsi = p ∧
      t₂.gpr .rcx = BitVec.ofNat 64 bs.length ∧ t₂.gpr .rbx = off (off B o) (slot wx j) ∧ t₂.mem = t₁.mem)
    (by xrun [State.ea, hdr, ws, hc₁.rdi, hdrOff, hl₁ sLink (by decide), hc₁.link, hln sp hsp, hb sp hsp, hp,
      hln sl hsl, hb sl hsl, hl, hl₁ (sArr j) (by unfold sArr; omega), hc₁.hdr.harr j hj]) rfl)
    fun t₂ ⟨⟨hsi₂, hcx₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  have hs₂ : Scr t₂ (off B o) (slot wx 8) := hc₁.good.scr.congr k₂.2.2
  have hsrc₂ : Src t₂ B Z p bs := by
    refine hsrc.congrK (rs := mmRegs ++ [.rax, .rsi, .rcx, .rbx]) ?_ (k₁.trans k₂)
    rw [hm₂]
    exact InScr.of_frm (f₁.rebase ho64 fun r hr' => by have := (hr r hr').2; omega) fun r hr' => by
      simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_singleton] at hr'
      subst hr'; simp only; omega
  have hw' : (bs.length + 7) / 8 ≤ wx := hkw
  refine WP.mono (loadBE_ok hs₂ hsi₂ hcx₂ hbx₂ rfl hk1 hk' rfl (by omega) (fun i hi' => hsrc₂.rd i hi')
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
  refine ⟨hc₁.of_frm (by rw [← hm₂]; exact f₃) hr (by rw [k₃.2.2, k₂.2.2]) ((k₃.gpr (by decide)).trans
    (k₂.gpr (by decide))), ?_, ho', ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have hz : wv t.mem (off B o) (slot wx j + 8 * ((bs.length + 7) / 8)) (wx - (bs.length + 7) / 8) = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
      rw [ho.word (by omega) (by omega), hm₂, show slot wx j + 8 * ((bs.length + 7) / 8) + 8 * q =
        slot wx j + 8 * ((bs.length + 7) / 8 + q) by omega]
      exact (wv_eq_zero_iff _ _ _ _).mp hz₁ _ (by omega)
  rw [wv_split _ _ _ (show (bs.length + 7) / 8 + (wx - (bs.length + 7) / 8) = wx by omega), hv, hz,
    Nat.mul_zero, Nat.add_zero]

end VG.Proof.Bignum.X86_64
