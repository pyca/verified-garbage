import VerifiedGarbage.Proof.Bignum.X86_64.IfmaRegion

/-!
# RSA with AVX512_IFMA on x86-64: from the regions back to the workspaces

`result_ok`: the twenty limbs of `Y` at prime `p`'s region, below `2 X`,
into 64-bit words at `aAcc` (`to64`), and `aY := Y mod X` by a conditional
subtraction (`subMod`, `selectAcc`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oX oY oE oFin sIfma mask52)

/-- The ranges `result` writes in the prime's workspace. -/
def resRanges : List (Nat × Nat) :=
  [(slot 16 Public.aAcc, 8 * 18), (slot 16 Public.aTmp, 8 * 18), (slot 16 Public.aY, 8 * 18)]

/-- The conditional subtraction's result, for `R` abstract. -/
theorem csub_fin {Tl Tw Dv X V c R : Nat} (hR : X < R) (hD : Dv < R) (hTl : Tl < R) (hc : c ≤ 1)
    (hacc : Tl + R * Tw = V) (hV : V < 2 * X) (hsub : Dv + X = Tl + R * c) :
    (if Tw < c then Tl else Dv) = V % X := by
  have := VG.Proof.Bignum.csub_result (Tl := Tl) (Tw := Tw) (Tw1 := 0) hR hD hc hTl (by rw [Nat.mul_zero, Nat.add_zero, hacc]; exact hV)
    hsub
  rwa [Nat.mul_zero, Nat.add_zero, hacc] at this

/-- `result`'s block: `Y`'s seventeen words at `aAcc`, and the bases for the subtraction. -/
theorem resBlock_ok {s : State} {B : Addr} {Z o a p : Nat} {mx : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B o) (hH : Hdr s.mem (off B o) 16 mx)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot 16 8 + tabBytes 16 ≤ a)
    (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2)
    (hL : ∀ j < 20, AmmSym.limb s.mem (off B a) (D * p + oY) j < 2 ^ 52)
    (hV : AmmSym.val52 s.mem (off B a) (D * p + oY) < 2 * wv s.mem (off B o) (slot 16 Public.aN) 16) :
    WP isa (.block (([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (D * p + oY))),
        .mov .r8 (.mem (hdr (sArr Public.aAcc)))] : List Instr) ++ CrtIfma.to64 ++
      ([.mov .rbx (.mem (hdr (sArr Public.aY))), .mov .r10 (.mem (hdr (sArr Public.aN))), .mov .r12 (.mem (hdr sW)),
        .mov .rsi (.mem (hdr (sArr Public.aTmp)))] : List Instr))) s fun t =>
      wv t.mem (off B o) (slot 16 Public.aAcc) 17 = AmmSym.val52 s.mem (off B a) (D * p + oY) ∧
      Outside (off B o) (slot 16 Public.aAcc) 136 s.mem t.mem ∧
      t.gpr .r8 = off (off B o) (slot 16 Public.aAcc) ∧ t.gpr .rbx = off (off B o) (slot 16 Public.aY) ∧
      t.gpr .r10 = off (off B o) (slot 16 Public.aN) ∧ t.gpr .r12 = BitVec.ofNat 64 16 ∧
      t.gpr .rsi = off (off B o) (slot 16 Public.aTmp) ∧
      Keep [.r11, .r8, .rax, .rcx, .rbp, .rbx, .r10, .r12, .rsi] s t := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have : oY = 192 := rfl
  have lA := slot_le (w := 16) (show Public.aAcc < 8 by decide)
  have hA0 := hdr_lt_slot 16 Public.aAcc (show 31 < 32 by decide)
  have hH' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot 16 8 hi; omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r8] (Q := fun t => t.gpr .r11 = off (off B a) (D * p + oY) ∧
    t.gpr .r8 = off (off B o) (slot 16 Public.aAcc) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hH' sIfma (by decide), hH' (sArr Public.aAcc) (by decide),
      AmmSym.se_ofNat (show D * p + oY < 2 ^ 31 by omega)]
    and_intros
    · exact congrArg (· + BitVec.ofNat 64 (D * p + oY)) hia
    · exact hH.harr _ (by decide)) rfl) fun s₁ ⟨⟨r11, r8, me⟩, k₁⟩ => ?_
  have hsep : ∀ m m' : Mem, Outside (off (off B o) (slot 16 Public.aAcc)) 0 136 m m' → ∀ j < 20,
      word m' (off (off B a) (D * p + oY)) (CrtIfma.off j) = word m (off (off B a) (D * p + oY)) (CrtIfma.off j) :=
    fun m m' ho j hj => by
    have := off_lt160 hj
    have f := Frm.of_outside_off (B := B) (by rw [off_off] at ho; exact ho) (by omega) (by omega)
    rw [word_off, word_off, word_off, word_off]
    exact f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only; omega)) (by omega)
  refine WP.mono (AmmSym.to64_ok r11 r8 (fun j hj => by
      have := off_lt160 hj
      rw [k₁.2.1, k₁.2.2, off_off, AmmSym.off_add]; exact hs.ld (by omega))
    (fun w hw => by rw [k₁.2.2, off_off, AmmSym.off_add]; exact hs.st (by omega))
    (fun j hj => by rw [me, word_off]; exact hL j hj) hsep) fun s₂ ⟨hw₂, ho₂, k₂, _⟩ => ?_
  have hlv : VG.Proof.Bignum.Amm52.lval (fun j => (AmmSym.limbsAt s₁.mem (off (off B a) (D * p + oY)) j).toNat) 20 =
      AmmSym.val52 s.mem (off B a) (D * p + oY) := VG.Proof.Bignum.Amm52.lval_congr fun j hj => by
    simp only [AmmSym.limbsAt, hj, ↓reduceIte]
    rw [me, word_off]
  rw [hlv] at hw₂
  have hacc := AmmSym.wv_to64_lt hV hw₂
  rw [me] at ho₂
  have f₂ := Frm.of_outside_off (B := B) (by rw [off_off] at ho₂; exact ho₂) (by omega) (by omega)
  have hh : ∀ i < 32, word s₂.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi => by
    have := hdr_lt_slot 16 Public.aAcc hi
    rw [word_off, word_off]
    exact f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega)) (by omega)
  have hH₂ : Hdr s₂.mem (off B o) 16 mx := ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hH' i hi
  have hdi₂ : s₂.gpr .rdi = off B o := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]; exact hdi
  refine WP.mono (WP.keep [.rbx, .r10, .r12, .rsi] (Q := fun t =>
    t.gpr .rbx = off (off B o) (slot 16 Public.aY) ∧ t.gpr .r10 = off (off B o) (slot 16 Public.aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 16 ∧ t.gpr .rsi = off (off B o) (slot 16 Public.aTmp) ∧ t.mem = s₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ (sArr Public.aY) (by decide), hl₂ (sArr Public.aN) (by decide),
      hl₂ sW (by decide), hl₂ (sArr Public.aTmp) (by decide)]
    and_intros
    · exact hH₂.harr _ (by decide)
    · exact hH₂.harr _ (by decide)
    · exact hH₂.hw
    · exact hH₂.harr _ (by decide)) rfl) fun t ⟨⟨bx, r10, r12, si, me₃⟩, k₃⟩ => ?_
  rw [wv_off, Nat.add_zero] at hacc
  refine ⟨by rw [me₃]; exact hacc, by rw [me₃]; exact AmmSym.Outside.rebase ho₂ (by omega) (by omega), by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact r8,
    bx, r10, r12, si, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `result p`: `aY := Y mod X` in the prime's workspace `off B o` (16
words, `aN = X`), `Y` the limbs at `oY` of region `p` of the area `off B a`. -/
theorem result_ok {s : State} {B : Addr} {Z o a p X : Nat} {mx : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B o) (hH : Hdr s.mem (off B o) 16 mx)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot 16 8 + tabBytes 16 ≤ a)
    (haZ : a + 2 * D + 8 ≤ Z) (hp : p < 2) (hN : wv s.mem (off B o) (slot 16 Public.aN) 16 = X)
    (hL : ∀ j < 20, AmmSym.limb s.mem (off B a) (D * p + oY) j < 2 ^ 52)
    (hV : AmmSym.val52 s.mem (off B a) (D * p + oY) < 2 * X) :
    WP isa (seqs (CrtIfma.result p)) s fun t =>
      wv t.mem (off B o) (slot 16 Public.aY) 16 = AmmSym.val52 s.mem (off B a) (D * p + oY) % X ∧
      Frm B (shiftRanges o resRanges) s.mem t.mem ∧ t.gpr .rdi = s.gpr .rdi ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hD : D = 3712 := rfl
  have hDp : D * p ≤ 3712 := by rcases AmmSym.D_mul hp with h | h <;> omega
  have h8 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have : oY = 192 := rfl
  have lA := slot_le (w := 16) (show Public.aAcc < 8 by decide)
  have lT := slot_le (w := 16) (show Public.aTmp < 8 by decide)
  have lY := slot_le (w := 16) (show Public.aY < 8 by decide)
  have lN := slot_le (w := 16) (show Public.aN < 8 by decide)
  have sAT := slot_sep (w := 16) (show Public.aAcc ≠ Public.aTmp by decide)
  have sAY := slot_sep (w := 16) (show Public.aAcc ≠ Public.aY by decide)
  have sTY := slot_sep (w := 16) (show Public.aTmp ≠ Public.aY by decide)
  have sTN := slot_sep (w := 16) (show Public.aTmp ≠ Public.aN by decide)
  have hA0 := hdr_lt_slot 16 Public.aAcc (show 31 < 32 by decide)
  have hH' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot 16 8 hi; omega)
  have hT8 := hdr_lt_slot 16 Public.aTmp (show 31 < 32 by decide)
  unfold CrtIfma.result
  simp only [seqs]
  refine WP.seq (WP.mono (resBlock_ok hs hdi hH hia hoa haZ hp hL (by rw [hN]; exact hV))
    fun s₁ ⟨hacc, ho₁, r8, bx, r10, r12, si, k₁⟩ => ?_)
  have hsW : Scr s₁ (off B o) (slot 16 8) := (hs.congr k₁.2.2).sub (by omega) (by omega)
  have hN₁ : wv s₁.mem (off B o) (slot 16 Public.aN) 16 = X := by
    rw [ho₁.wv (by rcases slot_sep (w := 16) (show Public.aAcc ≠ Public.aN by decide) with h | h <;> omega)
      (by omega)]; exact hN
  refine WP.seq (WP.mono (subMod_ok hsW r8 r10 si r12 (by decide) (by decide) (by omega) (by omega) (by omega)
    (by omega) (by omega)) fun s₂ ⟨c, lt, hbp, hlt, hD₂, ho₂, k₂⟩ => ?_)
  have hsW₂ := hsW.congr k₂.2.2
  refine WP.mono (selectAcc_ok hsW₂ ((k₂.gpr (by decide)).trans r8) ((k₂.gpr (by decide)).trans si)
    ((k₂.gpr (by decide)).trans bx) ((k₂.gpr (by decide)).trans r12) hbp (by decide) (by decide) (eo := slot 16 Public.aY)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨hv, ho₃, k₃⟩ => ?_
  have hA₂ : wv s₂.mem (off B o) (slot 16 Public.aAcc) 16 = wv s₁.mem (off B o) (slot 16 Public.aAcc) 16 :=
    ho₂.wv (by omega) (by omega)
  rw [show (17 : Nat) = 16 + 1 from rfl, wv] at hacc
  rw [hN₁] at hD₂
  have hX := VG.Proof.Bignum.X86_64.wv_lt s.mem (off B o) (slot 16 Public.aN) 16
  rw [hN] at hX
  have hDl := VG.Proof.Bignum.X86_64.wv_lt s₂.mem (off B o) (slot 16 Public.aTmp) 16
  have hTl := VG.Proof.Bignum.X86_64.wv_lt s₁.mem (off B o) (slot 16 Public.aAcc) 16
  -- The powers in these facts use core's `instPowNat`; say so, or `generalize` evaluates `2 ^ 1024`.
  generalize @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64 * 16) = R
    at hacc hD₂ hX hDl hTl
  have hres := csub_fin hX hDl hTl (Bool.toNat_le c) hacc hV hD₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hv, hA₂, hlt, ← hres]
    by_cases h : (word s₁.mem (off B o) (slot 16 Public.aAcc + 8 * 16)).toNat < c.toNat <;> simp [h]
  · refine (((Frm.of_outside_off ho₁ (by omega) (by omega)).append (Frm.of_outside_off ho₂ (by omega) (by omega))).append
      (Frm.of_outside_off ho₃ (by omega) (by omega))).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨_, List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩, by simp only; omega⟩
    · exact ⟨_, List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩, by simp only; omega⟩
    · exact ⟨_, List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl⟩,
        by simp only; omega⟩
  · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
  · exact ((k₁.trans k₂).trans k₃).mono (by simp [mmRegs])

/-! ## The area's base -/

/-- `ifma`'s first block: the area after `q`'s workspace and table, its base
into both primes' `sIfma`, and into `p`'s workspace. -/
theorem ifmaHead_ok {s : State} {B : Addr} {Z w op oq : Nat} {minv mq : BitVec 64} (hg : Good s B Z w minv)
    (hlo : slot w 8 ≤ op) (hpq : op + slot 16 8 + tabBytes 16 ≤ oq)
    (haZ : oq + slot 16 8 + tabBytes 16 + 2 * D + 8 ≤ Z)
    (hsp : word s.mem B (8 * sWsP) = off B op) (hsq : word s.mem B (8 * sWsQ) = off B oq)
    (hwsq : WsAt s.mem B oq 16 mq) :
    WP isa (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))) s fun t =>
      t.mem = (s.mem.writeW (off (off B op) (8 * sIfma)) (off (off B oq) (slot 16 8 + tabBytes 16))).writeW
        (off (off B oq) (8 * sIfma)) (off (off B oq) (slot 16 8 + tabBytes 16)) ∧
      t.gpr .rdi = off B op ∧ Keep [.rax, .rdx, .rdi] s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hD : D = 3712 := rfl
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = off B oq ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sWsQ (by decide), hsq]) rfl) fun s₁ ⟨⟨dx₁, me₁⟩, k₁⟩ => ?_
  refine WP.mono (wsEndT_ok (X := off B oq) (Z := slot 16 8 + tabBytes 16) (wx := 16)
    ((hs.congr k₁.2.2).sub (by omega) (by omega)) dx₁ (by rw [me₁]; exact hwsq.hdr.hw)
    (by rw [me₁]; exact hwsq.hdr.harr _ (by decide)) (by omega)) fun s₂ ⟨ax₂, me₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hdi₂ : s₂.gpr .rdi = B := by rw [k12.gpr (by decide)]; exact hg.rdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hst : ∀ o, o + 8 * 30 ≤ Z → InRegions s₂.wr (off (off B o) (8 * sIfma)) 8 := fun o ho => by
    rw [k12.2.2, off_off]; exact hs.st (by unfold sIfma sFn; omega)
  have hm₂ : s₂.mem = s.mem := me₂.trans me₁
  have hq' : (s.mem.writeW (off (off B op) (8 * sIfma)) (off (off B oq) (slot 16 8 + tabBytes 16))).readW
      (off B (8 * sWsQ)) 64 = off B oq := by
    rw [off_off]
    have := (writeW_outside s.mem B (d := op + 8 * sIfma) (off (off B oq) (slot 16 8 + tabBytes 16))
      (by unfold sIfma sFn; omega)).word (d := 8 * sWsQ) (.inl (by unfold sWsQ sFn; omega))
      (by unfold sWsQ sFn; omega)
    exact this.trans hsq
  refine WP.mono (WP.keep [.rdx, .rdi] (Q := fun t =>
    t.mem = (s.mem.writeW (off (off B op) (8 * sIfma)) (off (off B oq) (slot 16 8 + tabBytes 16))).writeW
      (off (off B oq) (8 * sIfma)) (off (off B oq) (slot 16 8 + tabBytes 16)) ∧ t.gpr .rdi = off B op) (by
    xrun [State.ea, hdr, ws, enterP, hdi₂, hdrOff, hl₂ sWsP (by decide), hl₂ sWsQ (by decide), hm₂, hsp, ax₂,
      hst op (by omega), hst oq (by omega), hq']
    show word _ B (8 * sWsP) = off B op
    have e1 := (writeW_outside s.mem B (d := op + 8 * sIfma) (off (off B oq) (slot 16 8 + tabBytes 16))
      (by unfold sIfma sFn; omega)).word (d := 8 * sWsP) (.inl (by unfold sWsP sFn; omega)) (by unfold sWsP sFn; omega)
    have e2 := (writeW_outside (s.mem.writeW (off B (op + 8 * sIfma)) (off (off B oq) (slot 16 8 + tabBytes 16))) B
      (d := oq + 8 * sIfma) (off (off B oq) (slot 16 8 + tabBytes 16))
      (by unfold sIfma sFn; omega)).word (d := 8 * sWsP) (.inl (by unfold sWsP sFn; omega)) (by unfold sWsP sFn; omega)
    rw [off_off B op, off_off B oq (8 * sIfma), e2, e1]
    exact hsp) rfl) fun t ⟨⟨me, di⟩, k₃⟩ => ?_
  exact ⟨me, di, (k12.trans k₃).mono (by simp)⟩

end VG.Proof.Bignum.X86_64
