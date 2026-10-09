import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-!
# `R² mod m` by word steps with ADX: `t = x 2^64 + q̂ mc - q̂ R` in place

`R2Adx.mulSub` (`Impl/Bignum/X86_64/R2Adx.lean`) over `w` words of `x` (at
`rbx`) and `mc` (at `rsi`), four at a time (`tile`), the carries in the flags
within a tile and in registers between tiles: the high word in `r9`, `CF` as
the mask in `r14`, the previous word of `x` in `r8`. Through every word `i`
(`WI`): `T_i + 2^(64 i) (h + OF + CF + prev) = X_i 2^64 + q̂ C_i` for the low
`i` words `X_i` of `x`, `C_i` of `mc` and `T_i` of `t` (`mulSub_ok`).
-/

namespace VG.Proof.Bignum.X86_64.R2a

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem wv_succ (m : Mem) (B : Addr) (e n : Nat) :
    wv m B e (n + 1) = wv m B e n + 2 ^ (64 * n) * (word m B (e + 8 * n)).toNat := rfl

/-- The registers a pass may change. -/
abbrev chRegs : List Reg := [.r8, .r9, .r11, .r13, .rax, .r14, .r15, .rcx]

/-- After the words below `i` of `t`, from `s₀`, in a tile at word `j`: the
previous word of `x` in `p`, the high word in `h` and the carries in the flags. -/
structure WI (s₀ : State) (B : Addr) (Z ex ec w j i : Nat) (p h : Reg) (t : State) : Prop where
  scr : Scr t B Z
  regs : ∀ r, r ∉ chRegs → t.gpr r = s₀.gpr r
  r15 : t.gpr .r15 = BitVec.ofNat 64 j
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  rcx : t.gpr .rcx = 0
  val : ∃ c o : Bool, t.cf = some c ∧ t.of = some o ∧ (t.gpr h).toNat + o.toNat ≤ 2 ^ 64 - 1 ∧
    wv t.mem B ex i + 2 ^ (64 * i) * ((t.gpr h).toNat + o.toNat + c.toNat + (t.gpr p).toNat) =
      wv s₀.mem B ex i * 2 ^ 64 + (s₀.gpr .rdx).toNat * wv s₀.mem B ec i
  out : Outside B ex (8 * i) s₀.mem t.mem

/-- A word of a tile, on `WI`. -/
theorem wstep {s₀ t : State} {B : Addr} {Z ex ec w j k : Nat} {prev next hiP hiN : Reg}
    (hI : WI s₀ B Z ex ec w j (j + k) prev hiP t) (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec)
    (hjk : j + k < w) (hX : ex + 8 * w ≤ Z) (hC : ec + 8 * w ≤ Z) (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex)
    (hn : next ∈ chRegs) (hp : prev ∈ chRegs) (hh : hiN ∈ chRegs)
    (d1 : hiN ≠ .r11) (d2 : hiP ≠ .r11) (d4 : next ≠ .r11) (d5 : next ≠ hiN) (d6 : prev ≠ .r11)
    (d7 : prev ≠ hiN) (d8 : prev ≠ next) (d9 : hiN ≠ .rbx) (d10 : hiN ≠ .r15) (d11 : next ≠ .rbx)
    (d12 : next ≠ .r15) (d14 : prev ≠ .rbx) (d15 : prev ≠ .r15) (d16 : hiP ≠ hiN) (d18 : hiN ≠ .rcx)
    (d19 : next ≠ .rcx) (d20 : prev ≠ .rcx) :
    WP isa (.block (R2Adx.word k prev next hiP hiN)) t (WI s₀ B Z ex ec w j (j + k + 1) next hiN) := by
  have hn' := hI.scr.nowrap
  obtain ⟨c, o, hc, ho, hhl, hv⟩ := hI.val
  have tbx : t.gpr .rbx = off B ex := (hI.regs _ (by decide)).trans hbx
  have tsi : t.gpr .rsi = off B ec := (hI.regs _ (by decide)).trans hsi
  have tdx : t.gpr .rdx = s₀.gpr .rdx := hI.regs _ (by decide)
  refine WP.mono (word_ok hI.scr tbx tsi hI.r15 (by omega) (by omega) hc ho d1 d2 d4 d5 d6 d7 d8 d9 d10 d11 d12
    d14 d15 d16) fun t' ⟨c', o', hc', ho', he, hhl', hnx, hm, k'⟩ => ?_
  have hxw : word t.mem B (ex + 8 * j + 8 * k) = word s₀.mem B (ex + 8 * (j + k)) := by
    rw [show ex + 8 * j + 8 * k = ex + 8 * (j + k) by omega, hI.out.word (by omega) (by omega)]
  have hcw : word t.mem B (ec + 8 * j + 8 * k) = word s₀.mem B (ec + 8 * (j + k)) := by
    rw [show ec + 8 * j + 8 * k = ec + 8 * (j + k) by omega, hI.out.word (by omega) (by omega)]
  have oo : Outside B (ex + 8 * (j + k)) 8 t.mem t'.mem := by
    rw [hm, show ex + 8 * j + 8 * k = ex + 8 * (j + k) by omega]; exact writeW_outside _ _ _ (by omega)
  refine ⟨hI.scr.congr k'.2.2, fun r hr => ?_, ?_, k'.2.1.trans hI.rd, k'.2.2.trans hI.wr, ?_,
    ⟨c', o', hc', ho', by have := Bool.toNat_le o'; omega, ?_⟩,
    (hI.out.mono (Nat.le_refl _) (by omega)).trans (oo.mono (by omega) (by omega))⟩
  · have hr' : r ∉ [hiN, .r11, next, prev] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl)
      exacts [hr hh, hr (by decide), hr hn, hr hp]
    rw [k'.gpr hr', hI.regs r hr]
  · rw [k'.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨Ne.symm d10, by decide,
      Ne.symm d12, Ne.symm d15⟩)]; exact hI.r15
  · rw [k'.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨Ne.symm d18, by decide,
      Ne.symm d19, Ne.symm d20⟩)]; exact hI.rcx
  · have hT : wv t'.mem B ex (j + k + 1) = wv t.mem B ex (j + k) + 2 ^ (64 * (j + k)) *
        (word t'.mem B (ex + 8 * j + 8 * k)).toNat := by
      have e := wv_writeW_top t.mem B ex (j + k) (word t'.mem B (ex + 8 * j + 8 * k)) (by omega)
      rw [show ex + 8 * (j + k) = ex + 8 * j + 8 * k by omega, ← hm] at e
      exact e
    rw [hT, hnx, hxw, wv_succ s₀.mem B ex, wv_succ s₀.mem B ec]
    rw [hcw, tdx] at he
    have p1 : 2 ^ (64 * (j + k + 1)) = 2 ^ (64 * (j + k)) * 2 ^ 64 := by
      rw [show 64 * (j + k + 1) = 64 * (j + k) + 64 by omega, Nat.pow_add]
    rw [p1]
    generalize 2 ^ (64 * (j + k)) = P at *
    have e := congrArg (P * ·) he
    simp only [Nat.mul_add] at e
    grind

/-- At a tile's start, from `s₀`: the carries in registers. -/
structure TI (s₀ : State) (B : Addr) (Z ex ec w : Nat) (J : Nat) (t : State) : Prop where
  scr : Scr t B Z
  regs : ∀ r, r ∉ chRegs → t.gpr r = s₀.gpr r
  r15 : t.gpr .r15 = BitVec.ofNat 64 (4 * J)
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  val : ∃ c : Bool, t.gpr .r14 = mask c ∧
    wv t.mem B ex (4 * J) + 2 ^ (64 * (4 * J)) * ((t.gpr .r9).toNat + c.toNat + (t.gpr .r8).toNat) =
      wv s₀.mem B ex (4 * J) * 2 ^ 64 + (s₀.gpr .rdx).toNat * wv s₀.mem B ec (4 * J)
  out : Outside B ex (8 * (4 * J)) s₀.mem t.mem

theorem mask_add_cf (c : Bool) : decide (2 ^ 64 ≤ (mask c).toNat + (mask c).toNat) = c := by
  cases c <;> decide

theorem mask_add_of (c : Bool) : addOverflow (mask c) (mask c) (mask c + mask c) = false := by
  cases c <;> decide

/-- The carries into the flags: `CF` from the mask, `OF` clear, `rcx = 0`. -/
theorem head_ok {s₀ t : State} {B : Addr} {Z ex ec w J : Nat} (hI : TI s₀ B Z ex ec w J t) :
    WP isa (.block tileHead) t (WI s₀ B Z ex ec w (4 * J) (4 * J + 0) .r8 .r9) := by
  obtain ⟨c, h14, hv⟩ := hI.val
  refine WP.mono (WP.keep [.rcx, .r14] (Q := fun t' => t'.gpr .rcx = 0 ∧ t'.cf = some c ∧ t'.of = some false ∧
      t'.mem = t.mem) (by
    unfold tileHead
    xrun [h14, mask_add_cf, mask_add_of, BitVec.xor_self]
    rfl) rfl) fun t' ⟨⟨hcx, hc, ho, hm⟩, k⟩ => ?_
  refine ⟨hI.scr.congr k.2.2, fun r hr => ?_, ?_, k.2.1.trans hI.rd, k.2.2.trans hI.wr, hcx,
    ⟨c, false, hc, ho, ?_, ?_⟩, by rw [hm]; exact hI.out⟩
  · rw [k.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (rfl | rfl) <;> exact hr (by decide)),
      hI.regs r hr]
  · rw [k.gpr (by decide)]; exact hI.r15
  · have := (t'.gpr .r9).isLt; simp only [Bool.toNat_false]; omega
  · rw [hm, k.gpr (by decide), k.gpr (by decide), Nat.add_zero]
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [show (t.gpr .r9).toNat + c.toNat + (t.gpr .r8).toNat = (t.gpr .r9).toNat + 0 + c.toNat + (t.gpr .r8).toNat
      by omega] at hv
    exact hv

/-- The carries out of the flags, and the next tile: `ZF` after the last of `N`. -/
theorem tail_ok {s₀ t : State} {B : Addr} {Z ex ec w J N : Nat} (hI : WI s₀ B Z ex ec w (4 * J) (4 * J + 4) .r8 .r9 t)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N)) (hJ : J < N) (hN : N < 2 ^ 60) :
    WP isa (.block tileTail) t fun t' => t'.zf = some (decide (J + 1 = N)) ∧ TI s₀ B Z ex ec w (J + 1) t' := by
  obtain ⟨c, o, hc, ho, hb, hv⟩ := hI.val
  rw [show tileTail = ([.adox .r9 (.reg .rcx)] : List Instr) ++
    ([.alu .sbb .r14 (.reg .r14), .alu .add .r15 (.imm 4), .alu .cmp .r15 (.reg .r12)] : List Instr) from rfl,
    WP.block_append_iff]
  refine WP.mono (adox_ok t (src := .reg .rcx) rfl (fun _ h => nomatch h) ho) fun t₁ ⟨o', ho₁, hc₁, e₁, k₁⟩ => ?_
  have hcx : (t.gpr .rcx).toNat = 0 := by rw [hI.rcx]; rfl
  have ho' : o' = false := by
    cases o'
    · rfl
    · simp only [Bool.toNat_true] at e₁; have := (t₁.gpr .r9).isLt; omega
  subst ho'
  have h15 : t₁.gpr .r15 = BitVec.ofNat 64 (4 * J) := (k₁.gpr (by decide)).trans hI.r15
  have h12' : t₁.gpr .r12 = BitVec.ofNat 64 (4 * N) := (k₁.gpr (by decide)).trans ((hI.regs _ (by decide)).trans h12)
  have hadd : BitVec.ofNat 64 (4 * J) + 4 = BitVec.ofNat 64 (4 * (J + 1)) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]
    congr 1
  have hcmp : (BitVec.ofNat 64 (4 * (J + 1)) - BitVec.ofNat 64 (4 * N) == 0) = decide (J + 1 = N) := by
    rw [ofNat_sub_beq (by omega) (by omega)]; exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.r14, .r15] (Q := fun t' => t'.gpr .r14 = mask c ∧
      t'.gpr .r15 = BitVec.ofNat 64 (4 * (J + 1)) ∧ t'.zf = some (decide (J + 1 = N)) ∧ t'.mem = t₁.mem) (by
    xrun [hc₁.trans hc, h15, h12']
    exact ⟨rfl, hadd, by rw [hadd]; exact hcmp⟩) rfl) fun t' ⟨⟨h14, h15', hz, hm⟩, k⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k.2.2.trans k₁.2.2.2), fun r hr => ?_, h15', k.2.1.trans (k₁.2.2.1.trans hI.rd),
    k.2.2.trans (k₁.2.2.2.trans hI.wr), ⟨c, h14, ?_⟩, by rw [hm, k₁.2.1]; exact hI.out⟩
  · rw [k.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (rfl | rfl) <;> exact hr (by decide)),
      k₁.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro rfl; exact hr (by decide)),
      hI.regs r hr]
  · have g9 : t'.gpr .r9 = t₁.gpr .r9 := k.gpr (by decide)
    have g8 : t'.gpr .r8 = t.gpr .r8 := (k.gpr (by decide)).trans (k₁.gpr (by decide))
    rw [hm, k₁.2.1, g9, g8]
    rw [hcx, Nat.add_zero] at e₁
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e₁
    rw [show 4 * (J + 1) = 4 * J + 4 by omega, e₁]
    omega

/-- A tile: four words of `t`, and `ZF` after the last of `N`. -/
theorem tile_ok {s₀ t : State} {B : Addr} {Z ex ec w J N : Nat} (hI : TI s₀ B Z ex ec w J t)
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N))
    (hw : w = 4 * N) (hJ : J < N) (hN : N < 2 ^ 60) (hX : ex + 8 * w ≤ Z) (hC : ec + 8 * w ≤ Z)
    (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa (.block tile) t fun t' => t'.zf = some (decide (J + 1 = N)) ∧ TI s₀ B Z ex ec w (J + 1) t' := by
  unfold tile
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (head_ok hI) fun t₀ h₀ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wstep (k := 0) h₀ hbx hsi (by omega) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wstep (k := 1) h₁ hbx hsi (by omega) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wstep (k := 2) h₂ hbx hsi (by omega) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wstep (k := 3) h₃ hbx hsi (by omega) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₄ h₄ => ?_
  exact tail_ok h₄ h12 hJ hN

/-- The tiles: the low `w = 4 N` words of `t`. -/
theorem tiles_ok {s₀ : State} {B : Addr} {Z ex ec w N : Nat} (h0 : TI s₀ B Z ex ec w 0 s₀)
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N))
    (hw : w = 4 * N) (hN0 : 0 < N) (hN : N < 2 ^ 60) (hX : ex + 8 * w ≤ Z) (hC : ec + 8 * w ≤ Z)
    (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa (.loop (.block tile) .ne) s₀ (TI s₀ B Z ex ec w N) :=
  wp_upto (a := 0) (N := N) hN0 (TI s₀ B Z ex ec w) (fun _ _ hJ _ hI =>
    tile_ok hI hbx hsi h12 hw hJ hN hX hC sep) (fun _ h => h) h0

/-- `q̂` into `rdx`, `mc` into `rsi`, no carries: a tile's start. -/
theorem mulHead_ok {s : State} {B : Addr} {Z ec : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hA : word s.mem B (8 * sArr Public.aAcc) = off B ec) (hZ : 8 * sArr Public.aAcc + 8 ≤ Z) :
    WP isa (.block mulHead) s fun t => t.gpr .rdx = s.gpr .rcx ∧ t.gpr .rsi = off B ec ∧ t.gpr .r8 = 0 ∧
      t.gpr .r9 = 0 ∧ t.gpr .r14 = 0 ∧ t.gpr .r15 = 0 ∧ t.mem = s.mem ∧
      Keep [.rdx, .rsi, .r8, .r9, .r14, .r15] s t := by
  refine WP.mono (WP.keep [.rdx, .rsi, .r8, .r9, .r14, .r15] (Q := fun t => t.gpr .rdx = s.gpr .rcx ∧
      t.gpr .rsi = off B ec ∧ t.gpr .r8 = 0 ∧ t.gpr .r9 = 0 ∧ t.gpr .r14 = 0 ∧ t.gpr .r15 = 0 ∧ t.mem = s.mem) (by
    unfold mulHead
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld hZ, hA]) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2, k⟩

theorem top_arith {T P W r9 c r8 q r8' c' V : Nat} (hW : W = P * 2 ^ 64) (hq : q ≤ 2 ^ 64)
    (h1 : T + P * (r9 + c + r8) = V) (h2 : r8' + 2 ^ 64 * c' = r8 + r9 + c) :
    (T + P * ((r8' + (2 ^ 64 - q)) % 2 ^ 64) + q * P) % W = V % W := by
  rw [← Nat.mul_mod_mul_left, ← hW]
  generalize hd : 2 ^ 64 - q = d
  have hqd : q + d = 2 ^ 64 := by omega
  generalize hA : P * (r8' + d) = A
  have e : T + A + q * P + W * c' = V + W := by
    rw [← h1, ← hA, hW, show r9 + c + r8 = r8' + 2 ^ 64 * c' by omega, ← hqd]
    grind
  have hm := Nat.mod_add_div A W
  calc (T + A % W + q * P) % W = (T + A % W + q * P + W * (A / W)) % W := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (T + A + q * P) % W := by congr 1; omega
    _ = (T + A + q * P + W * c') % W := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (V + W) % W := by rw [e]
    _ = V % W := Nat.add_mod_right _ _

/-- `t[w] = prev + h + CF - q̂`, after the tiles. -/
theorem mulTop_ok {s₀ t : State} {B : Addr} {Z ex ec w N : Nat} (hI : TI s₀ B Z ex ec w N t)
    (hbx : s₀.gpr .rbx = off B ex) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hX : ex + 8 * (w + 1) ≤ Z)
    (hw : w = 4 * N) :
    WP isa (.block mulTop) t fun t' =>
      (wv t'.mem B ex (w + 1) + (s₀.gpr .rdx).toNat * 2 ^ (64 * w)) % 2 ^ (64 * (w + 1)) =
        (wv s₀.mem B ex w * 2 ^ 64 + (s₀.gpr .rdx).toNat * wv s₀.mem B ec w) % 2 ^ (64 * (w + 1)) ∧
      Outside B ex (8 * (w + 1)) s₀.mem t'.mem ∧ Keep [.rcx, .r14, .r8] t t' := by
  subst hw
  have hn := hI.scr.nowrap
  obtain ⟨c, h14, hv⟩ := hI.val
  rw [show mulTop = ([.alu .xor .rcx (.reg .rcx), .alu .add .r14 (.reg .r14)] : List Instr) ++
    (([.adcx .r8 (.reg .r9)] : List Instr) ++ (([.alu .sub .r8 (.reg .rdx)] : List Instr) ++
      ([.store (ix .rbx .r12) .r8] : List Instr))) from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r14] (Q := fun t' => t'.cf = some c ∧ t'.mem = t.mem) (by
    xrun [h14, mask_add_cf]) rfl) fun t₁ ⟨⟨hc₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcx_ok t₁ (src := .reg .r9) rfl (fun _ h => nomatch h) hc₁) fun t₂ ⟨c', _, _, e₂, k₂⟩ => ?_
  have tbx : t₂.gpr .rbx = off B ex := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.regs _ (by decide)]; exact hbx
  have t12 : t₂.gpr .r12 = BitVec.ofNat 64 (4 * N) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.regs _ (by decide)]; exact h12
  have tdx : t₂.gpr .rdx = s₀.gpr .rdx := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.regs _ (by decide)]
  have hs₂ : Scr t₂ B Z := hI.scr.congr (k₂.2.2.2.trans k₁.2.2)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8] (Q := fun t₃ => t₃.gpr .r8 = t₂.gpr .r8 - s₀.gpr .rdx ∧ t₃.mem = t₂.mem)
    (by xrun [tdx]) rfl) fun t₃ ⟨⟨h8₃, hm₃⟩, k₃⟩ => ?_
  have hea : t₃.ea (ix .rbx .r12) = off B (ex + 8 * (4 * N)) :=
    ea_ix0 t₃ ((k₃.gpr (by decide)).trans tbx) ((k₃.gpr (by decide)).trans t12)
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t₂.mem.writeW (off B (ex + 8 * (4 * N)))
      (t₂.gpr .r8 - s₀.gpr .rdx)) (by
    xrun [hea, (hs₂.congr k₃.2.2).st (show ex + 8 * (4 * N) + 8 ≤ Z by omega), h8₃, hm₃]) rfl)
    fun t' ⟨hm, k'₀⟩ => ?_
  have k' : Keep [.r8] t₂ t' := (k₃.trans k'₀).mono (by decide)
  have hm₂ : t₂.mem = t.mem := k₂.2.1.trans hm₁
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, hm₂, wv_writeW_top _ _ _ _ _ (by omega), BitVec.toNat_sub]
    rw [k₁.gpr (by decide), k₁.gpr (by decide)] at e₂
    have := (s₀.gpr .rdx).isLt
    rw [show (2 ^ 64 - (s₀.gpr .rdx).toNat + (t₂.gpr .r8).toNat) % 2 ^ 64 =
      ((t₂.gpr .r8).toNat + (2 ^ 64 - (s₀.gpr .rdx).toNat)) % 2 ^ 64 by rw [Nat.add_comm]]
    exact top_arith (P := 2 ^ (64 * (4 * N))) (by rw [← Nat.pow_add]; congr 1) (by omega) hv e₂
  · rw [hm, hm₂]
    exact (hI.out.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · exact ((k₁.trans ⟨k₂.1, k₂.2.2⟩).trans k').mono (by decide)

/-- `t := x 2^64 + q̂ mc - q̂ R` in place over `w + 1` words, `q̂` in `rcx`, `mc` from the header. -/
theorem mulSub_ok {s : State} {B : Addr} {Z w ex ec N : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hA : word s.mem B (8 * sArr Public.aAcc) = off B ec) (hZ : 8 * sArr Public.aAcc + 8 ≤ Z)
    (hbx : s.gpr .rbx = off B ex) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : w = 4 * N) (hN0 : 0 < N)
    (hN : N < 2 ^ 60) (hX : ex + 8 * (w + 1) ≤ Z) (hC : ec + 8 * w ≤ Z)
    (sep : ex + 8 * (w + 1) ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa mulSub s fun t =>
      (wv t.mem B ex (w + 1) + (s.gpr .rcx).toNat * 2 ^ (64 * w)) % 2 ^ (64 * (w + 1)) =
        (wv s.mem B ex w * 2 ^ 64 + (s.gpr .rcx).toNat * wv s.mem B ec w) % 2 ^ (64 * (w + 1)) ∧
      Outside B ex (8 * (w + 1)) s.mem t.mem ∧
      Keep [.rdx, .rsi, .r8, .r9, .r11, .r13, .rax, .r14, .r15, .rcx] s t := by
  unfold mulSub
  refine WP.seq (WP.mono (mulHead_ok hs hdi hA hZ) fun s₀ ⟨hdx, hsi, h8, h9, h14, h15, hm, k⟩ => ?_)
  have b0 : s₀.gpr .rbx = off B ex := (k.gpr (by decide)).trans hbx
  have c0 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N) := by rw [k.gpr (by decide), h12, hw]
  have h0 : TI s₀ B Z ex ec w 0 s₀ := ⟨hs.congr k.2.2, fun _ _ => rfl, h15, rfl, rfl,
    ⟨false, h14, by rw [h8, h9]; simp [wv]⟩, Outside.refl _ _ _ _⟩
  refine WP.seq (WP.mono (tiles_ok h0 b0 hsi c0 hw hN0 hN (by omega) hC (by omega)) fun t hT => ?_)
  refine WP.mono (mulTop_ok hT b0 (by rw [c0, hw]) hX hw) fun t' ⟨hv, ho, k'⟩ => ⟨?_, ?_, ?_⟩
  · rw [hdx, hm] at hv; exact hv
  · rw [← hm]; exact ho
  · have kT : Keep chRegs s₀ t := ⟨hT.regs, hT.rd, hT.wr⟩
    exact (Keep.trans k (Keep.trans kT k')).mono (by decide)

end VG.Proof.Bignum.X86_64.R2a
