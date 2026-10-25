module
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep

/-!
# `R² mod m` by word steps with ADX: `t = x 2^64 + q̂ mc - q̂ R` in place

`R2Adx.mulSub` (`Impl/Bignum/X86_64/R2Adx.lean`) over `w` words of `x` (at
`rbx`) and `mc` (at `rsi`), four at a time (`tile`), the carries in the flags
within a tile and in registers between tiles: the high word in `r9`, `CF` as
the mask in `r14`, the previous word of `x` in `r8`. Through every word `i`
(`WI`): `T_i + 2^(64 i) (h + OF + CF + prev) = X_i 2^64 + q̂ C_i` for the low
`i` words `X_i` of `x`, `C_i` of `mc` and `T_i` of `t` (`mulSub_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2ax

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
  refine WP.mono (word_ok hI.scr tbx tsi hI.r15 (by omega_arith) (by omega_arith) hc ho d1 d2 d4 d5 d6 d7 d8 d9 d10 d11 d12
    d14 d15 d16) fun t' ⟨c', o', hc', ho', he, hhl', hnx, hm, k'⟩ => ?_
  have hxw : word t.mem B (ex + 8 * j + 8 * k) = word s₀.mem B (ex + 8 * (j + k)) := by
    rw [show ex + 8 * j + 8 * k = ex + 8 * (j + k) by omega_arith, hI.out.word (by omega_arith) (by omega_arith)]
  have hcw : word t.mem B (ec + 8 * j + 8 * k) = word s₀.mem B (ec + 8 * (j + k)) := by
    rw [show ec + 8 * j + 8 * k = ec + 8 * (j + k) by omega_arith, hI.out.word (by omega_arith) (by omega_arith)]
  have oo : Outside B (ex + 8 * (j + k)) 8 t.mem t'.mem := by
    rw [hm, show ex + 8 * j + 8 * k = ex + 8 * (j + k) by omega_arith]; exact writeW_outside _ _ _ (by omega_arith)
  refine ⟨hI.scr.congr k'.2.2, fun r hr => ?_, ?_, k'.2.1.trans hI.rd, k'.2.2.trans hI.wr, ?_,
    ⟨c', o', hc', ho', by have := Bool.toNat_le o'; omega_arith, ?_⟩,
    (hI.out.mono (Nat.le_refl _) (by omega_arith)).trans (oo.mono (by omega_arith) (by omega_arith))⟩
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
      have e := wv_writeW_top t.mem B ex (j + k) (word t'.mem B (ex + 8 * j + 8 * k)) (by omega_arith)
      rw [show ex + 8 * (j + k) = ex + 8 * j + 8 * k by omega_arith, ← hm] at e
      exact e
    rw [hT, hnx, hxw, wv_succ s₀.mem B ex, wv_succ s₀.mem B ec]
    rw [hcw, tdx] at he
    have p1 : 2 ^ (64 * (j + k + 1)) = 2 ^ (64 * (j + k)) * 2 ^ 64 := by
      rw [show 64 * (j + k + 1) = 64 * (j + k) + 64 by omega_arith, Nat.pow_add]
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
  · have := (t'.gpr .r9).isLt; simp only [Bool.toNat_false]; omega_arith
  · rw [hm, k.gpr (by decide), k.gpr (by decide), Nat.add_zero]
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [show (t.gpr .r9).toNat + c.toNat + (t.gpr .r8).toNat = (t.gpr .r9).toNat + 0 + c.toNat + (t.gpr .r8).toNat
      by omega_arith] at hv
    exact hv

/-- The carries out of the flags, and the next group (`inc = 4 g`): `ZF` after
the last of `N` tiles. -/
theorem groupTail_ok {s₀ t : State} {B : Addr} {Z ex ec w J g N : Nat} {inc : BitVec 32}
    (hI : WI s₀ B Z ex ec w (4 * J) (4 * J + 4 * g) .r8 .r9 t)
    (hinc : BitVec.signExtend 64 inc = BitVec.ofNat 64 (4 * g))
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N)) (hJ : J + g ≤ N) (hN : N < 2 ^ 60) :
    WP isa (.block ([.adox .r9 (.reg .rcx), .alu .sbb .r14 (.reg .r14), .alu .add .r15 (.imm inc),
      .alu .cmp .r15 (.reg .r12)] : List Instr)) t fun t' =>
      t'.zf = some (decide (J + g = N)) ∧ TI s₀ B Z ex ec w (J + g) t' := by
  obtain ⟨c, o, hc, ho, hb, hv⟩ := hI.val
  rw [show ([.adox .r9 (.reg .rcx), .alu .sbb .r14 (.reg .r14), .alu .add .r15 (.imm inc),
      .alu .cmp .r15 (.reg .r12)] : List Instr) = ([.adox .r9 (.reg .rcx)] : List Instr) ++
    ([.alu .sbb .r14 (.reg .r14), .alu .add .r15 (.imm inc), .alu .cmp .r15 (.reg .r12)] : List Instr) from rfl,
    WP.block_append_iff]
  refine WP.mono (adox_ok t (src := .reg .rcx) rfl (fun _ h => nomatch h) ho) fun t₁ ⟨o', ho₁, hc₁, e₁, k₁⟩ => ?_
  have hcx : (t.gpr .rcx).toNat = 0 := by rw [hI.rcx]; rfl
  have ho' : o' = false := by
    cases o'
    · rfl
    · simp only [Bool.toNat_true] at e₁; have := (t₁.gpr .r9).isLt; omega_arith
  subst ho'
  have h15 : t₁.gpr .r15 = BitVec.ofNat 64 (4 * J) := (k₁.gpr (by decide)).trans hI.r15
  have h12' : t₁.gpr .r12 = BitVec.ofNat 64 (4 * N) := (k₁.gpr (by decide)).trans ((hI.regs _ (by decide)).trans h12)
  have hadd : BitVec.ofNat 64 (4 * J) + BitVec.ofNat 64 (4 * g) = BitVec.ofNat 64 (4 * (J + g)) := by
    rw [BitVec.ofNat_add_ofNat]
    congr 1
    omega_arith
  have hcmp : (BitVec.ofNat 64 (4 * (J + g)) - BitVec.ofNat 64 (4 * N) == 0) = decide (J + g = N) := by
    rw [ofNat_sub_beq (by omega_arith) (by omega_arith)]; exact decide_eq_decide.mpr (by omega_arith)
  refine WP.mono (WP.keep [.r14, .r15] (Q := fun t' => t'.gpr .r14 = mask c ∧
      t'.gpr .r15 = BitVec.ofNat 64 (4 * (J + g)) ∧ t'.zf = some (decide (J + g = N)) ∧ t'.mem = t₁.mem) (by
    xrun [hc₁.trans hc, h15, h12', hinc]
    exact ⟨rfl, hadd, by rw [hadd]; exact hcmp⟩) rfl) fun t' ⟨⟨h14, h15', hz, hm⟩, k⟩ => ⟨hz, ?_⟩
  have hout : Outside B ex (8 * (4 * (J + g))) s₀.mem t'.mem := by
    rw [hm, k₁.2.1, show 4 * (J + g) = 4 * J + 4 * g by omega_arith]; exact hI.out
  refine ⟨hI.scr.congr (k.2.2.trans k₁.2.2.2), fun r hr => ?_, h15', k.2.1.trans (k₁.2.2.1.trans hI.rd),
    k.2.2.trans (k₁.2.2.2.trans hI.wr), ⟨c, h14, ?_⟩, hout⟩
  · rw [k.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (rfl | rfl) <;> exact hr (by decide)),
      k₁.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro rfl; exact hr (by decide)),
      hI.regs r hr]
  · have g9 : t'.gpr .r9 = t₁.gpr .r9 := k.gpr (by decide)
    have g8 : t'.gpr .r8 = t.gpr .r8 := (k.gpr (by decide)).trans (k₁.gpr (by decide))
    rw [hm, k₁.2.1, g9, g8]
    rw [hcx, Nat.add_zero] at e₁
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e₁
    rw [show 4 * (J + g) = 4 * J + 4 * g by omega_arith, e₁]
    omega_arith

/-- Tile `i` of a group at tile `J`: words `4 J + 4 i` to `4 J + 4 i + 3`. -/
theorem tileWords_ok {s₀ t : State} {B : Addr} {Z ex ec w J i : Nat}
    (hI : WI s₀ B Z ex ec w (4 * J) (4 * J + 4 * i) .r8 .r9 t)
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec) (hi : 4 * J + 4 * i + 4 ≤ w)
    (hX : ex + 8 * w ≤ Z) (hC : ec + 8 * w ≤ Z) (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa (.block (tileWords i)) t (WI s₀ B Z ex ec w (4 * J) (4 * J + 4 * (i + 1)) .r8 .r9) := by
  unfold tileWords
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (wstep (k := 4 * i) hI hbx hsi (by omega_arith) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wstep (k := 4 * i + 1) h₁ hbx hsi (by omega_arith) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wstep (k := 4 * i + 2) h₂ hbx hsi (by omega_arith) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₃ h₃ => ?_
  refine WP.mono (wstep (k := 4 * i + 3) h₃ hbx hsi (by omega_arith) hX hC sep (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₄ h₄ => ?_
  rwa [show 4 * J + (4 * i + 3) + 1 = 4 * J + 4 * (i + 1) by omega_arith] at h₄

/-- The `g` tiles of a group at tile `J`. -/
theorem groupWords_ok {s₀ t : State} {B : Addr} {Z ex ec w J : Nat}
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec)
    (hX : ex + 8 * w ≤ Z) (hC : ec + 8 * w ≤ Z) (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex) :
    ∀ g, 4 * J + 4 * g ≤ w → WI s₀ B Z ex ec w (4 * J) (4 * J + 0) .r8 .r9 t →
      WP isa (.block (groupWords g)) t (WI s₀ B Z ex ec w (4 * J) (4 * J + 4 * g) .r8 .r9)
  | 0, _, hI => WP.block_nil hI
  | g + 1, hg, hI => by
    rw [groupWords, WP.block_append_iff]
    exact WP.mono (groupWords_ok hbx hsi hX hC sep g (by omega_arith) hI) fun t' h' =>
      tileWords_ok h' hbx hsi (by omega_arith) hX hC sep

/-- A group of `g` tiles at tile `J` (`inc = 4 g`), and `ZF` after the last of `N`. -/
theorem group_ok {s₀ t : State} {B : Addr} {Z ex ec w J g N : Nat} {inc : BitVec 32} (hI : TI s₀ B Z ex ec w J t)
    (hinc : BitVec.signExtend 64 inc = BitVec.ofNat 64 (4 * g))
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N))
    (hw : w = 4 * N) (hJ : J + g ≤ N) (hN : N < 2 ^ 60) (hX : ex + 8 * w ≤ Z) (hC : ec + 8 * w ≤ Z)
    (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa (.block (group g inc)) t fun t' => t'.zf = some (decide (J + g = N)) ∧ TI s₀ B Z ex ec w (J + g) t' := by
  unfold group
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (head_ok hI) fun t₀ h₀ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (groupWords_ok hbx hsi hX hC sep g (by omega_arith) h₀) fun t₁ h₁ => groupTail_ok h₁ hinc h12 hJ hN

/-- Groups of `g` tiles, `N = g K` tiles in all. -/
theorem groups_ok {s₀ t : State} {B : Addr} {Z ex ec w g K N : Nat} {inc : BitVec 32}
    (h0 : TI s₀ B Z ex ec w 0 t) (hinc : BitVec.signExtend 64 inc = BitVec.ofNat 64 (4 * g))
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N))
    (hw : w = 4 * N) (hg : 0 < g) (hK : N = g * K) (hK0 : 0 < K) (hN : N < 2 ^ 60) (hX : ex + 8 * w ≤ Z)
    (hC : ec + 8 * w ≤ Z) (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa (.loop (.block (group g inc)) .ne) t (TI s₀ B Z ex ec w N) := by
  have e : ∀ i, g * i + g = N ↔ i + 1 = K := fun i => by
    rw [hK, ← Nat.mul_add_one]; exact Nat.mul_left_cancel_iff hg
  refine wp_upto (a := 0) (N := K) hK0 (fun i => TI s₀ B Z ex ec w (g * i)) (fun i _ hi _ hI => ?_)
    (fun _ h => by rw [hK]; exact h) (by rw [Nat.mul_zero]; exact h0)
  refine WP.mono (group_ok hI hinc hbx hsi h12 hw (by rw [hK, ← Nat.mul_add_one]; exact Nat.mul_le_mul_left g hi)
    hN hX hC sep) fun t' ⟨hz, hI'⟩ => ⟨by rw [hz]; exact congrArg some (decide_eq_decide.mpr (e i)), ?_⟩
  rw [Nat.mul_add_one]; exact hI'

/-- `wTest k`: ZF set iff `w` is a multiple of `k + 1 = 2^j`; the tiles' state kept. -/
theorem wTest_ok {s₀ t : State} {B : Addr} {Z ex ec w N j : Nat} {k : BitVec 32} (hI : TI s₀ B Z ex ec w N t)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64)
    (hk : (BitVec.signExtend 64 k).toNat = 2 ^ j - 1) :
    WP isa (.block (wTest k)) t fun t' => t'.zf = some (decide (w % 2 ^ j = 0)) ∧ TI s₀ B Z ex ec w N t' := by
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.regs _ (by decide)).trans h12
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (w % 2 ^ j = 0)) ∧ t'.mem = t.mem) (by
    unfold wTest
    xrun [t12]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have e := congrArg BitVec.toNat h
      rwa [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, hk, Nat.and_two_pow_sub_one_eq_mod] at e
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, hk, Nat.and_two_pow_sub_one_eq_mod, h]
      rfl) rfl) fun t' ⟨⟨hz, hm⟩, k'⟩ => ⟨hz, ?_⟩
  obtain ⟨c, h14, hv⟩ := hI.val
  refine ⟨hI.scr.congr k'.2.2, fun r hr => ?_, (k'.gpr (by decide)).trans hI.r15, k'.2.1.trans hI.rd,
    k'.2.2.trans hI.wr, ⟨c, (k'.gpr (by decide)).trans h14, ?_⟩, by rw [hm]; exact hI.out⟩
  · rw [k'.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro rfl; exact hr (by decide)),
      hI.regs r hr]
  · rw [hm, k'.gpr (by decide), k'.gpr (by decide)]; exact hv

/-- The tiles: the low `w = 4 N` words of `t`, in groups of 8, 4 or 1. -/
theorem tiles_ok {s₀ : State} {B : Addr} {Z ex ec w N : Nat} (h0 : TI s₀ B Z ex ec w 0 s₀)
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N))
    (hw : w = 4 * N) (hN0 : 0 < N) (hN : N < 2 ^ 60) (hX : ex + 8 * w ≤ Z) (hC : ec + 8 * w ≤ Z)
    (sep : ex + 8 * w ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa tiles s₀ (TI s₀ B Z ex ec w N) := by
  have h12w : s₀.gpr .r12 = BitVec.ofNat 64 w := by rw [h12, hw]
  unfold tiles
  refine WP.seq (WP.mono (wTest_ok (j := 5) h0 h12w (by omega_arith) rfl) fun t ⟨hz, hI⟩ => ?_)
  refine WP.ite (decide (w % 2 ^ 5 = 0)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_)
  · rw [decide_eq_true_eq] at h
    exact groups_ok (g := 8) (K := N / 8) hI (by rw [VG.Proof.MlKem.X86_64.sx32]; rfl) hbx hsi h12 hw (by decide) (by omega_arith) (by omega_arith) hN hX hC sep
  refine WP.seq (WP.mono (wTest_ok (j := 4) hI h12w (by omega_arith) rfl) fun t ⟨hz, hI⟩ => ?_)
  refine WP.ite (decide (w % 2 ^ 4 = 0)) (by simp only [eval, hz]) (fun h => ?_) (fun _ => ?_)
  · rw [decide_eq_true_eq] at h
    exact groups_ok (g := 4) (K := N / 4) hI (by rw [VG.Proof.MlKem.X86_64.sx16]; rfl) hbx hsi h12 hw (by decide) (by omega_arith) (by omega_arith) hN hX hC sep
  · exact groups_ok (g := 1) (K := N) hI (by rw [VG.Proof.MlKem.X86_64.sx4]; rfl) hbx hsi h12 hw (by decide) (by omega_arith) hN0 hN hX hC sep

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
  have hqd : q + d = 2 ^ 64 := by omega_arith
  generalize hA : P * (r8' + d) = A
  have e : T + A + q * P + W * c' = V + W := by
    rw [← h1, ← hA, hW, show r9 + c + r8 = r8' + 2 ^ 64 * c' by omega_arith, ← hqd]
    grind
  have hm := Nat.mod_add_div A W
  calc (T + A % W + q * P) % W = (T + A % W + q * P + W * (A / W)) % W := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (T + A + q * P) % W := by congr 1; omega_arith
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
    xrun [hea, (hs₂.congr k₃.2.2).st (show ex + 8 * (4 * N) + 8 ≤ Z by omega_arith), h8₃, hm₃]) rfl)
    fun t' ⟨hm, k'₀⟩ => ?_
  have k' : Keep [.r8] t₂ t' := (k₃.trans k'₀).mono (by decide)
  have hm₂ : t₂.mem = t.mem := k₂.2.1.trans hm₁
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, hm₂, wv_writeW_top _ _ _ _ _ (by omega_arith), BitVec.toNat_sub]
    rw [k₁.gpr (by decide), k₁.gpr (by decide)] at e₂
    have := (s₀.gpr .rdx).isLt
    rw [show (2 ^ 64 - (s₀.gpr .rdx).toNat + (t₂.gpr .r8).toNat) % 2 ^ 64 =
      ((t₂.gpr .r8).toNat + (2 ^ 64 - (s₀.gpr .rdx).toNat)) % 2 ^ 64 by rw [Nat.add_comm]]
    exact top_arith (P := 2 ^ (64 * (4 * N))) (by rw [← Nat.pow_add]; congr 1) (by omega_arith) hv e₂
  · rw [hm, hm₂]
    exact (hI.out.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · exact ((k₁.trans ⟨k₂.1, k₂.2.2⟩).trans k').mono (by decide)

/-- The tiles and the top word, from the start of a pass: `t + q̂ R ≡ x 2^64 + q̂ mc`. -/
theorem mulBody_ok {s₀ : State} {B : Addr} {Z w ex ec N : Nat} (hs : Scr s₀ B Z)
    (hbx : s₀.gpr .rbx = off B ex) (hsi : s₀.gpr .rsi = off B ec) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (h8 : s₀.gpr .r8 = 0) (h9 : s₀.gpr .r9 = 0) (h14 : s₀.gpr .r14 = 0) (h15 : s₀.gpr .r15 = 0)
    (hw : w = 4 * N) (hN0 : 0 < N) (hN : N < 2 ^ 60) (hX : ex + 8 * (w + 1) ≤ Z) (hC : ec + 8 * w ≤ Z)
    (sep : ex + 8 * (w + 1) ≤ ec ∨ ec + 8 * w ≤ ex) :
    WP isa (.seq tiles (.block mulTop)) s₀ fun t =>
      (wv t.mem B ex (w + 1) + (s₀.gpr .rdx).toNat * 2 ^ (64 * w)) % 2 ^ (64 * (w + 1)) =
        (wv s₀.mem B ex w * 2 ^ 64 + (s₀.gpr .rdx).toNat * wv s₀.mem B ec w) % 2 ^ (64 * (w + 1)) ∧
      Outside B ex (8 * (w + 1)) s₀.mem t.mem ∧ Keep chRegs s₀ t := by
  have c0 : s₀.gpr .r12 = BitVec.ofNat 64 (4 * N) := by rw [h12, hw]
  have h0 : TI s₀ B Z ex ec w 0 s₀ := ⟨hs, fun _ _ => rfl, h15, rfl, rfl,
    ⟨false, h14, by rw [h8, h9]; simp [wv]⟩, Outside.refl _ _ _ _⟩
  refine WP.seq (WP.mono (tiles_ok h0 hbx hsi c0 hw hN0 hN (by omega_arith) hC (by omega_arith)) fun t hT => ?_)
  refine WP.mono (mulTop_ok hT hbx h12 hX hw) fun t' ⟨hv, ho, k'⟩ => ⟨hv, ho, ?_⟩
  have kT : Keep chRegs s₀ t := ⟨hT.regs, hT.rd, hT.wr⟩
  exact (Keep.trans kT k').mono (by decide)

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
  refine WP.mono (mulBody_ok (hs.congr k.2.2) ((k.gpr (by decide)).trans hbx) hsi ((k.gpr (by decide)).trans h12)
    h8 h9 h14 h15 hw hN0 hN hX hC sep) fun t ⟨hv, ho, k'⟩ => ⟨?_, ?_, ?_⟩
  · rw [hdx, hm] at hv; exact hv
  · rw [← hm]; exact ho
  · exact (Keep.trans k k').mono (by decide)

end VG.Proof.Bignum.X86_64.R2ax
