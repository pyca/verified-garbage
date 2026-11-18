module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Region
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ZCore
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub

/-! ### `Bignum.X86_64.Ifma.Glue`, which this module and modules that import it used -/

section

/-!
# RSA with AVX512_IFMA on x86-64, any size: from the regions back to the workspaces

`result_ok`: the `4 R` limbs of `Y` at prime
`p`'s region, below `2 X`, into `W + 1` 64-bit words at `aAcc` (`to64`),
and `aY := Y mod X` by a conditional subtraction (`subMod`, `selectAcc`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64 (csub_fin)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The ranges `result` writes in the prime's workspace. -/
def resRanges (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Nat × Nat) :=
  [(slot l.W Public.aAcc, 8 * (l.W + 2)), (slot l.W Public.aTmp, 8 * (l.W + 2)), (slot l.W Public.aY, 8 * (l.W + 2))]

/-- `result`'s block: `Y`'s seventeen words at `aAcc`, and the bases for the subtraction. -/
theorem resBlock_ok (hl : AmmOk l) {s : State} {B : Addr} {Z o a p : Nat} {mx : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B o) (hH : Hdr s.mem (off B o) l.W mx)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot l.W 8 ≤ a)
    (haZ : a + l.nl * l.D + 8 ≤ Z) (hp : p < l.nl)
    (hL : ∀ j < l.L, limb l s.mem (off B a) (l.D * p + l.oY) j < 2 ^ 52)
    (hV : val52 l s.mem (off B a) (l.D * p + l.oY) < 2 * wv s.mem (off B o) (slot l.W Public.aN) l.W) :
    WP isa (.block (([.mov .r11 (.mem (hdr sIfma)), .alu .add .r11 (.imm (BitVec.ofNat 32 (l.D * p + l.oY))),
        .mov .r8 (.mem (hdr (sArr Public.aAcc)))] : List Instr) ++ to64 l ++
      ([.mov .rbx (.mem (hdr (sArr Public.aY))), .mov .r10 (.mem (hdr (sArr Public.aN))), .mov .r12 (.mem (hdr sW)),
        .mov .rsi (.mem (hdr (sArr Public.aTmp)))] : List Instr))) s fun t =>
      wv t.mem (off B o) (slot l.W Public.aAcc) (l.W + 1) = val52 l s.mem (off B a) (l.D * p + l.oY) ∧
      Outside (off B o) (slot l.W Public.aAcc) (8 * (l.W + 1)) s.mem t.mem ∧
      t.gpr .r8 = off (off B o) (slot l.W Public.aAcc) ∧ t.gpr .rbx = off (off B o) (slot l.W Public.aY) ∧
      t.gpr .r10 = off (off B o) (slot l.W Public.aN) ∧ t.gpr .r12 = BitVec.ofNat 64 l.W ∧
      t.gpr .rsi = off (off B o) (slot l.W Public.aTmp) ∧
      Keep [.r11, .r8, .rax, .rcx, .rbp, .rbx, .r10, .r12, .rsi] s t := by
  obtain hS8 : slot l.W 8 = 256 + 64 * (l.W + 2) := by unfold slot hdrBytes; omega_using []
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_boundsN hl
  obtain hDp : l.D * p ≤ l.D ∧ l.D * p + l.D ≤ l.nl * l.D ∧ l.nl * l.D ≤ 2 * l.D := ⟨D_le hl hp, lane_end hl hp, (nlD_le hl).2⟩
  obtain h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain lA := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
  obtain hA0 := hdr_lt_slot l.W Public.aAcc (show 31 < 32 by decide)
  obtain hH' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega_using [hoa, hS8, haZ, this])
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r8] (Q := fun t => t.gpr .r11 = off (off B a) (l.D * p + l.oY) ∧
    t.gpr .r8 = off (off B o) (slot l.W Public.aAcc) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hH' sIfma (by decide), hH' (sArr Public.aAcc) (by decide),
      AmmSym.se_ofNat (show l.D * p + l.oY < 2 ^ 31 by omega_using [o2, hDb2, hDp])]
    and_intros
    · exact congrArg (· + BitVec.ofNat 64 (l.D * p + l.oY)) hia
    · exact hH.harr _ (by decide)) rfl) fun s₁ ⟨⟨r11, r8, me⟩, k₁⟩ => ?_
  obtain hsep : ∀ m m' : Mem, Outside (off (off B o) (slot l.W Public.aAcc)) 0 (8 * (l.W + 1)) m m' → ∀ j < l.L,
      word m' (off (off B a) (l.D * p + l.oY)) (l.off j) = word m (off (off B a) (l.D * p + l.oY)) (l.off j) :=
    fun m m' ho j hj => by
    have := off_ltN hl hj
    obtain f := Frm.of_outside_off (B := B) (by rw [off_off] at ho; exact ho) (by omega_using [hoa, hS8, haZ, hn, lA])
        (by omega_using [hoa, hS8, haZ, hn, lA])
    rw [word_off, word_off, word_off, word_off]
    exact f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only; omega_using [hoa, hS8, lA]))
        (by omega_using [haZ, hn, o2, o10, hDp, this])
  refine WP.mono (to64_ok r11 r8 (fun j hj => by
      have := off_ltN hl hj
      rw [k₁.2.1, k₁.2.2, off_off, AmmSym.off_add]; exact hs.ld (by omega_using [haZ, o2, o10, hDp, this]))
    (fun w hw => by rw [k₁.2.2, off_off, AmmSym.off_add]; exact hs.st (by omega_using [hoa, hS8, haZ, lA, hw]))
    (fun j hj => by rw [me, word_off]; exact hL j hj) (by omega_using [hW2]) hsep) fun s₂ ⟨hw₂, ho₂, k₂, _⟩ => ?_
  obtain hlv : VG.Proof.Bignum.Amm52.lval (fun j => (limbsAt l s₁.mem (off (off B a) (l.D * p + l.oY)) j).toNat) l.L =
      val52 l s.mem (off B a) (l.D * p + l.oY) := VG.Proof.Bignum.Amm52.lval_congr fun j hj => by
    simp only [limbsAt, hj, ↓reduceIte]
    rw [me, word_off]
  rw [hlv] at hw₂
  obtain hacc := wv_to64_lt hV hw₂
  rw [me] at ho₂
  obtain f₂ := Frm.of_outside_off (B := B) (by rw [off_off] at ho₂; exact ho₂) (by omega_using [hoa, hS8, haZ, hn, lA])
      (by omega_using [hoa, hS8, haZ, hn, lA])
  obtain hh : ∀ i < 32, word s₂.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi => by
    have := hdr_lt_slot l.W Public.aAcc hi
    rw [word_off, word_off]
    exact f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_using [this]))
        (by omega_using [hoa, hS8, haZ, hn, lA, this])
  obtain hH₂ : Hdr s₂.mem (off B o) l.W mx := ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega_using [hj])).trans (hH.harr j hj)⟩
  obtain hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hH' i hi
  obtain hdi₂ : s₂.gpr .rdi = off B o := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]; exact hdi
  refine WP.mono (WP.keep [.rbx, .r10, .r12, .rsi] (Q := fun t =>
    t.gpr .rbx = off (off B o) (slot l.W Public.aY) ∧ t.gpr .r10 = off (off B o) (slot l.W Public.aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 l.W ∧ t.gpr .rsi = off (off B o) (slot l.W Public.aTmp) ∧ t.mem = s₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ (sArr Public.aY) (by decide), hl₂ (sArr Public.aN) (by decide),
      hl₂ sW (by decide), hl₂ (sArr Public.aTmp) (by decide)]
    and_intros
    · exact hH₂.harr _ (by decide)
    · exact hH₂.harr _ (by decide)
    · exact hH₂.hw
    · exact hH₂.harr _ (by decide)) rfl) fun t ⟨⟨bx, r10, r12, si, me₃⟩, k₃⟩ => ?_
  rw [wv_off, Nat.add_zero] at hacc
  refine ⟨by rw [me₃]; exact hacc, by rw [me₃]; exact AmmSym.Outside.rebase ho₂ (by omega_using [hoa, hS8, haZ, hn, lA]) (by omega_using [hoa, hS8, haZ, hn, lA]), by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact r8,
    bx, r10, r12, si, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `result p`: `aY := Y mod X` in the prime's workspace `off B o` (16
words, `aN = X`), `Y` the limbs at `l.oY` of region `p` of the area `off B a`. -/
theorem result_ok (hl : AmmOk l) {s : State} {B : Addr} {Z o a p X : Nat} {mx : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B o) (hH : Hdr s.mem (off B o) l.W mx)
    (hia : word s.mem (off B o) (8 * sIfma) = off B a) (hoa : o + slot l.W 8 ≤ a)
    (haZ : a + l.nl * l.D + 8 ≤ Z) (hp : p < l.nl) (hN : wv s.mem (off B o) (slot l.W Public.aN) l.W = X)
    (hL : ∀ j < l.L, limb l s.mem (off B a) (l.D * p + l.oY) j < 2 ^ 52)
    (hV : val52 l s.mem (off B a) (l.D * p + l.oY) < 2 * X) :
    WP isa (seqs (result l p)) s fun t =>
      wv t.mem (off B o) (slot l.W Public.aY) l.W = val52 l s.mem (off B a) (l.D * p + l.oY) % X ∧
      Frm B (shiftRanges o (resRanges l)) s.mem t.mem ∧ t.gpr .rdi = s.gpr .rdi ∧ Keep mmRegs s t := by
  obtain hS8 : slot l.W 8 = 256 + 64 * (l.W + 2) := by unfold slot hdrBytes; omega_using []
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_boundsN hl
  obtain hDp : l.D * p ≤ l.D ∧ l.D * p + l.D ≤ l.nl * l.D ∧ l.nl * l.D ≤ 2 * l.D := ⟨D_le hl hp, lane_end hl hp, (nlD_le hl).2⟩
  obtain h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain lA := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
  obtain lT := slot_le (w := l.W) (show Public.aTmp < 8 by decide)
  obtain lY := slot_le (w := l.W) (show Public.aY < 8 by decide)
  obtain lN := slot_le (w := l.W) (show Public.aN < 8 by decide)
  obtain sAT := slot_sep (w := l.W) (show Public.aAcc ≠ Public.aTmp by decide)
  obtain sAY := slot_sep (w := l.W) (show Public.aAcc ≠ Public.aY by decide)
  obtain sTY := slot_sep (w := l.W) (show Public.aTmp ≠ Public.aY by decide)
  obtain sTN := slot_sep (w := l.W) (show Public.aTmp ≠ Public.aN by decide)
  obtain hA0 := hdr_lt_slot l.W Public.aAcc (show 31 < 32 by decide)
  obtain hH' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega_using [hoa, hS8, haZ, this])
  obtain hT8 := hdr_lt_slot l.W Public.aTmp (show 31 < 32 by decide)
  unfold result
  simp only [seqs]
  refine WP.seq (WP.mono (resBlock_ok hl hs hdi hH hia hoa haZ hp hL (by rw [hN]; exact hV))
    fun s₁ ⟨hacc, ho₁, r8, bx, r10, r12, si, k₁⟩ => ?_)
  obtain hsW : Scr s₁ (off B o) (slot l.W 8) := (hs.congr k₁.2.2).sub (by omega_using [hoa, hS8, haZ]) (by omega_using [lN])
  obtain hN₁ : wv s₁.mem (off B o) (slot l.W Public.aN) l.W = X := by
    rw [ho₁.wv (by rcases slot_sep (w := l.W) (show Public.aAcc ≠ Public.aN by decide) with h | h <;> omega_using [h])
      (by omega_using [hoa, hS8, haZ, hn, lN])]; exact hN
  refine WP.seq (WP.mono (subMod_ok hsW r8 r10 si r12 (by omega_using [hW1]) (by omega_using [hW2])
      (by omega_using [lA]) (by omega_using [lN]) (by omega_using [lT])
    (by omega_using [sAT]) (by omega_using [sTN])) fun s₂ ⟨c, lt, hbp, hlt, hD₂, ho₂, k₂⟩ => ?_)
  obtain hsW₂ := hsW.congr k₂.2.2
  refine WP.mono (selectAcc_ok hsW₂ ((k₂.gpr (by decide)).trans r8) ((k₂.gpr (by decide)).trans si)
    ((k₂.gpr (by decide)).trans bx) ((k₂.gpr (by decide)).trans r12) hbp (by omega_using [hW1]) (by omega_using [hW2])
        (eo := slot l.W Public.aY)
    (by omega_using [lA]) (by omega_using [lT]) (by omega_using [lY]) (by omega_using [sAY])
        (by omega_using [sTY])) fun t ⟨hv, ho₃, k₃⟩ => ?_
  obtain hA₂ : wv s₂.mem (off B o) (slot l.W Public.aAcc) l.W = wv s₁.mem (off B o) (slot l.W Public.aAcc) l.W :=
    ho₂.wv (by omega_using [sAT]) (by omega_using [hoa, hS8, haZ, hn, lA])
  rw [wv] at hacc
  rw [hN₁] at hD₂
  obtain hX := VG.Proof.Bignum.wv_lt s.mem (off B o) (slot l.W Public.aN) l.W
  rw [hN] at hX
  obtain hDl := VG.Proof.Bignum.wv_lt s₂.mem (off B o) (slot l.W Public.aTmp) l.W
  obtain hTl := VG.Proof.Bignum.wv_lt s₁.mem (off B o) (slot l.W Public.aAcc) l.W
  -- The powers in these facts use core's `instPowNat`; say so, or `generalize` evaluates `2 ^ 1024`.
  generalize @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64 * l.W) = R
    at hacc hD₂ hX hDl hTl
  obtain hres := csub_fin hX hDl hTl (Bool.toNat_le c) hacc hV hD₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hv, hA₂, hlt, ← hres]
    by_cases h : (word s₁.mem (off B o) (slot l.W Public.aAcc + 8 * l.W)).toNat < c.toNat <;> simp [h]
  · refine (((Frm.of_outside_off ho₁ (by omega_using [hoa, hS8, haZ, hn]) (by omega_using [hoa, hS8, haZ, hn, lA])).append
      (Frm.of_outside_off ho₂ (by omega_using [hoa, hS8, haZ, hn]) (by omega_using [hoa, hS8, haZ, hn, lT]))).append
      (Frm.of_outside_off ho₃ (by omega_using [hoa, hS8, haZ, hn]) (by omega_using [hoa, hS8, haZ, hn, lY]))).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨_, List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩, by simp only; omega_using []⟩
    · exact ⟨_, List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩, by simp only; omega_using []⟩
    · exact ⟨_, List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl⟩,
        by simp only; omega_using []⟩
  · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
  · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-! ## The area's base -/

/-- `ifma`'s first block: the area after `q`'s workspace and table, its base
into both primes' `sIfma`, and into `p`'s workspace. -/
theorem ifmaHead_ok (hl : AmmOk l) {s : State} {B : Addr} {Z w op oq : Nat} {minv mq : BitVec 64} (hg : VG.Proof.Bignum.X86_64.Good s B Z w minv)
    (hlo : slot w 8 ≤ op) (hpq : op + slot l.W 8 + wsTab l.W ≤ oq)
    (haZ : oq + slot l.W 8 + wsTab l.W + l.nl * l.D + 8 ≤ Z)
    (hsp : word s.mem B (8 * sWsP) = off B op) (hsq : word s.mem B (8 * sWsQ) = off B oq)
    (hwsq : WsAt s.mem B oq l.W mq) :
    WP isa (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))) s fun t =>
      t.mem = (s.mem.writeW (off (off B op) (8 * sIfma)) (off (off B oq) (slot l.W 8 + wsTab l.W))).writeW
        (off (off B oq) (8 * sIfma)) (off (off B oq) (slot l.W 8 + wsTab l.W)) ∧
      t.gpr .rdi = off B op ∧ Keep [.rax, .rdx, .rdi] s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_boundsN hl
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_using [haZ, hT, hi])
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = off B oq ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sWsQ (by decide), hsq]) rfl) fun s₁ ⟨⟨dx₁, me₁⟩, k₁⟩ => ?_
  refine WP.mono (wsEndT_ok (X := off B oq) (Z := slot l.W 8 + wsTab l.W) (wx := l.W)
    ((hs.congr k₁.2.2).sub (by omega_using [haZ]) (by omega_using [hT])) dx₁ (by rw [me₁]; exact hwsq.hdr.hw)
    (by rw [me₁]; exact hwsq.hdr.harr _ (by decide)) (by omega_using [])) fun s₂ ⟨ax₂, me₂, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain hdi₂ : s₂.gpr .rdi = B := by rw [k12.gpr (by decide)]; exact hg.rdi
  obtain hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  obtain hst : ∀ o, o + 8 * 30 ≤ Z → InRegions s₂.wr (off (off B o) (8 * sIfma)) 8 := fun o ho => by
    rw [k12.2.2, off_off]; exact hs.st (by unfold sIfma sFn; omega_using [ho])
  obtain hm₂ : s₂.mem = s.mem := me₂.trans me₁
  obtain hq' : (s.mem.writeW (off (off B op) (8 * sIfma)) (off (off B oq) (slot l.W 8 + wsTab l.W))).readW
      (off B (8 * sWsQ)) 64 = off B oq := by
    rw [off_off]
    have := (writeW_outside s.mem B (d := op + 8 * sIfma) (off (off B oq) (slot l.W 8 + wsTab l.W))
      (by unfold sIfma sFn; omega_using [hpq, haZ, hn, hT])).word (d := 8 * sWsQ) (.inl (by unfold sWsQ sFn; omega_using [hlo, h8]))
      (by unfold sWsQ sFn; omega_using [])
    exact this.trans hsq
  refine WP.mono (WP.keep [.rdx, .rdi] (Q := fun t =>
    t.mem = (s.mem.writeW (off (off B op) (8 * sIfma)) (off (off B oq) (slot l.W 8 + wsTab l.W))).writeW
      (off (off B oq) (8 * sIfma)) (off (off B oq) (slot l.W 8 + wsTab l.W)) ∧ t.gpr .rdi = off B op) (by
    xrun [State.ea, hdr, ws, enterP, hdi₂, hdrOff, hl₂ sWsP (by decide), hl₂ sWsQ (by decide), hm₂, hsp, ax₂,
      hst op (by omega_using [hpq, haZ, hT]), hst oq (by omega_using [haZ, hT]), hq']
    show word _ B (8 * sWsP) = off B op
    obtain e1 := (writeW_outside s.mem B (d := op + 8 * sIfma) (off (off B oq) (slot l.W 8 + wsTab l.W))
      (by unfold sIfma sFn; omega_using [hpq, haZ, hn, hT])).word (d := 8 * sWsP) (.inl
          (by unfold sWsP sFn; omega_using [hlo, h8])) (by unfold sWsP sFn; omega_using [])
    obtain e2 := (writeW_outside (s.mem.writeW (off B (op + 8 * sIfma)) (off (off B oq) (slot l.W 8 + wsTab l.W))) B
      (d := oq + 8 * sIfma) (off (off B oq) (slot l.W 8 + wsTab l.W))
      (by unfold sIfma sFn; omega_using [haZ, hn, hT])).word (d := 8 * sWsP) (.inl
          (by unfold sWsP sFn; omega_using [hpq, hT])) (by unfold sWsP sFn; omega_using [])
    rw [off_off B op, off_off B oq (8 * sIfma), e2, e1]
    exact hsp) rfl) fun t ⟨⟨me, di⟩, k₃⟩ => ?_
  exact ⟨me, di, (k12.trans k₃).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.Ifma

end

end

/-!
# RSA with AVX512_IFMA on x86-64, any size: `ifma`

`ifma_ok`: the IFMA area after `q`'s workspace,
both regions, the vector code, and the results back in the primes'
workspaces. `IMem` gathers what holds throughout; `IMem.of_frm` keeps it
across any change within `ifmaR`, the ranges `ifma` writes.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64 (two)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The ranges `ifma` writes, but its first two stores. -/
def ifmaR (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (op oq a : Nat) : List (Nat × Nat) :=
  shiftRanges op (k1Ranges l.W ++ (resRanges l)) ++ shiftRanges oq (k1Ranges l.W ++ (resRanges l)) ++ [(a, 2 * l.D + 8)]

/-- What `ifma` keeps, but the area's base in the primes' headers. -/
structure IPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (w op oq : Nat) (minv mp mq mk : BitVec 64) (P Q : Nat) (ep eq : Addr)
    (lp lq : Nat) : Prop where
  nh : Hdr m B w minv
  wsP : word m B (8 * sWsP) = off B op
  wsQ : word m B (8 * sWsQ) = off B oq
  pws : WsAt m B op l.W mp
  qws : WsAt m B oq l.W mq
  pn : wv m (off B op) (slot l.W Public.aN) l.W = P
  pinv : ((word m (off B op) (slot l.W Public.aN)).toNat * mp.toNat + 1) % 2 ^ 64 = 0
  pone : wv m (off B op) (slot l.W Public.aOne) l.W = 1
  qn : wv m (off B oq) (slot l.W Public.aN) l.W = Q
  qinv : ((word m (off B oq) (slot l.W Public.aN)).toNat * mq.toNat + 1) % 2 ^ 64 = 0
  qone : wv m (off B oq) (slot l.W Public.aOne) l.W = 1
  pmk : word m (off B op) (8 * sMaskX) = mk
  dp : word m B (8 * sDp) = ep
  pl : word m B (8 * sPlen) = BitVec.ofNat 64 lp
  dq : word m B (8 * sDq) = eq
  ql : word m B (8 * sQlen) = BitVec.ofNat 64 lq

/-- What `ifma` keeps. -/
structure IMem (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (w op oq a : Nat) (minv mp mq mk : BitVec 64) (P Q : Nat) (ep eq : Addr)
    (lp lq : Nat) : Prop extends IPre l m B w op oq minv mp mq mk P Q ep eq lp lq where
  pia : word m (off B op) (8 * sIfma) = off B a
  qia : word m (off B oq) (8 * sIfma) = off B a

/-- What `IPre` reads: below `p`'s workspace, the first 29 slots of a
prime's header, and its modulus and one. -/
def IKept (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (op oq d n : Nat) : Prop :=
  d + n ≤ op ∨ (op ≤ d ∧ d + n ≤ op + 8 * 29) ∨ (d = op + slot l.W Public.aN ∧ n ≤ 8 * l.W) ∨
    (d = op + slot l.W Public.aOne ∧ n ≤ 8 * l.W) ∨ (oq ≤ d ∧ d + n ≤ oq + 8 * 29) ∨
    (d = oq + slot l.W Public.aN ∧ n ≤ 8 * l.W) ∨ (d = oq + slot l.W Public.aOne ∧ n ≤ 8 * l.W)

theorem ifmaR_disj {op oq a d n : Nat} (hpq : op + slot l.W 8 + wsTab l.W ≤ oq)
    (hqa : oq + slot l.W 8 + wsTab l.W ≤ a)
    (h : IKept l op oq d n ∨ (d = op + 8 * sIfma ∧ n = 8) ∨ (d = oq + 8 * sIfma ∧ n = 8)) :
    ∀ r ∈ ifmaR l op oq a, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain hs : ∀ j, slot l.W j = 256 + j * (8 * (l.W + 2)) := fun j => by unfold slot hdrBytes; omega_using []
  simp only [IKept, Public.aN, Public.aOne, hs, sIfma, sFn] at h
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, sCtr, sFn, hs,
    Public.aAcc, Public.aTmp, Public.aY, aT] at hpq hqa ⊢
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega_using [h, hpq, hqa]

theorem ifmaR_le {op oq a : Nat} (hpq : op + slot l.W 8 + wsTab l.W ≤ oq)
    (hqa : oq + slot l.W 8 + wsTab l.W ≤ a) : ∀ r ∈ ifmaR l op oq a, r.1 + r.2 ≤ a + 2 * l.D + 8 := by
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain hs : ∀ j, slot l.W j = 256 + j * (8 * (l.W + 2)) := fun j => by unfold slot hdrBytes; omega_using []
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, sCtr, sFn, hs,
    Public.aAcc, Public.aTmp, Public.aY, aT] at hpq hqa ⊢
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega_arith

theorem IPre.of_frm (hl : LayOk l) {m m' : Mem} {B : Addr} {w op oq : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (h : IPre l m B w op oq minv mp mq mk P Q ep eq lp lq) {rs : List (Nat × Nat)}
    (hf : Frm B rs m m') (hr : ∀ d n, IKept l op oq d n → ∀ r ∈ rs, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hlo : slot w 8 ≤ op) (hpq : op + slot l.W 8 + wsTab l.W ≤ oq) (hz : oq + slot l.W 8 ≤ 2 ^ 64) :
    IPre l m' B w op oq minv mp mq mk P Q ep eq lp lq := by
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have := slot_le (w := l.W) (show Public.aN < 8 by decide)
  have := slot_le (w := l.W) (show Public.aOne < 8 by decide)
  obtain hW : ∀ d, IKept l op oq d 8 → word m' B d = word m B d := fun d hk =>
    hf.word_eq (hr d 8 hk) (by unfold IKept at hk; omega_arith)
  obtain hV : ∀ d, IKept l op oq d (8 * l.W) → wv m' B d l.W = wv m B d l.W := fun d hk =>
    hf.wv_eq (hr d (8 * l.W) hk) (by unfold IKept at hk; omega_arith)
  obtain hn : ∀ i < 32, word m' B (8 * i) = word m B (8 * i) := fun i hi => hW _ (.inl (by omega_using [hlo, h8, hi]))
  obtain hp : ∀ i < 29, word m' (off B op) (8 * i) = word m (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inl ⟨by omega_using [], by omega_using [hi]⟩))
  obtain hq : ∀ i < 29, word m' (off B oq) (8 * i) = word m (off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hW _ (.inr (.inr (.inr (.inr (.inl ⟨by omega_using [], by omega_using [hi]⟩)))))
  refine ⟨⟨(hn _ (by decide)).trans h.nh.hw, (hn _ (by decide)).trans h.nh.hminv,
      fun j hj => (hn _ (by unfold sArr; omega_using [hj])).trans (h.nh.harr j hj)⟩,
    (hn _ (by decide)).trans h.wsP, (hn _ (by decide)).trans h.wsQ,
    h.pws.of_words fun i hi => hp i (by omega_using [hi]), h.qws.of_words fun i hi => hq i (by omega_using [hi]),
    ?_, ?_, ?_, ?_, ?_, ?_, (hp _ (by decide)).trans h.pmk, (hn _ (by decide)).trans h.dp,
    (hn _ (by decide)).trans h.pl, (hn _ (by decide)).trans h.dq, (hn _ (by decide)).trans h.ql⟩
  · rw [wv_off, hV _ (.inr (.inr (.inl ⟨rfl, Nat.le_refl _⟩))), ← wv_off]; exact h.pn
  · rw [word_off, hW _ (.inr (.inr (.inl ⟨rfl, by omega_using [hW1]⟩))), ← word_off]; exact h.pinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inl ⟨rfl, Nat.le_refl _⟩)))), ← wv_off]; exact h.pone
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, Nat.le_refl _⟩)))))), ← wv_off]; exact h.qn
  · rw [word_off, hW _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, by omega_using [hW1]⟩)))))), ← word_off]; exact h.qinv
  · rw [wv_off, hV _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, Nat.le_refl _⟩)))))), ← wv_off]; exact h.qone

theorem IMem.of_frm (hl : LayOk l) {m m' : Mem} {B : Addr} {w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (h : IMem l m B w op oq a minv mp mq mk P Q ep eq lp lq)
    (hf : Frm B (ifmaR l op oq a) m m') (hlo : slot w 8 ≤ op) (hpq : op + slot l.W 8 + wsTab l.W ≤ oq)
    (hqa : oq + slot l.W 8 + wsTab l.W ≤ a) (hz : a ≤ 2 ^ 64) :
    IMem l m' B w op oq a minv mp mq mk P Q ep eq lp lq := by
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_arith
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  refine ⟨h.toIPre.of_frm hl hf (fun d n hk => ifmaR_disj hpq hqa (.inl hk)) hlo hpq (by omega_using [hqa, hz]), ?_, ?_⟩
  · rw [word_off, hf.word_eq (ifmaR_disj hpq hqa (.inr (.inl ⟨rfl,
      rfl⟩))) (by unfold sIfma sFn; omega_using [hpq, hqa, hz, h16]), ← word_off]
    exact h.pia
  · rw [word_off, hf.word_eq (ifmaR_disj hpq hqa (.inr (.inr ⟨rfl, rfl⟩))) (by unfold sIfma sFn; omega_using [hqa, hz, h16]), ← word_off]
    exact h.qia

/-! ## `ifma`'s first half: the regions -/

/-- `ifma`'s first block, from `n`'s workspace to `p`'s. -/
theorem headI_ok (hl : LayOk l) {s : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : IPre l s.mem B w op oq minv mp mq mk P Q ep eq lp lq) (hlo : slot w 8 ≤ op)
    (hpq : op + slot l.W 8 + wsTab l.W ≤ oq) (ha : a = oq + slot l.W 8 + wsTab l.W) (haZ : a + 2 * l.D + 8 ≤ Z) :
    WP isa (.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))) s fun u =>
      IMem l u.mem B w op oq a minv mp mq mk P Q ep eq lp lq ∧
      Frm B [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] s.mem u.mem ∧ u.gpr .rdi = off B op ∧
      Keep [.rax, .rdx, .rdi] s u := by
  have hn := hs.nowrap
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  subst ha
  refine WP.mono (ifmaHead_ok hl ⟨hs, hdi, h.nh⟩ hlo hpq (by omega_using [haZ, hl.nlD]) h.wsP h.wsQ h.qws) fun u ⟨me, di, k⟩ => ?_
  obtain o1 := writeW_outside s.mem B (d := op + 8 * sIfma) (off (off B oq) (slot l.W 8 + wsTab l.W))
    (by unfold sIfma sFn; omega_using [hpq, hn, h16, haZ])
  obtain o2 := writeW_outside (s.mem.writeW (off B (op + 8 * sIfma)) (off (off B oq) (slot l.W 8 + wsTab l.W))) B
    (d := oq + 8 * sIfma) (off (off B oq) (slot l.W 8 + wsTab l.W)) (by unfold sIfma sFn; omega_using [hn, h16, haZ])
  rw [off_off B op, off_off B oq (8 * sIfma)] at me
  obtain f : Frm B [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] s.mem u.mem := by
    rw [me]
    exact (Frm.of_outside o1 (List.mem_cons_self ..)).trans
      (Frm.of_outside o2 (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain hia : off (off B oq) (slot l.W 8 + wsTab l.W) = off B (oq + slot l.W 8 + wsTab l.W) := by
    rw [off_off, Nat.add_assoc]
  refine ⟨⟨h.of_frm hl f (fun d n hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain hs : ∀ j, slot l.W j = 256 + j * (8 * (l.W + 2)) := fun j => by unfold slot hdrBytes; omega_using []
      simp only [IKept, hs, Public.aN, Public.aOne] at hk
      rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega_using [hpq, h16, hk, hT]) hlo hpq
      (by omega_using [hn, haZ]), ?_, ?_⟩, f, di, k⟩
  · rw [word_off, me, o2.word (.inl (by unfold sIfma sFn; omega_using [hpq, h16]))
      (by unfold sIfma sFn; omega_using [hpq, hn, h16, haZ]), ← hia]
    exact VG.Proof.Bignum.word_writeW_self _ _ _ _
  · rw [word_off, me, ← hia]
    exact VG.Proof.Bignum.word_writeW_self _ _ _ _

/-- From one workspace (`rdi = off B o`, linked to `B`) to the one in `n`'s slot `sl`. -/
theorem swapWs_ok {u : State} {B : Addr} {Z o o' sl : Nat} (hs : Scr u B Z) (hdi : u.gpr .rdi = off B o)
    (hlk : word u.mem (off B o) (8 * sLink) = B) (hsl : word u.mem B (8 * sl) = off B o') (hsl' : sl < 32)
    (ho : o + 8 * 32 ≤ Z) :
    WP isa (.block [leave, .mov .rdi (.mem (hdr sl))]) u fun u' =>
      u'.gpr .rdi = off B o' ∧ u'.mem = u.mem ∧ Keep [.rdi] u u' := by
  obtain hl : InRegions (u.rd ++ u.wr) (off (off B o) (8 * sLink)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega_using [ho])
  obtain hl' : InRegions (u.rd ++ u.wr) (off B (8 * sl)) 8 := hs.ld (by omega_using [hsl', ho])
  refine WP.mono (WP.keep [.rdi] (Q := fun u' => u'.gpr .rdi = off B o' ∧ u'.mem = u.mem) (by
    xrun [leave, State.ea, hdr, hdi, hdrOff, hl, hlk, hl', hsl]) rfl) fun u' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

theorem k1sh_lt (o : Nat) : ∀ r ∈ shiftRanges o (k1Ranges l.W), o + 8 * 30 ≤ r.1 ∧ r.1 + r.2 ≤ o + slot l.W 8 := by
  obtain hs : ∀ j, slot l.W j = 256 + j * (8 * (l.W + 2)) := fun j => by unfold slot hdrBytes; omega_using []
  simp only [shiftRanges, k1Ranges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    sCtr, sFn, hs, Public.aAcc, Public.aTmp, aT]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only <;> omega_using []

theorem k1sh_ifmaR (op oq a : Nat) {o : Nat} (ho : o = op ∨ o = oq) :
    ∀ r ∈ shiftRanges o (k1Ranges l.W), r ∈ ifmaR l op oq a := fun r hr => by
  simp only [ifmaR, shiftRanges, List.map_append, List.mem_append] at hr ⊢
  rcases ho with rfl | rfl
  · exact .inl (.inl (.inl hr))
  · exact .inl (.inr (.inl hr))

theorem regFr_ifmaR (hl : LayOk l) {op oq a o p : Nat} (ho : o = op ∨ o = oq) (hp : p < 2) :
    ∀ r ∈ shiftRanges o (k1Ranges l.W) ++ [(a + l.D * p, l.D)], ∃ r' ∈ ifmaR l op oq a,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun r hr => by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, k1sh_ifmaR op oq a ho r hr, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(a, 2 * l.D + 8), List.mem_append_right _ (List.mem_singleton_self _),
      by rw [List.mem_singleton.mp hr]; simp only; omega_using [hDp]⟩

/-- `ifma`'s first half: the area's base, and both regions. -/
theorem ifmaA_ok (hl : LayOk l) {s : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {ebp ebq : List Byte} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : IPre l s.mem B w op oq minv mp mq mk P Q ep eq ebp.length ebq.length) (hlo : slot w 8 ≤ op)
    (hpq : op + slot l.W 8 + wsTab l.W ≤ oq) (ha : a = oq + slot l.W 8 + wsTab l.W) (haZ : a + 2 * l.D + 8 ≤ Z)
    (hYp : wv s.mem (off B op) (slot l.W Public.aY) l.W < P) (hYq : wv s.mem (off B oq) (slot l.W Public.aY) l.W < Q)
    (hep : Src s B Z ep ebp) (heq : Src s B Z eq ebq) (hLp1 : 1 ≤ ebp.length) (hLp2 : ebp.length ≤ l.E)
    (hLq1 : 1 ≤ ebq.length) (hLq2 : ebq.length ≤ l.E) :
    WP isa (seqs (([.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))] : List (Prog isa)) ++ (region l 0 sDp sPlen ++
      (([.block [leave, enterQ]] : List (Prog isa)) ++ region l 1 sDq sQlen)))) s fun t =>
      IMem l t.mem B w op oq a minv mp mq mk P Q ep eq ebp.length ebq.length ∧
      RegOut l t.mem (off B a) 0 P (2 ^ l.dbls * wv s.mem (off B op) (slot l.W Public.aY) l.W % P)
        (wv s.mem (off B op) (slot l.W aXc) l.W) (wv s.mem (off B op) (slot l.W Public.aY) l.W)
        (wv s.mem (off B op) (slot l.W Public.aY) l.W) (mp &&& mask52) ebp ∧
      RegOut l t.mem (off B a) 1 Q (2 ^ l.dbls * wv s.mem (off B oq) (slot l.W Public.aY) l.W % Q)
        (wv s.mem (off B oq) (slot l.W aXc) l.W) (wv s.mem (off B oq) (slot l.W Public.aY) l.W) 1
        (mq &&& mask52) ebq ∧
      Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR l op oq a) s.mem t.mem ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ t.gpr .rdi = off B oq ∧ Keep (mmRegs ++ ([.rdi] : List Reg)) s t := by
  have hn := hs.nowrap
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain lY := slot_le (w := l.W) (show Public.aY < 8 by decide)
  obtain lC := slot_le (w := l.W) (show aXc < 8 by decide)
  obtain hY0 := hdr_lt_slot l.W Public.aY (show 31 < 32 by decide)
  obtain hC0 := hdr_lt_slot l.W aXc (show 31 < 32 by decide)
  -- The head.
  refine wp_seqs_append (by simp) (by simp [region, k1, copyArr]) (WP.mono
    (headI_ok hl hs hdi h hlo hpq ha haZ) fun u₁ ⟨m₁, f₁, d₁, k₁⟩ => ?_)
  obtain hf₁ : ∀ {d n}, d + n ≤ op + 8 * sIfma ∨ (op + 8 * sIfma + 8 ≤ d ∧ d + n ≤ oq + 8 * sIfma) ∨
      oq + 8 * sIfma + 8 ≤ d → ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], d + n ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_using [hpq, hd]
  obtain hYp₁ : wv u₁.mem (off B op) (slot l.W Public.aY) l.W = wv s.mem (off B op) (slot l.W Public.aY) l.W := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr
        (.inl ⟨by unfold sIfma sFn; omega_using [hY0], by omega_using [hpq, lY]⟩))) (by omega_arith)
  obtain hCp₁ : wv u₁.mem (off B op) (slot l.W aXc) l.W = wv s.mem (off B op) (slot l.W aXc) l.W := by
    rw [wv_off, wv_off]; exact f₁.wv_eq (hf₁ (.inr
        (.inl ⟨by unfold sIfma sFn; omega_using [hC0], by omega_using [hpq, lC]⟩))) (by omega_arith)
  obtain hZ₁ : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)], r.1 + r.2 ≤ Z := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sIfma, sFn] <;> omega_using [hpq, ha, haZ, lC, hC0]
  -- `p`'s region.
  refine wp_seqs_append (by simp [region, k1, copyArr]) (by simp) (WP.mono
    (region_ok hl (p := 0) (SubCtx.mk' (hs.congr k₁.2.2) m₁.nh m₁.pws d₁ hlo (by have := tabBytes_le_wsTab l.W; omega_using [hpq, ha, haZ, this])) m₁.pia
        (by omega_using [hpq, ha]) (by rw [hl.nlD]; exact haZ)
      (by rw [hl.nl]; decide) m₁.pn (by rw [hYp₁]; exact hYp) (by decide) (by decide) m₁.dp m₁.pl
      (hep.congr (InScr.of_frm f₁ hZ₁) k₁.2.1 k₁.2.2) hLp1 hLp2) fun u₂ ⟨rp, f₂, w₂, d₂, k₂⟩ => ?_)
  obtain f₂' := f₂.widen (regFr_ifmaR hl (oq := oq) (.inl rfl) (by decide))
  obtain m₂ := m₁.of_frm hl f₂' hlo hpq (by omega_using [ha]) (by omega_using [haZ, hl.nlD, hn])
  obtain F₂ : Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR l op oq a) s.mem u₂.mem :=
    (f₁.mono fun r hr => List.mem_append_left _ hr).trans (f₂'.mono fun r hr => List.mem_append_right _ hr)
  obtain hZF : ∀ r ∈ [(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR l op oq a, r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hZ₁ r hr
    · have := ifmaR_le hpq (by omega_using [ha]) r hr; omega_using [haZ, hl.nlD, this]
  -- To `q`'s workspace.
  refine wp_seqs_append (by simp) (by simp [region, k1, copyArr]) (WP.mono
    (swapWs_ok (o' := oq) (hs.congr (w₂.trans k₁.2.2)) d₂ m₂.pws.link m₂.wsQ (by decide) (by omega_using [hpq, ha, haZ, lC, hC0]))
    fun u₃ ⟨d₃, me₃, k₃⟩ => ?_)
  rw [← me₃] at m₂ F₂
  obtain hq₃ : ∀ j, j < 8 → j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ aT →
      wv u₃.mem (off B oq) (slot l.W j) l.W = wv s.mem (off B oq) (slot l.W j) l.W := fun j hj h1 h2 h3 => by
    have := slot_le (w := l.W) hj
    have := hdr_lt_slot l.W j (show 31 < 32 by decide)
    rw [wv_off, wv_off, me₃, f₂.wv_eq (fun r hr => ?_) (by omega_arith),
      f₁.wv_eq (hf₁ (.inr (.inr (by unfold sIfma sFn; omega_using [this])))) (by omega_arith)]
    rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := k1sh_lt op r hr; omega_using [hpq, this])
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_arith)
  obtain k₁₃ := (k₁.trans k₂).trans k₃
  -- `q`'s region.
  refine WP.mono (region_ok hl (p := 1) (SubCtx.mk' (hs.congr k₁₃.2.2) m₂.nh m₂.qws d₃ (by omega_using [hlo, hpq])
      (by have := tabBytes_le_wsTab l.W; omega_using [ha, haZ, this])) m₂.qia
    (by omega_using [ha]) (by rw [hl.nlD]; exact haZ) (by rw [hl.nl]; decide) m₂.qn (by rw [hq₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hYq)
    (by decide) (by decide) m₂.dq m₂.ql (heq.congr (InScr.of_frm F₂ hZF) k₁₃.2.1 k₁₃.2.2) hLq1 hLq2)
    fun t ⟨rq, f₄, w₄, d₄, k₄⟩ => ?_
  obtain f₄' := f₄.widen (regFr_ifmaR hl (op := op) (.inr rfl) (by decide))
  rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (0 : Nat) = 0)), hYp₁, hCp₁, ← me₃] at rp
  simp only [Nat.one_ne_zero, ↓reduceIte] at rq
  rw [hq₃ _ (by decide) (by decide) (by decide) (by decide),
    hq₃ _ (by decide) (by decide) (by decide) (by decide)] at rq
  refine ⟨m₂.of_frm hl f₄' hlo hpq (by omega_using [ha]) (by omega_using [haZ, hl.nlD, hn]),
      rp.of_frm hl f₄ (fun r hr => ?_) (by omega_using [haZ, hl.nlD, hn]), rq,
    F₂.trans (f₄'.mono fun r hr => List.mem_append_right _ hr), w₄.trans k₁₃.2.2, ?_, d₄,
    k₁₃.trans k₄ |>.mono (by decide)⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact .inr (by have := k1sh_lt oq r hr; omega_using [ha, this])
    · rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_using [])
  · rw [k₄.2.1, k₁₃.2.1]

/-! ## `ifma`'s second half: the vector code and the results -/

/-- The vector code, from `q`'s workspace: the base of the area into `rbx`. -/
theorem vecI_ok (hl : LayOk l) {t : State} {B : Addr} {Z w op oq a wp : Nat} {minv mp mq mk : BitVec 64} {P Q C : Nat}
    {ep eq : Addr} {ebp ebq : List Byte} {K : Prop} {Yp Xcp Yq Xcq : Nat} (hs : Scr t B Z)
    (hdi : t.gpr .rdi = off B oq) (hm : IMem l t.mem B w op oq a minv mp mq mk P Q ep eq ebp.length ebq.length)
    (haZ : a + 2 * l.D + 8 ≤ Z) (hqa : oq + slot l.W 8 ≤ a)
    (rp : RegOut l t.mem (off B a) 0 P (2 ^ l.dbls * Yp % P) Xcp Yp Yp (mp &&& mask52) ebp)
    (rq : RegOut l t.mem (off B a) 1 Q (2 ^ l.dbls * Yq % Q) Xcq Yq 1 (mq &&& mask52) ebq)
    (hwp : wp = l.W) (hPo : P % 2 = 1) (hQo : Q % 2 = 1) (hYp : Yp < P) (hYq : Yq < Q) (hXp : Xcp < P)
    (hXq : Xcq < Q) (vxp : K → Xcp % P = C * 2 ^ (64 * wp) % P) (vxq : K → Xcq % Q = C * 2 ^ (64 * wp) % Q)
    (vyp : K → Yp % P = 2 ^ (64 * wp) % P) (vyq : K → Yq % Q = 2 ^ (64 * wp) % Q)
    (hLp : ebp.length ≤ l.E) (hLq : ebq.length ≤ l.E) :
    WP isa (seqs [.block [.mov .rbx (.mem (hdr sIfma))], vec l]) t fun t' =>
      (GoodS l t'.mem (off B a) (two P Q) l.oY 0 ∧
        (K → val52 l t'.mem (off B a) (l.D * 0 + l.oY) % P = C ^ Spec.Rsa.os2ip ebp * Yp % P)) ∧
      (GoodS l t'.mem (off B a) (two P Q) l.oY 1 ∧
        (K → val52 l t'.mem (off B a) (l.D * 1 + l.oY) % Q = C ^ Spec.Rsa.os2ip ebq * 1 % Q)) ∧
      Outside (off B a) 0 (2 * l.D + 8) t.mem t'.mem ∧ t'.gpr .rdi = t.gpr .rdi ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr ∧ Keep mmRegs t t' := by
  have hn := hs.nowrap
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain h01 : ∀ p, p < l.nl → p = 0 ∨ p = 1 := fun p hp => by have := hl.nl; omega_using [hp, this]
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = off B a ∧ u.mem = t.mem ∧ u.mxcsr = t.mxcsr) (by
    obtain hl : InRegions (t.rd ++ t.wr) (off (off B oq) (8 * sIfma)) 8 := by
      rw [off_off]; exact hs.ld (by unfold sIfma sFn; omega_using [haZ, hl.nlD, hqa, h16])
    xrun [State.ea, hdr, hdi, hdrOff, hl, hm.qia]; and_intros; all_goals rfl) rfl) fun u ⟨⟨bx, me, mx⟩, k⟩ => ?_)
  obtain hmP := VG.Proof.Bignum.wv_lt t.mem (off B op) (slot l.W Public.aN) l.W
  obtain hmQ := VG.Proof.Bignum.wv_lt t.mem (off B oq) (slot l.W Public.aN) l.W
  rw [hm.pn, ← hwp] at hmP
  rw [hm.qn, ← hwp] at hmQ
  refine WP.mono (vecR_ok hl (M := two P Q) (K1 := two (2 ^ l.dbls * Yp % P) (2 ^ l.dbls * Yq % Q))
    (Xc := two Xcp Xcq) (Y := two Yp Yq) (Fin := two Yp 1) (x := fun _ => C) (mi := two mp mq) (Q := K)
    (e := two (Spec.Rsa.os2ip ebp) (Spec.Rsa.os2ip ebq))
    (w := wp) (R := 2 ^ (64 * wp)) hwp rfl bx ((hs.congr k.2.2).sub (by omega_using [haZ, hl.nlD]) (by omega_using []))
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.n; exact rq.n])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.k1; exact rq.k1])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.x; exact rq.x])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.y; exact rq.y])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.fin; exact rq.fin])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.k0; exact rq.k0])
    (fun p hp => by
      rcases h01 p hp with rfl | rfl
      · show (P % 2 ^ 64 * mp.toNat + 1) % 2 ^ 64 = 0
        rw [← hm.pn, VG.Proof.Bignum.wv_mod64 _ _ _ (by omega_using [hW1])]; exact hm.pinv
      · show (Q % 2 ^ 64 * mq.toNat + 1) % 2 ^ 64 = 0
        rw [← hm.qn, VG.Proof.Bignum.wv_mod64 _ _ _ (by omega_using [hW1])]; exact hm.qinv)
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hmP; exact hmQ])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hPo; exact hQo])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact Nat.mod_lt _ (by omega_using [hXp]); exact Nat.mod_lt _ (by omega_using [hXq])])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hXp; exact hXq])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [exact hYp; exact hYq])
    (fun p hp => by rcases h01 p hp with rfl | rfl <;> [show Yp < 2 * P; show 1 < 2 * Q] <;> omega_using [hYp, hXq])
    (fun hK p hp => by rcases h01 p hp with rfl | rfl <;> [exact vxp hK; exact vxq hK])
    (fun hK p hp => by rcases h01 p hp with rfl | rfl <;> [exact vyp hK; exact vyq hK])
    (fun hK p hp => by
      rcases h01 p hp with rfl | rfl
      · show 2 ^ l.dbls * Yp % P % P = 2 ^ l.dbls * 2 ^ (64 * wp) % P
        rw [Nat.mod_mod, Nat.mul_mod, vyp hK, ← Nat.mul_mod]
      · show 2 ^ l.dbls * Yq % Q % Q = 2 ^ l.dbls * 2 ^ (64 * wp) % Q
        rw [Nat.mod_mod, Nat.mul_mod, vyq hK, ← Nat.mul_mod])
    (fun p hp => by
      obtain lt8 : ∀ {eb : List Byte}, eb.length ≤ l.E → Spec.Rsa.os2ip eb < 2 ^ (8 * l.E) := fun h =>
        Nat.lt_of_lt_of_le (VG.Proof.Bignum.os2ip_lt _)
          (by rw [Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) h)
      rcases h01 p hp with rfl | rfl <;> [exact lt8 hLp; exact lt8 hLq])
    (fun p hp i hi => by rcases h01 p hp with rfl | rfl <;> rw [me] <;> [exact rp.d i hi; exact rq.d i hi]))
    fun t' ⟨hy, ho, hr, hrd, hwr, hmx⟩ => ?_
  refine ⟨⟨(hy 0 (by rw [hl.nl]; decide)).1, fun hK => ?_⟩, ⟨(hy 1 (by rw [hl.nl]; decide)).1, fun hK => ?_⟩, by rw [← me]; rw [hl.nlD] at ho; exact ho,
    by rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), k.gpr (by decide)], by rw [hrd, k.2.1],
    by rw [hwr, k.2.2], by rw [hmx, mx], ⟨fun r hrm => ?_, by rw [hrd, k.2.1], by rw [hwr, k.2.2]⟩⟩
  · exact (hy 0 (by rw [hl.nl]; decide)).2 hK
  · exact (hy 1 (by rw [hl.nl]; decide)).2 hK
  · have hn : ∀ r', r' ∈ mmRegs → r ≠ r' := fun r' h' h => hrm (h ▸ h')
    rw [hr r (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
      (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
      (hn _ (by decide)) (hn _ (by decide)), k.gpr (fun h => hn .rbx (by decide) (List.mem_singleton.mp h))]

/-- Back to `n`'s workspace. -/
theorem leaveB_ok {u : State} {B : Addr} {Z o : Nat} (hs : Scr u B Z) (hdi : u.gpr .rdi = off B o)
    (hlk : word u.mem (off B o) (8 * sLink) = B) (ho : o + 8 * 32 ≤ Z) :
    WP isa (.block [leave]) u fun u' => u'.gpr .rdi = B ∧ u'.mem = u.mem ∧ Keep [.rdi] u u' := by
  obtain hl : InRegions (u.rd ++ u.wr) (off (off B o) (8 * sLink)) 8 := by
    rw [off_off]; exact hs.ld (by unfold sLink sFn; omega_using [ho])
  refine WP.mono (WP.keep [.rdi] (Q := fun u' => u'.gpr .rdi = B ∧ u'.mem = u.mem) (by
    xrun [leave, State.ea, hdr, hdi, hdrOff, hl, hlk]) rfl) fun u' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- A region's `Y` after changes below the area. -/
theorem goodY_below (hl : LayOk l) {m m' : Mem} {B : Addr} {a p : Nat} {M : Nat → Nat} {rs : List (Nat × Nat)}
    (g : GoodS l m (off B a) M l.oY p) (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ a) (hp : p < 2)
    (hz : a + 2 * l.D ≤ 2 ^ 64) :
    GoodS l m' (off B a) M l.oY p ∧ val52 l m' (off B a) (l.D * p + l.oY) = val52 l m (off B a) (l.D * p + l.oY) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  obtain hq : ∀ q < l.L, limb l m' (off B a) (l.D * p + l.oY) q = limb l m (off B a) (l.D * p + l.oY) q :=
    fun q hq => by
      have := off_lt hl hq
      simp only [limb]
      rw [word_off, word_off, hf.word_eq (fun r hr' => .inr (by have := hr r hr'; omega_using [this]))
          (by omega_using [hz, o2, o10, hDp, this])]
  exact ⟨g.of_limbs (c := l.oY) hq, val52_of_limbs hq⟩

theorem resSh_lt (o : Nat) : ∀ r ∈ shiftRanges o (resRanges l), o + 8 * 32 ≤ r.1 ∧ r.1 + r.2 ≤ o + slot l.W 8 := by
  obtain hs : ∀ j, slot l.W j = 256 + j * (8 * (l.W + 2)) := fun j => by unfold slot hdrBytes; omega_using []
  simp only [shiftRanges, resRanges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, hs,
    Public.aAcc, Public.aTmp, Public.aY]
  rintro _ (rfl | rfl | rfl) <;> simp only <;> omega_using []

theorem resSh_ifmaR (op oq a : Nat) {o : Nat} (ho : o = op ∨ o = oq) :
    ∀ r ∈ shiftRanges o (resRanges l), r ∈ ifmaR l op oq a := fun r hr => by
  simp only [ifmaR, shiftRanges, List.map_append, List.mem_append] at hr ⊢
  rcases ho with rfl | rfl
  · exact .inl (.inl (.inr hr))
  · exact .inl (.inr (.inr hr))

/-- The results, from `q`'s workspace: `aY := Y mod X` in both, then back to `n`'s. -/
theorem resI_ok (hl : LayOk l) {t : State} {B : Addr} {Z w op oq a : Nat} {minv mp mq mk : BitVec 64} {P Q : Nat}
    {ep eq : Addr} {lp lq : Nat} (hs : Scr t B Z) (hdi : t.gpr .rdi = off B oq)
    (hm : IMem l t.mem B w op oq a minv mp mq mk P Q ep eq lp lq) (hlo : slot w 8 ≤ op)
    (hpq : op + slot l.W 8 + wsTab l.W ≤ oq) (hqa : oq + slot l.W 8 + wsTab l.W ≤ a) (haZ : a + 2 * l.D + 8 ≤ Z)
    (gp : GoodS l t.mem (off B a) (two P Q) l.oY 0) (gq : GoodS l t.mem (off B a) (two P Q) l.oY 1) :
    WP isa (seqs (result l 1 ++ (([.block [leave, enterP]] : List (Prog isa)) ++
      (result l 0 ++ ([.block [leave]] : List (Prog isa)))))) t fun t' =>
      IMem l t'.mem B w op oq a minv mp mq mk P Q ep eq lp lq ∧
      wv t'.mem (off B oq) (slot l.W Public.aY) l.W = val52 l t.mem (off B a) (l.D * 1 + l.oY) % Q ∧
      wv t'.mem (off B op) (slot l.W Public.aY) l.W = val52 l t.mem (off B a) (l.D * 0 + l.oY) % P ∧
      Frm B (ifmaR l op oq a) t.mem t'.mem ∧ t'.gpr .rdi = B ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      Keep (mmRegs ++ ([.rdi] : List Reg)) t t' := by
  have hn := hs.nowrap
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  obtain lY := slot_le (w := l.W) (show Public.aY < 8 by decide)
  obtain hY0 := hdr_lt_slot l.W Public.aY (show 31 < 32 by decide)
  -- `q`'s result.
  refine wp_seqs_append (by simp [result]) (by simp) (WP.mono (result_ok hl (p := 1) hs hdi hm.qws.hdr hm.qia
    (by omega_using [hqa]) (by rw [hl.nlD]; exact haZ) (by rw [hl.nl]; decide) hm.qn gq.lt gq.v) fun t₁ ⟨vq, f₁, d₁, k₁⟩ => ?_)
  obtain m₁ := hm.of_frm hl (f₁.mono (resSh_ifmaR op oq a (.inr rfl))) hlo hpq hqa (by omega_using [haZ, hl.nlD, hn])
  obtain hs₁ := hs.congr k₁.2.2
  -- To `p`'s workspace.
  refine wp_seqs_append (by simp) (by simp [result]) (WP.mono (swapWs_ok (o' := op) hs₁ (d₁.trans hdi)
    m₁.qws.link m₁.wsP (by decide) (by omega_using [hqa, haZ, lY, hY0])) fun t₂ ⟨d₂, me₂, k₂⟩ => ?_)
  rw [← me₂] at m₁ vq
  obtain gp₂ := goodY_below hl gp (show Frm B _ t.mem t₂.mem by rw [me₂]; exact f₁)
      (fun r hr => by have := resSh_lt oq r hr; omega_using [hqa, this])
    (by decide) (by omega_using [haZ, hl.nlD, hn])
  obtain hs₂ := hs₁.congr k₂.2.2
  -- `p`'s result.
  refine wp_seqs_append (by simp [result]) (by simp) (WP.mono (result_ok hl (p := 0) hs₂ d₂ m₁.pws.hdr m₁.pia
    (by omega_using [hpq, hqa]) (by rw [hl.nlD]; exact haZ) (by rw [hl.nl]; decide) m₁.pn gp₂.1.lt gp₂.1.v) fun t₃ ⟨vp, f₃, d₃, k₃⟩ => ?_)
  obtain m₃ := m₁.of_frm hl (f₃.mono (resSh_ifmaR op oq a (.inl rfl))) hlo hpq hqa (by omega_using [haZ, hl.nlD, hn])
  -- Back to `n`'s workspace.
  refine WP.mono (leaveB_ok (hs₂.congr k₃.2.2) (d₃.trans d₂) m₃.pws.link (by omega_using [hpq, hqa, haZ, lY, hY0]))
      fun t' ⟨d₄, me₄, k₄⟩ => ?_
  rw [← me₄] at m₃ vp
  refine ⟨m₃, ?_, by rw [vp, gp₂.2], ?_, d₄, ?_, ?_, ?_⟩
  · rw [← vq, me₄, wv_off, wv_off, f₃.wv_eq (fun r hr => .inr (by have := resSh_lt op r hr; omega_using [hpq, this]))
      (by omega_using [hqa, haZ, hn, lY])]
  · rw [me₄]
    exact ((f₁.mono (resSh_ifmaR op oq a (.inr rfl))).trans (show Frm B _ t₁.mem t₃.mem by rw [← me₂]; exact f₃.mono (resSh_ifmaR op oq a (.inl rfl))))
  · rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [k₄.2.2, k₃.2.2, k₂.2.2, k₁.2.2]
  · exact (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)

/-! ## `ifma` -/

theorem ifma_eq : ifma l = (([.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))] : List (Prog isa)) ++ (region l 0 sDp sPlen ++
      (([.block [leave, enterQ]] : List (Prog isa)) ++ region l 1 sDq sQlen))) ++
    (([.block [.mov .rbx (.mem (hdr sIfma))], vec l] : List (Prog isa)) ++
      (result l 1 ++ (([.block [leave, enterP]] : List (Prog isa)) ++
        (result l 0 ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [ifma, List.append_assoc, List.cons_append, List.nil_append]

theorem ifmaA_mx (hl : LayOk l) : (seqs ((([.block (([.mov .rdx (.mem (hdr sWsQ))] : List Instr) ++ wsEndT ++
      ([.mov .rdx (.mem (hdr sWsP)), .store (ws .rdx sIfma) .rax, .mov .rdx (.mem (hdr sWsQ)),
        .store (ws .rdx sIfma) .rax, enterP] : List Instr))] : List (Prog isa)) ++ (region l 0 sDp sPlen ++
      (([.block [leave, enterQ]] : List (Prog isa)) ++ region l 1 sDq sQlen))))).allInstrs
      (fun i => !loadsMxcsr i) = true := by
  rcases hl with rfl | rfl | rfl | rfl <;> decide +kernel

theorem resI_mx (hl : LayOk l) : (seqs (result l 1 ++ (([.block [leave, enterP]] : List (Prog isa)) ++
      (result l 0 ++ ([.block [leave]] : List (Prog isa)))))).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases hl with rfl | rfl | rfl | rfl <;> decide +kernel

/-- `ifma`: `q`'s result `C^dq mod q` in its `aY`, `p`'s `C^dp R_p` in its. -/
theorem ifma_ok (hl : LayOk l) {s : State} {B : Addr} {Z w op oq a wp : Nat} {minv mp mq mk : BitVec 64} {P Q C : Nat}
    {ep eq : Addr} {ebp ebq : List Byte} {K : Prop} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h : IPre l s.mem B w op oq minv mp mq mk P Q ep eq ebp.length ebq.length) (hlo : slot w 8 ≤ op)
    (hpq : op + slot l.W 8 + wsTab l.W ≤ oq) (ha : a = oq + slot l.W 8 + wsTab l.W) (haZ : a + 2 * l.D + 8 ≤ Z)
    (hwp : wp = l.W) (hPo : P % 2 = 1) (hQo : Q % 2 = 1)
    (hYp : wv s.mem (off B op) (slot l.W Public.aY) l.W < P) (hYq : wv s.mem (off B oq) (slot l.W Public.aY) l.W < Q)
    (hXp : wv s.mem (off B op) (slot l.W aXc) l.W < P) (hXq : wv s.mem (off B oq) (slot l.W aXc) l.W < Q)
    (vxp : K → wv s.mem (off B op) (slot l.W aXc) l.W % P = C * 2 ^ (64 * wp) % P)
    (vxq : K → wv s.mem (off B oq) (slot l.W aXc) l.W % Q = C * 2 ^ (64 * wp) % Q)
    (vyp : K → wv s.mem (off B op) (slot l.W Public.aY) l.W % P = 2 ^ (64 * wp) % P)
    (vyq : K → wv s.mem (off B oq) (slot l.W Public.aY) l.W % Q = 2 ^ (64 * wp) % Q)
    (hep : Src s B Z ep ebp) (heq : Src s B Z eq ebq) (hLp1 : 1 ≤ ebp.length) (hLp2 : ebp.length ≤ l.E)
    (hLq1 : 1 ≤ ebq.length) (hLq2 : ebq.length ≤ l.E) :
    WP isa (seqs (ifma l)) s fun t =>
      IMem l t.mem B w op oq a minv mp mq mk P Q ep eq ebp.length ebq.length ∧
      wv t.mem (off B oq) (slot l.W Public.aY) l.W < Q ∧
      (K → wv t.mem (off B oq) (slot l.W Public.aY) l.W = C ^ Spec.Rsa.os2ip ebq % Q) ∧
      wv t.mem (off B op) (slot l.W Public.aY) l.W < P ∧
      (K → wv t.mem (off B op) (slot l.W Public.aY) l.W % P = C ^ Spec.Rsa.os2ip ebp * 2 ^ (64 * wp) % P) ∧
      Frm B ([(op + 8 * sIfma, 8), (oq + 8 * sIfma, 8)] ++ ifmaR l op oq a) s.mem t.mem ∧ t.gpr .rdi = B ∧
      Keep mmRegs s t ∧ t.mxcsr = s.mxcsr := by
  obtain hT : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  obtain h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  rw [ifma_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono_mx (ifmaA_mx hl) (ifmaA_ok hl hs hdi h hlo hpq ha haZ hYp hYq hep heq
    hLp1 hLp2 hLq1 hLq2) fun u ⟨mu, rp, rq, fu, wu, rdu, du, ku⟩ mxu => ?_)
  refine wp_seqs_append (by simp) (by simp [result]) (WP.mono (vecI_ok hl (K := K) (hs.congr wu) du mu haZ
    (by omega_using [ha]) rp rq hwp hPo hQo hYp hYq hXp hXq vxp vxq vyp vyq hLp2 hLq2)
    fun v ⟨⟨gp, vp⟩, ⟨gq, vq⟩, ov, dv, rdv, wrv, mxv, kv⟩ => ?_)
  obtain fv : Frm B (ifmaR l op oq a) u.mem v.mem :=
    (Frm.of_outside_off ov (by have := hs.nowrap; omega_using [haZ, hl.nlD, this])
        (by have := hs.nowrap; omega_using [haZ, hl.nlD, this])).widen fun r hr =>
      ⟨(a, 2 * l.D + 8), List.mem_append_right _ (List.mem_singleton_self _),
        by rw [List.mem_singleton.mp hr]; simp only; omega_using []⟩
  obtain mv := mu.of_frm hl fv hlo hpq (by omega_using [ha]) (by have := hs.nowrap; omega_using [haZ, hl.nlD, this])
  refine WP.mono_mx (resI_mx hl) (resI_ok hl ((hs.congr wu).congr wrv) (dv.trans du) mv hlo hpq (by omega_using [ha]) haZ gp gq)
    fun t ⟨mt, vqt, vpt, ft, dt, rdt, wrt, kt⟩ mxt => ?_
  obtain hQ0 : 0 < Q := by omega_using [hXq]
  obtain hP0 : 0 < P := by omega_using [hXp]
  refine ⟨mt, by rw [vqt]; exact Nat.mod_lt _ hQ0, fun hK => by rw [vqt, vq hK, Nat.mul_one],
    by rw [vpt]; exact Nat.mod_lt _ hP0,
    fun hK => by rw [vpt, Nat.mod_mod, vp hK, Nat.mul_mod, vyp hK, ← Nat.mul_mod],
    (fu.trans (fv.mono fun r hr => List.mem_append_right _ hr)).trans (ft.mono fun r hr => List.mem_append_right _ hr),
    dt, ⟨fun r hr => ?_, by rw [rdt, rdv, rdu], by rw [wrt, wrv, wu]⟩, by rw [mxt, mxv, mxu]⟩
  by_cases hrd : r = .rdi
  · subst hrd; rw [dt, hdi]
  · have hr' : r ∉ mmRegs ++ ([.rdi] : List Reg) := fun h =>
      (List.mem_append.mp h).elim hr fun h' => hrd (List.mem_singleton.mp h')
    rw [kt.gpr hr', kv.gpr hr, ku.gpr hr']

end VG.Proof.Bignum.X86_64.Ifma
