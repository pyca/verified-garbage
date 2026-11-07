module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Ifma

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Out
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Win
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

-- separate module: the scalar limb chains, which build beside the vector code's proofs and change apart from them

/-!
# The IFMA Miller–Rabin round: numbers in limbs, by scalar code

The area at `B` (`rbx`), numbers of `L` limbs of 52 bits in the stride
layout (`limb`, `val52`): `addN`, `subN`, `selN`, `eqN`, and the doublings
modulo the modulus at offset 0 (`dbl1`, `dbls`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside mask Frm)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Bignum.X86_64.Ifma (limb val52)
open VG.Proof.Bignum.X86_64.Ifma.Pub (Mod)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52)
open VG.Impl.MillerRabin.X86_64.Ifma
open VG.Impl.Rsa.X86_64.CrtIfma (at_)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (writeW_outside word_writeW_self)
open VG.Proof.Bignum.X86_64.Ifma (off_ltN off_sepN eaG' and_mask')

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

open VG.Impl.Rsa.X86_64.PubIfma (pay1024 pay1536 pay2048 pay3072 pay4096) in
/-- The round's layouts: one lane, a candidate of 16, 24, 32, 48 or 64
words. -/
def MrOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop :=
  l = pay1024 ∨ l = pay1536 ∨ l = pay2048 ∨ l = pay3072 ∨ l = pay4096

theorem MrOk.amm (hl : MrOk l) : VG.Proof.Bignum.X86_64.Ifma.AmmOk l := by
  rcases hl with h | h | h | h | h
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr h))))
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))

theorem MrOk.nl (hl : MrOk l) : l.nl = 1 := by rcases hl with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The limbs of the number at offset `o` are below `2⁵²`. -/
def Canon (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (o : Nat) : Prop :=
  ∀ j < l.L, limb l m B o j < 2 ^ 52

/-- Two numbers whose bytes do not overlap. -/
def Sep (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o a : Nat) : Prop := o + l.NB ≤ a ∨ a + l.NB ≤ o


/-! ## Limbs through stores -/

/-- A word of the number at `a`, through a change outside the number at `o`. -/
theorem word_out (hl : MrOk l) {m m' : Mem} {B : Addr} {o a j : Nat} (f : Outside B o l.NB m m')
    (sep : Sep l o a) (ha : a + l.NB ≤ 2 ^ 63) (hj : j < l.L) :
    word m' B (a + l.off j) = word m B (a + l.off j) := by
  have := off_ltN hl.amm hj
  unfold Sep at sep
  exact f.word (by omega_arith) (by omega_arith)

/-- A store of limb `n` of the number at `o` changes only that number. -/
theorem out_wr (hl : MrOk l) (m : Mem) (B : Addr) {o n : Nat} (v : BitVec 64) (hn : n < l.L)
    (ho : o + l.NB ≤ 2 ^ 63) : Outside B o l.NB m (m.writeW (off B (o + l.off n)) v) := by
  have := off_ltN hl.amm hn
  exact (writeW_outside m B v (by omega_arith)).mono (by omega_arith) (by omega_arith)

/-- ... and none of its other limbs. -/
theorem word_wr_ne (hl : MrOk l) (m : Mem) (B : Addr) {o n j : Nat} (v : BitVec 64) (hn : n < l.L)
    (hj : j < l.L) (h : j ≠ n) (ho : o + l.NB ≤ 2 ^ 63) :
    word (m.writeW (off B (o + l.off n)) v) B (o + l.off j) = word m B (o + l.off j) := by
  have := off_ltN hl.amm hn
  have := off_ltN hl.amm hj
  have := off_sepN hl.amm hn hj h
  exact (writeW_outside m B v (by omega_arith)).word (by omega_arith) (by omega_arith)

/-- A chain of blocks, one per limb, by an invariant indexed by the limbs done. -/
theorem chain_ok {f : Nat → List Instr} {I : Nat → State → Prop} {N : Nat}
    (step : ∀ n < N, ∀ t, I n t → WP isa (.block (f n)) t (I (n + 1))) :
    ∀ n ≤ N, ∀ s, I 0 s → WP isa (.block ((List.range n).flatMap f)) s (I n) := by
  intro n
  induction n with
  | zero => intro _ s h; exact WP.block_nil h
  | succ n ih =>
    intro hn s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega_arith) s h) fun t ht => step n (by omega_arith) t ht

theorem add3 (c : Nat) (x y : BitVec 64) :
    BitVec.ofNat 64 c + x + y = BitVec.ofNat 64 (c + x.toNat + y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem shr52 {S : Nat} (h : S < 2 ^ 64) : BitVec.ofNat 64 S >>> 52 = BitVec.ofNat 64 (S / 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_arith)]

theorem mov32_ok {s : State} (r : Reg) :
    WP isa (.block [.mov32 r (.imm 0)]) s fun t =>
      t.gpr r = BitVec.ofNat 64 0 ∧ Keep [r] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  refine WP.block_cons_iff.2 ⟨s.setReg32 r 0, rfl, WP.block_nil ⟨?_, ⟨fun q hq => ?_, rfl, rfl⟩, rfl, rfl⟩⟩
  · rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl
  · rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (fun h => hq (by simp [h]))]

theorem mov32_1_ok {s : State} (r : Reg) :
    WP isa (.block [.mov32 r (.imm 1)]) s fun t =>
      t.gpr r = BitVec.ofNat 64 1 ∧ Keep [r] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  refine WP.block_cons_iff.2 ⟨s.setReg32 r 1, rfl, WP.block_nil ⟨?_, ⟨fun q hq => ?_, rfl, rfl⟩, rfl, rfl⟩⟩
  · rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl
  · rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (fun h => hq (by simp [h]))]

/-! ## `addN` -/

/-- Limb `j` of `addN`. -/
def addL (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o a b j : Nat) : List Instr :=
  [.alu .add .rdx (.mem (at_ .rbx (a + l.off j))), .alu .add .rdx (.mem (at_ .rbx (b + l.off j))),
    .mov .rax (.reg .rdx), .alu .and .rax (.reg .r12), .store (at_ .rbx (o + l.off j)) .rax,
    .shift .shr .rdx 52]

theorem addN_eq {o a b : Nat} :
    addN l o a b = ([.mov32 .rdx (.imm 0)] : List Instr) ++ (List.range l.L).flatMap (addL l o a b) := rfl

theorem addL_ok {t : State} {B : Addr} {o a b j c : Nat} (hB : t.gpr .rbx = B) (h12 : t.gpr .r12 = mask52)
    (hd : t.gpr .rdx = BitVec.ofNat 64 c)
    (ra : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (a + l.off j)) 8)
    (rb : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (b + l.off j)) 8)
    (wo : InRegions t.wr (B + BitVec.ofNat 64 (o + l.off j)) 8)
    (hc : c + (word t.mem B (a + l.off j)).toNat + (word t.mem B (b + l.off j)).toNat < 2 ^ 64) :
    WP isa (.block (addL l o a b j)) t fun t' =>
      t'.mem = t.mem.writeW (off B (o + l.off j)) (BitVec.ofNat 64
        ((c + (word t.mem B (a + l.off j)).toNat + (word t.mem B (b + l.off j)).toNat) % 2 ^ 52)) ∧
      t'.gpr .rdx = BitVec.ofNat 64
        ((c + (word t.mem B (a + l.off j)).toNat + (word t.mem B (b + l.off j)).toNat) / 2 ^ 52) ∧
      Keep [.rax, .rdx] t t' ∧ t'.mxcsr = t.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rdx] (Q := fun t' =>
    t'.mem = t.mem.writeW (off B (o + l.off j)) (BitVec.ofNat 64
        ((c + (word t.mem B (a + l.off j)).toNat + (word t.mem B (b + l.off j)).toNat) % 2 ^ 52)) ∧
      t'.gpr .rdx = BitVec.ofNat 64
        ((c + (word t.mem B (a + l.off j)).toNat + (word t.mem B (b + l.off j)).toNat) / 2 ^ 52) ∧
      t'.mxcsr = t.mxcsr) ?_ rfl) fun t' ⟨⟨m, d, x⟩, k⟩ => ⟨m, d, k, x⟩
  unfold addL
  xrun [eaG', hB, h12, hd, ra, rb, wo]
  refine ⟨congrArg (Mem.writeW _ _) ?_, ?_, rfl⟩
  · rw [add3, and_mask', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  · rw [add3, shr52 hc]

theorem add_step {X Ya Yb c la lb P : Nat} (hv : X + c * P = Ya + Yb) :
    X + (c + la + lb) % 2 ^ 52 * P + (c + la + lb) / 2 ^ 52 * (P * 2 ^ 52) = Ya + la * P + (Yb + lb * P) := by
  have e := Nat.mod_add_div (c + la + lb) (2 ^ 52)
  grind


/-- `[o] := [a] + [b]` (no overlap of `o` with `a` or `b`). -/
theorem addN_ok (hl : MrOk l) {s : State} {B : Addr} {Z o a b : Nat}
    (hB : s.gpr .rbx = B) (h12 : s.gpr .r12 = mask52) (hs : Scr s B Z)
    (ho : o + l.NB ≤ Z) (ha : a + l.NB ≤ Z) (hb : b + l.NB ≤ Z) (hZ : Z < 2 ^ 31)
    (soa : Sep l o a) (sob : Sep l o b)
    (hca : Canon l s.mem B a) (hcb : Canon l s.mem B b)
    (hlt : val52 l s.mem B a + val52 l s.mem B b < 2 ^ (52 * l.L)) :
    WP isa (.block (addN l o a b)) s fun t =>
      Canon l t.mem B o ∧ val52 l t.mem B o = val52 l s.mem B a + val52 l s.mem B b ∧
      Outside B o l.NB s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  rw [addN_eq, WP.block_append_iff]
  refine WP.mono (mov32_ok .rdx) fun t0 ⟨hd0, k0, m0, x0⟩ => ?_
  refine WP.mono (chain_ok (N := l.L) (f := addL l o a b) (I := fun n t =>
      (∃ c ≤ 1, t.gpr .rdx = BitVec.ofNat 64 c ∧
        lval (limb l t.mem B o) n + c * 2 ^ (52 * n) = lval (limb l s.mem B a) n + lval (limb l s.mem B b) n) ∧
      (∀ j < n, limb l t.mem B o j < 2 ^ 52) ∧ Outside B o l.NB s.mem t.mem ∧ Keep [.rax, .rdx] s t ∧
      t.mxcsr = s.mxcsr) ?step l.L (Nat.le_refl _) t0
    ⟨⟨0, by decide, hd0, by simp only [lval_zero, Nat.zero_mul]⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [m0]; exact Outside.refl _ _ _ _, k0.mono (by decide), x0⟩) fun t ⟨⟨c, hc1, _, hv⟩, hcn, f, k, x⟩ => ?fin
  case fin =>
    refine ⟨hcn, ?_, f, k, x⟩
    unfold val52 at hlt ⊢
    rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl
    · rw [Nat.zero_mul, Nat.add_zero] at hv; exact hv
    · rw [Nat.one_mul] at hv; omega_arith
  case step =>
    intro n hn t ⟨⟨c, hc1, hd, hv⟩, hcn, f, k, x⟩
    have hsn := hs.congr k.2.2
    have hBt : t.gpr .rbx = B := (k.gpr (by decide)).trans hB
    have h12t : t.gpr .r12 = mask52 := (k.gpr (by decide)).trans h12
    have hwa := word_out hl f soa (by omega_arith) hn
    have hwb := word_out hl f sob (by omega_arith) hn
    have hla : (word s.mem B (a + l.off n)).toNat < 2 ^ 52 := hca n hn
    have hlb : (word s.mem B (b + l.off n)).toNat < 2 ^ 52 := hcb n hn
    have := off_ltN hl.amm hn
    refine WP.mono (addL_ok (j := n) hBt h12t hd (hsn.ld (by omega_arith)) (hsn.ld (by omega_arith))
      (hsn.st (by omega_arith)) (by rw [hwa, hwb]; omega_arith)) fun t' ⟨hm, hd', k', x'⟩ => ?_
    rw [hwa, hwb] at hm hd'
    have hlo : limb l t'.mem B o n = (c + limb l s.mem B a n + limb l s.mem B b n) % 2 ^ 52 := by
      simp only [limb]
      rw [hm, word_writeW_self, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    have hlj : ∀ j < n, limb l t'.mem B o j = limb l t.mem B o j := fun j hj => by
      simp only [limb]
      rw [hm, word_wr_ne hl _ _ _ hn (by omega_arith) (by omega_arith) (by omega_arith)]
    refine ⟨⟨_, by omega_arith, hd', ?_⟩, fun j hj => ?_, ?_, (k.trans k').mono (by decide), x'.trans x⟩
    · rw [lval_succ, lval_succ, lval_succ (limb l s.mem B b), lval_congr hlj, hlo, Nat.mul_add_one, Nat.pow_add]
      exact add_step hv
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · rw [hlj j hj]; exact hcn j hj
      · rw [hlo]; exact Nat.mod_lt _ (by decide)
    · rw [hm]; exact f.trans (out_wr hl _ _ _ hn (by omega_arith))

/-! ## `subN` -/

/-- Limb `j` of `subN`. -/
def subL (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o a b j : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbx (a + l.off j))), .alu .add .rax (.reg .r12), .alu .add .rax (.reg .rdx),
    .alu .sub .rax (.mem (at_ .rbx (b + l.off j))), .mov .rdx (.reg .rax), .shift .shr .rdx 52,
    .alu .and .rax (.reg .r12), .store (at_ .rbx (o + l.off j)) .rax]

theorem subN_eq {o a b : Nat} :
    subN l o a b = ([.mov32 .rdx (.imm 1)] : List Instr) ++ (List.range l.L).flatMap (subL l o a b) := rfl

theorem m52 : mask52.toNat = 2 ^ 52 - 1 := by
  unfold mask52; rw [BitVec.toNat_ofNat]

theorem sub4 (x y : BitVec 64) (c : Nat) (h : y.toNat ≤ x.toNat + (2 ^ 52 - 1) + c)
    (h' : x.toNat + (2 ^ 52 - 1) + c < 2 ^ 64) :
    x + mask52 + BitVec.ofNat 64 c - y = BitVec.ofNat 64 (x.toNat + (2 ^ 52 - 1) + c - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, m52, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := y.isLt
  omega

theorem subL_ok {t : State} {B : Addr} {o a b j c : Nat} (hB : t.gpr .rbx = B) (h12 : t.gpr .r12 = mask52)
    (hd : t.gpr .rdx = BitVec.ofNat 64 c)
    (ra : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (a + l.off j)) 8)
    (rb : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (b + l.off j)) 8)
    (wo : InRegions t.wr (B + BitVec.ofNat 64 (o + l.off j)) 8) (hc : c ≤ 1)
    (hla : (word t.mem B (a + l.off j)).toNat < 2 ^ 52) (hlb : (word t.mem B (b + l.off j)).toNat < 2 ^ 52) :
    WP isa (.block (subL l o a b j)) t fun t' =>
      t'.mem = t.mem.writeW (off B (o + l.off j)) (BitVec.ofNat 64
        (((word t.mem B (a + l.off j)).toNat + (2 ^ 52 - 1) + c - (word t.mem B (b + l.off j)).toNat) % 2 ^ 52)) ∧
      t'.gpr .rdx = BitVec.ofNat 64
        (((word t.mem B (a + l.off j)).toNat + (2 ^ 52 - 1) + c - (word t.mem B (b + l.off j)).toNat) / 2 ^ 52) ∧
      Keep [.rax, .rdx] t t' ∧ t'.mxcsr = t.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rdx] (Q := fun t' =>
    t'.mem = t.mem.writeW (off B (o + l.off j)) (BitVec.ofNat 64
        (((word t.mem B (a + l.off j)).toNat + (2 ^ 52 - 1) + c - (word t.mem B (b + l.off j)).toNat) % 2 ^ 52)) ∧
      t'.gpr .rdx = BitVec.ofNat 64
        (((word t.mem B (a + l.off j)).toNat + (2 ^ 52 - 1) + c - (word t.mem B (b + l.off j)).toNat) / 2 ^ 52) ∧
      t'.mxcsr = t.mxcsr) ?_ rfl) fun t' ⟨⟨m, d, x⟩, k⟩ => ⟨m, d, k, x⟩
  unfold subL
  have hla' : (t.mem.readW (B + BitVec.ofNat 64 (a + l.off j)) 64).toNat < 2 ^ 52 := hla
  have hlb' : (t.mem.readW (B + BitVec.ofNat 64 (b + l.off j)) 64).toNat < 2 ^ 52 := hlb
  have e := sub4 (t.mem.readW (B + BitVec.ofNat 64 (a + l.off j)) 64)
    (t.mem.readW (B + BitVec.ofNat 64 (b + l.off j)) 64) c (by omega_arith) (by omega_arith)
  xrun [eaG', hB, h12, hd, ra, rb, wo, e]
  refine ⟨congrArg (Mem.writeW _ _) ?_, ?_, rfl⟩
  · rw [and_mask', BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]
  · rw [shr52 (by omega_arith)]

theorem sub_step {X Ya Yb c la lb S P : Nat} (hv : X + Yb + c * P = Ya + P) (hS : S + lb + 1 = la + 2 ^ 52 + c) :
    X + S % 2 ^ 52 * P + (Yb + lb * P) + S / 2 ^ 52 * (P * 2 ^ 52) = Ya + la * P + P * 2 ^ 52 := by
  have e := Nat.mod_add_div S (2 ^ 52)
  grind

/-- `[o] := [a] − [b] mod 2^(52 L)`; `rdx` is 1 if `[a] ≥ [b]`, else 0 (no
overlap of `o` with `a` or `b`). -/
theorem subN_ok (hl : MrOk l) {s : State} {B : Addr} {Z o a b : Nat}
    (hB : s.gpr .rbx = B) (h12 : s.gpr .r12 = mask52) (hs : Scr s B Z)
    (ho : o + l.NB ≤ Z) (ha : a + l.NB ≤ Z) (hb : b + l.NB ≤ Z) (hZ : Z < 2 ^ 31)
    (soa : Sep l o a) (sob : Sep l o b)
    (hca : Canon l s.mem B a) (hcb : Canon l s.mem B b) :
    WP isa (.block (subN l o a b)) s fun t =>
      Canon l t.mem B o ∧
      val52 l t.mem B o + val52 l s.mem B b =
        val52 l s.mem B a + (if val52 l s.mem B b ≤ val52 l s.mem B a then 0 else 2 ^ (52 * l.L)) ∧
      t.gpr .rdx = BitVec.ofNat 64 (if val52 l s.mem B b ≤ val52 l s.mem B a then 1 else 0) ∧
      Outside B o l.NB s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  rw [subN_eq, WP.block_append_iff]
  refine WP.mono (mov32_1_ok .rdx) fun t0 ⟨hd0, k0, m0, x0⟩ => ?_
  refine WP.mono (chain_ok (N := l.L) (f := subL l o a b) (I := fun n t =>
      (∃ c ≤ 1, t.gpr .rdx = BitVec.ofNat 64 c ∧
        lval (limb l t.mem B o) n + lval (limb l s.mem B b) n + c * 2 ^ (52 * n) =
          lval (limb l s.mem B a) n + 2 ^ (52 * n)) ∧
      (∀ j < n, limb l t.mem B o j < 2 ^ 52) ∧ Outside B o l.NB s.mem t.mem ∧ Keep [.rax, .rdx] s t ∧
      t.mxcsr = s.mxcsr) ?step l.L (Nat.le_refl _) t0
    ⟨⟨1, by decide, hd0, by simp only [lval_zero, Nat.zero_add]⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [m0]; exact Outside.refl _ _ _ _, k0.mono (by decide), x0⟩) fun t ⟨⟨c, hc1, hd, hv⟩, hcn, f, k, x⟩ => ?fin
  case fin =>
    refine ⟨hcn, ?_, ?_, f, k, x⟩
    · have ho := lval_lt hcn
      have ha := lval_lt hca
      have hb := lval_lt hcb
      unfold val52
      generalize 2 ^ (52 * l.L) = P at hv ho ha hb ⊢
      rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl
      · rw [Nat.zero_mul, Nat.add_zero] at hv
        rw [VG.Proof.MlKem.X86_64.ifn (by omega_arith)]; omega_arith
      · rw [Nat.one_mul] at hv
        rw [VG.Proof.MlKem.X86_64.ifp (by omega_arith)]; omega_arith
    · have ho := lval_lt hcn
      unfold val52
      generalize 2 ^ (52 * l.L) = P at hv ho
      rw [hd]
      rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl
      · rw [Nat.zero_mul, Nat.add_zero] at hv
        rw [VG.Proof.MlKem.X86_64.ifn (by omega_arith)]
      · rw [Nat.one_mul] at hv
        rw [VG.Proof.MlKem.X86_64.ifp (by omega_arith)]
  case step =>
    intro n hn t ⟨⟨c, hc1, hd, hv⟩, hcn, f, k, x⟩
    have hsn := hs.congr k.2.2
    have hBt : t.gpr .rbx = B := (k.gpr (by decide)).trans hB
    have h12t : t.gpr .r12 = mask52 := (k.gpr (by decide)).trans h12
    have hwa := word_out hl f soa (by omega_arith) hn
    have hwb := word_out hl f sob (by omega_arith) hn
    have hla : (word s.mem B (a + l.off n)).toNat < 2 ^ 52 := hca n hn
    have hlb : (word s.mem B (b + l.off n)).toNat < 2 ^ 52 := hcb n hn
    have := off_ltN hl.amm hn
    refine WP.mono (subL_ok (j := n) hBt h12t hd (hsn.ld (by omega_arith)) (hsn.ld (by omega_arith))
      (hsn.st (by omega_arith)) hc1 (by rw [hwa]; exact hla) (by rw [hwb]; exact hlb))
      fun t' ⟨hm, hd', k', x'⟩ => ?_
    rw [hwa, hwb] at hm hd'
    have hlo : limb l t'.mem B o n =
        (limb l s.mem B a n + (2 ^ 52 - 1) + c - limb l s.mem B b n) % 2 ^ 52 := by
      simp only [limb]
      rw [hm, word_writeW_self, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    have hlj : ∀ j < n, limb l t'.mem B o j = limb l t.mem B o j := fun j hj => by
      simp only [limb]
      rw [hm, word_wr_ne hl _ _ _ hn (by omega_arith) (by omega_arith) (by omega_arith)]
    refine ⟨⟨_, by omega_arith, hd', ?_⟩, fun j hj => ?_, ?_, (k.trans k').mono (by decide), x'.trans x⟩
    · rw [lval_succ, lval_succ, lval_succ (limb l s.mem B a), lval_congr hlj, hlo, Nat.mul_add_one, Nat.pow_add]
      have hla2 : limb l s.mem B a n < 2 ^ 52 := hca n hn
      have hlb2 : limb l s.mem B b n < 2 ^ 52 := hcb n hn
      exact sub_step hv (by omega_arith)
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · rw [hlj j hj]; exact hcn j hj
      · rw [hlo]; exact Nat.mod_lt _ (by decide)
    · rw [hm]; exact f.trans (out_wr hl _ _ _ hn (by omega_arith))

/-! ## `selN`, `eqN` -/

/-- Limb `j` of `selN`. -/
def selL (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o t j : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbx (o + l.off j))), .mov .rcx (.mem (at_ .rbx (t + l.off j))),
    .alu .xor .rcx (.reg .rax), .alu .and .rcx (.reg .rdx), .alu .xor .rax (.reg .rcx),
    .store (at_ .rbx (o + l.off j)) .rax]

theorem selN_eq {o t : Nat} : selN l o t = (List.range l.L).flatMap (selL l o t) := rfl

theorem selL_ok {u : State} {B : Addr} {o t j : Nat} {p : Bool} (hB : u.gpr .rbx = B) (hd : u.gpr .rdx = mask p)
    (ro : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (o + l.off j)) 8)
    (rt : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (t + l.off j)) 8)
    (wo : InRegions u.wr (B + BitVec.ofNat 64 (o + l.off j)) 8) :
    WP isa (.block (selL l o t j)) u fun u' =>
      u'.mem = u.mem.writeW (off B (o + l.off j))
        (if p then word u.mem B (t + l.off j) else word u.mem B (o + l.off j)) ∧
      Keep [.rax, .rcx] u u' ∧ u'.mxcsr = u.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx] (Q := fun u' =>
    u'.mem = u.mem.writeW (off B (o + l.off j))
        (if p then word u.mem B (t + l.off j) else word u.mem B (o + l.off j)) ∧
      u'.mxcsr = u.mxcsr) ?_ rfl) fun u' ⟨⟨m, x⟩, k⟩ => ⟨m, k, x⟩
  unfold selL
  xrun [eaG', hB, hd, ro, rt, wo]
  refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
  rw [BitVec.xor_comm, VG.Proof.Bignum.select_mask]

/-- Limb `j` of `eqN`. -/
def eqL (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (k j : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rbx (oY l + l.off j))), .alu .xor .rax (.mem (at_ .rbx (k + l.off j))),
    .alu .or .rcx (.reg .rax)]

theorem eqN_eq {k : Nat} : eqN l k = ([.mov32 .rcx (.imm 0)] : List Instr) ++ ((List.range l.L).flatMap (eqL l k) ++
    ([.alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx)] : List Instr)) := rfl

theorem eqL_ok {t : State} {B : Addr} {k j : Nat} (hB : t.gpr .rbx = B)
    (ry : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (oY l + l.off j)) 8)
    (rk : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 (k + l.off j)) 8) :
    WP isa (.block (eqL l k j)) t fun t' =>
      t'.gpr .rcx = t.gpr .rcx ||| (word t.mem B (oY l + l.off j) ^^^ word t.mem B (k + l.off j)) ∧
      t'.mem = t.mem ∧ Keep [.rax, .rcx] t t' ∧ t'.mxcsr = t.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx] (Q := fun t' =>
    t'.gpr .rcx = t.gpr .rcx ||| (word t.mem B (oY l + l.off j) ^^^ word t.mem B (k + l.off j)) ∧
      t'.mem = t.mem ∧ t'.mxcsr = t.mxcsr) ?_ rfl) fun t' ⟨⟨c, m, x⟩, k⟩ => ⟨c, m, k, x⟩
  unfold eqL
  xrun [eaG', hB, ry, rk]
  all_goals rfl

theorem lt1_iff (x : BitVec 64) : x.toNat < BitVec.toNat (1 : BitVec 64) ↔ x = 0#64 := by
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1]
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  · intro h; rw [h, BitVec.toNat_ofNat]; decide

/-- `cmp r, 1; sbb r, r`: the mask of `r = 0`. -/
theorem cmpSbb_rcx {s : State} :
    WP isa (.block [.alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx)]) s fun t =>
      t.gpr .rcx = mask (decide (s.gpr .rcx = 0#64)) ∧ Keep [.rcx] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rcx] (Q := fun t =>
    t.gpr .rcx = mask (decide (s.gpr .rcx = 0#64)) ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) ?_ rfl)
    fun t ⟨⟨c, m, x⟩, k⟩ => ⟨c, k, m, x⟩
  xrun
  rw [decide_eq_decide.2 (lt1_iff _)]
  exact ⟨rfl, rfl⟩

theorem cmpSbb_rdx {s : State} :
    WP isa (.block [.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)]) s fun t =>
      t.gpr .rdx = mask (decide (s.gpr .rdx = 0#64)) ∧ Keep [.rdx] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx] (Q := fun t =>
    t.gpr .rdx = mask (decide (s.gpr .rdx = 0#64)) ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) ?_ rfl)
    fun t ⟨⟨c, m, x⟩, k⟩ => ⟨c, k, m, x⟩
  xrun
  rw [decide_eq_decide.2 (lt1_iff _)]
  exact ⟨rfl, rfl⟩


/-- `[o] := p ? [t] : [o]`, limb by limb, for `rdx = mask p` (`o` and `t`
not overlapping). -/
theorem selN_ok (hl : MrOk l) {s : State} {B : Addr} {Z o t : Nat} {p : Bool}
    (hB : s.gpr .rbx = B) (hd : s.gpr .rdx = mask p) (hs : Scr s B Z)
    (ho : o + l.NB ≤ Z) (ht : t + l.NB ≤ Z) (hZ : Z < 2 ^ 31) (sot : Sep l o t) :
    WP isa (.block (selN l o t)) s fun s' =>
      (∀ j < l.L, limb l s'.mem B o j = if p then limb l s.mem B t j else limb l s.mem B o j) ∧
      Outside B o l.NB s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [selN_eq]
  refine WP.mono (chain_ok (N := l.L) (f := selL l o t) (I := fun n s' =>
      (∀ j < l.L, word s'.mem B (o + l.off j) = if j < n then
        (if p then word s.mem B (t + l.off j) else word s.mem B (o + l.off j)) else word s.mem B (o + l.off j)) ∧
      Outside B o l.NB s.mem s'.mem ∧ Keep [.rax, .rcx] s s' ∧ s'.mxcsr = s.mxcsr) ?step l.L (Nat.le_refl _) s
    ⟨fun j _ => (VG.Proof.MlKem.X86_64.ifn (Nat.not_lt_zero j) _ _).symm, Outside.refl _ _ _ _, Keep.refl _ _, rfl⟩)
    fun s' ⟨hw, f, k, x⟩ => ?fin
  case fin =>
    refine ⟨fun j hj => ?_, f, k, x⟩
    simp only [limb]
    rw [hw j hj, VG.Proof.MlKem.X86_64.ifp hj]
    cases p <;> rfl
  case step =>
    intro n hn u ⟨hw, f, k, x⟩
    have hsn := hs.congr k.2.2
    have hBt : u.gpr .rbx = B := (k.gpr (by decide)).trans hB
    have hdt : u.gpr .rdx = mask p := (k.gpr (by decide)).trans hd
    have hwt := word_out hl f sot (by omega_arith) hn
    have hwo : word u.mem B (o + l.off n) = word s.mem B (o + l.off n) := by
      rw [hw n hn, VG.Proof.MlKem.X86_64.ifn (Nat.lt_irrefl n)]
    have := off_ltN hl.amm hn
    refine WP.mono (selL_ok (j := n) hBt hdt (hsn.ld (by omega_arith)) (hsn.ld (by omega_arith))
      (hsn.st (by omega_arith))) fun u' ⟨hm, k', x'⟩ => ⟨fun j hj => ?_, ?_, (k.trans k').mono (by decide), x'.trans x⟩
    · rw [hm, hwt, hwo]
      by_cases e : j = n
      · subst e; rw [word_writeW_self, VG.Proof.MlKem.X86_64.ifp (Nat.lt_succ_self _)]
      · rw [word_wr_ne hl _ _ _ hn hj e (by omega_arith), hw j hj]
        by_cases h : j < n
        · rw [VG.Proof.MlKem.X86_64.ifp h, VG.Proof.MlKem.X86_64.ifp (show j < n + 1 by omega_arith)]
        · rw [VG.Proof.MlKem.X86_64.ifn h, VG.Proof.MlKem.X86_64.ifn (show ¬j < n + 1 by omega_arith)]
    · rw [hm]; exact f.trans (out_wr hl _ _ _ hn (by omega_arith))

/-- `rcx := mask (Y = [k] limb by limb)`. -/
theorem eqN_ok (hl : MrOk l) {s : State} {B : Addr} {Z k : Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B Z)
    (hy : oY l + l.NB ≤ Z) (hk : k + l.NB ≤ Z) (hZ : Z < 2 ^ 31) :
    WP isa (.block (eqN l k)) s fun t =>
      t.gpr .rcx = mask (decide (∀ j < l.L, limb l s.mem B (oY l) j = limb l s.mem B k j)) ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx] s t ∧ t.mxcsr = s.mxcsr := by
  have _hZ := hZ
  rw [eqN_eq, WP.block_append_iff]
  refine WP.mono (mov32_ok .rcx) fun t0 ⟨hc0, k0, m0, x0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok (N := l.L) (f := eqL l k) (I := fun n t =>
      (t.gpr .rcx = 0#64 ↔ ∀ j < n, limb l s.mem B (oY l) j = limb l s.mem B k j) ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx] s t ∧ t.mxcsr = s.mxcsr) ?step l.L (Nat.le_refl _) t0
    ⟨by rw [hc0]; exact ⟨fun _ j hj => absurd hj (Nat.not_lt_zero _), fun _ => rfl⟩, m0, k0.mono (by decide), x0⟩)
    fun t ⟨hz, hm, k, x⟩ => ?fin
  case fin =>
    refine WP.mono cmpSbb_rcx fun t' ⟨hc, k', m', x'⟩ =>
      ⟨?_, m'.trans hm, (k.trans k').mono (by decide), x'.trans x⟩
    rw [hc]; exact congrArg mask (decide_eq_decide.2 hz)
  case step =>
    intro n hn t ⟨hz, hm, k, x⟩
    have hsn := hs.congr k.2.2
    have hBt : t.gpr .rbx = B := (k.gpr (by decide)).trans hB
    have := off_ltN hl.amm hn
    refine WP.mono (eqL_ok (j := n) hBt (hsn.ld (by omega_arith)) (hsn.ld (by omega_arith)))
      fun t' ⟨hc, hm', k', x'⟩ => ⟨?_, hm'.trans hm, (k.trans k').mono (by decide), x'.trans x⟩
    rw [hc, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, hz, hm]
    constructor
    · rintro ⟨h, e⟩ j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact h j hj
      · exact congrArg BitVec.toNat e
    · intro h
      exact ⟨fun j hj => h j (by omega_arith), BitVec.eq_of_toNat_eq (h n (by omega_arith))⟩

/-! ## Doublings -/

theorem pub_pos (hl : MrOk l) : 0 < l.L ∧ 8 ≤ l.NB ∧ l.S = l.L := by
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The limbs at 0, through changes of `x` and `tmp` only. -/
theorem frm_word0 (hl : MrOk l) {m m' : Mem} {B : Addr} {x tmp : Nat}
    (h : Frm B [(x, l.NB), (tmp, l.NB)] m m') (sx0 : Sep l x 0) (st0 : Sep l tmp 0) (hN : l.NB < 2 ^ 63)
    {j : Nat} (hj : j < l.L) : word m' B (0 + l.off j) = word m B (0 + l.off j) := by
  have := off_ltN hl.amm hj
  unfold Sep at sx0 st0
  refine h.word_eq (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl <;> (try dsimp only) <;> omega_arith

/-- `dbl1`, the modulus given by its limbs at 0. -/
theorem dbl1_core (hl : MrOk l) {s : State} {B : Addr} {Z x tmp c : Nat}
    (hB : s.gpr .rbx = B) (h12 : s.gpr .r12 = mask52) (hs : Scr s B Z)
    (h0c : Canon l s.mem B 0) (h0v : val52 l s.mem B 0 = c) (hbig : 4 * c ≤ 2 ^ (52 * l.S))
    (hx : x + l.NB ≤ Z) (ht : tmp + l.NB ≤ Z) (hZ : Z < 2 ^ 31)
    (sxt : Sep l x tmp) (sx0 : Sep l x 0) (st0 : Sep l tmp 0)
    (hcx : Canon l s.mem B x) (hlt : val52 l s.mem B x < c) :
    WP isa (.block (dbl1 l x tmp)) s fun t =>
      Canon l t.mem B x ∧ val52 l t.mem B x = 2 * val52 l s.mem B x % c ∧
      Frm B [(x, l.NB), (tmp, l.NB)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧
      t.mxcsr = s.mxcsr := by
  obtain ⟨-, hNB, hSL⟩ := pub_pos hl
  have h0 : 0 + l.NB ≤ Z := by unfold Sep at sx0; omega_arith
  obtain ⟨v, hv⟩ : ∃ v, val52 l s.mem B x = v := ⟨_, rfl⟩
  have hP : val52 l s.mem B x + val52 l s.mem B x < 2 ^ (52 * l.L) := by
    rw [hSL] at hbig; rw [hv]; rw [hv] at hlt
    generalize 2 ^ (52 * l.L) = P at hbig ⊢; omega_arith
  rw [hv]
  unfold dbl1
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (addN_ok hl hB h12 hs ht hx hx hZ (Or.symm sxt) (Or.symm sxt) hcx hcx hP)
    fun t1 ⟨c1, v1, f1, k1, x1⟩ => ?_
  rw [hv] at v1
  have hw0 : ∀ j < l.L, limb l t1.mem B 0 j = limb l s.mem B 0 j := fun j hj =>
    congrArg BitVec.toNat (word_out hl f1 st0 (by omega_arith) hj)
  have c01 : Canon l t1.mem B 0 := fun j hj => by rw [hw0 j hj]; exact h0c j hj
  have v01 : val52 l t1.mem B 0 = c := by rw [← h0v]; unfold val52; exact lval_congr hw0
  refine WP.mono (subN_ok hl ((k1.gpr (by decide)).trans hB) ((k1.gpr (by decide)).trans h12) (hs.congr k1.2.2)
    hx ht h0 hZ sxt sx0 c1 c01) fun t2 ⟨c2, v2, d2, f2, k2, x2⟩ => ?_
  rw [v01, v1] at v2 d2
  have hwt : ∀ j < l.L, word t2.mem B (tmp + l.off j) = word t1.mem B (tmp + l.off j) := fun j hj =>
    word_out hl f2 sxt (by omega_arith) hj
  refine WP.mono cmpSbb_rdx fun t3 ⟨d3, k3, m3, x3⟩ => ?_
  have hp : t3.gpr .rdx = mask (decide (v + v < c)) := by
    rw [d3, d2]
    refine congrArg mask (decide_eq_decide.2 ?_)
    by_cases h : c ≤ v + v
    · rw [VG.Proof.MlKem.X86_64.ifp h]
      exact ⟨fun e => absurd e (by decide), fun e => absurd h (by omega_arith)⟩
    · rw [VG.Proof.MlKem.X86_64.ifn h]
      exact ⟨fun _ => by omega_arith, fun _ => rfl⟩
  have hB3 : t3.gpr .rbx = B :=
    (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans hB))
  refine WP.mono (selN_ok hl hB3 hp (hs.congr (k3.2.2.trans (k2.2.2.trans k1.2.2))) hx ht hZ sxt)
    fun t4 ⟨h4, f4, k4, x4⟩ => ?_
  have m3' : t3.mem = t2.mem := m3
  refine ⟨fun j hj => ?_, ?_, ?_, (((k1.trans k2).trans k3).trans k4).mono (by decide),
    x4.trans (x3.trans (x2.trans x1))⟩
  · rw [h4 j hj, m3']
    split
    · simp only [limb]; rw [hwt j hj]; exact c1 j hj
    · exact c2 j hj
  · by_cases hc : v + v < c
    · have e : val52 l t4.mem B x = val52 l t1.mem B tmp := by
        unfold val52
        refine lval_congr fun j hj => ?_
        rw [h4 j hj, m3', decide_eq_true hc, VG.Proof.MlKem.X86_64.ifp rfl]
        simp only [limb]; rw [hwt j hj]
      rw [e, v1, ← Nat.two_mul, Nat.mod_eq_of_lt (by omega_arith)]
    · have e : val52 l t4.mem B x = val52 l t2.mem B x := by
        unfold val52
        refine lval_congr fun j hj => ?_
        rw [h4 j hj, m3', decide_eq_false hc, VG.Proof.MlKem.X86_64.ifn Bool.false_ne_true]
      rw [VG.Proof.MlKem.X86_64.ifp (show c ≤ v + v by omega_arith)] at v2
      rw [e, Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
  · have F1 : Frm B [(x, l.NB), (tmp, l.NB)] s.mem t1.mem :=
      VG.Proof.Bignum.Frm.of_outside f1 (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have F2 : Frm B [(x, l.NB), (tmp, l.NB)] t1.mem t2.mem :=
      VG.Proof.Bignum.Frm.of_outside f2 (List.mem_cons_self ..)
    have F4 : Frm B [(x, l.NB), (tmp, l.NB)] t3.mem t4.mem :=
      VG.Proof.Bignum.Frm.of_outside f4 (List.mem_cons_self ..)
    rw [m3'] at F4
    exact (F1.trans F2).trans F4

theorem mov32n_ok {s : State} (r : Reg) {n : Nat} (hn : n < 2 ^ 31) :
    WP isa (.block [.mov32 r (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr r = BitVec.ofNat 64 n ∧ Keep [r] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  refine WP.block_cons_iff.2 ⟨s.setReg32 r _, rfl, WP.block_nil ⟨?_, ⟨fun q hq => ?_, rfl, rfl⟩, rfl, rfl⟩⟩
  · rw [State.setReg32, RegUpd.gpr_setReg_self]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (fun h => hq (by simp [h]))]

theorem sub13_ok {s : State} {k : Nat} (h : s.gpr .r13 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 31) :
    WP isa (.block [.alu .sub .r13 (.imm 1)]) s fun t =>
      t.gpr .r13 = BitVec.ofNat 64 (k - 1) ∧ t.zf = some (decide (k - 1 = 0)) ∧ Keep [.r13] s t ∧
      t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun t =>
    t.gpr .r13 = BitVec.ofNat 64 (k - 1) ∧ t.zf = some (decide (k - 1 = 0)) ∧ t.mem = s.mem ∧
      t.mxcsr = s.mxcsr) ?_ rfl) fun t ⟨⟨a, b, c, d⟩, kk⟩ => ⟨a, b, kk, c, d⟩
  xrun [h, VG.Proof.MlKem.X86_64.ofNat64_pred hk (by omega),
    VG.Proof.MlKem.X86_64.ofNat64_beq_zero (k := k - 1) (by omega)]
  rfl

/-- `[x] := 2 [x] mod c`, the modulus `c` at 0, through `tmp`. -/
theorem dbl1_ok (hl : MrOk l) {s : State} {B : Addr} {Z x tmp c k : Nat}
    (hB : s.gpr .rbx = B) (h12 : s.gpr .r12 = mask52) (hs : Scr s B Z) (hm : Mod l s.mem B c k)
    (hx : x + l.NB ≤ Z) (ht : tmp + l.NB ≤ Z) (hZ : Z < 2 ^ 31)
    (sxt : Sep l x tmp) (sx0 : Sep l x 0) (st0 : Sep l tmp 0)
    (hcx : Canon l s.mem B x) (hlt : val52 l s.mem B x < c) :
    WP isa (.block (dbl1 l x tmp)) s fun t =>
      Canon l t.mem B x ∧ val52 l t.mem B x = 2 * val52 l s.mem B x % c ∧
      Frm B [(x, l.NB), (tmp, l.NB)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧
      t.mxcsr = s.mxcsr := by
  exact dbl1_core hl hB h12 hs hm.lt hm.val hm.big hx ht hZ sxt sx0 st0 hcx hlt

/-- `[x] := 2^n [x] mod c`, through `tmp`, `r13` counting. -/
theorem dbls_ok (hl : MrOk l) {s : State} {B : Addr} {Z x tmp c k n : Nat}
    (hB : s.gpr .rbx = B) (h12 : s.gpr .r12 = mask52) (hs : Scr s B Z) (hm : Mod l s.mem B c k)
    (hx : x + l.NB ≤ Z) (ht : tmp + l.NB ≤ Z) (hZ : Z < 2 ^ 31)
    (sxt : Sep l x tmp) (sx0 : Sep l x 0) (st0 : Sep l tmp 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 31)
    (hcx : Canon l s.mem B x) (hlt : val52 l s.mem B x < c) :
    WP isa (dbls l x tmp n) s fun t =>
      Canon l t.mem B x ∧ val52 l t.mem B x = 2 ^ n * val52 l s.mem B x % c ∧
      Frm B [(x, l.NB), (tmp, l.NB)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .r13] s t ∧
      t.mxcsr = s.mxcsr := by
  obtain ⟨-, hNB, -⟩ := pub_pos hl
  have hc0 : 0 < c := by omega_arith
  have hN : l.NB < 2 ^ 63 := by omega_arith
  obtain ⟨v, hv⟩ : ∃ v, val52 l s.mem B x = v := ⟨_, rfl⟩
  rw [hv] at hlt ⊢
  unfold dbls
  refine WP.seq (WP.mono (mov32n_ok .r13 hn') fun t0 ⟨r0, k0, m0, x0⟩ => ?_)
  refine VG.Proof.Bignum.X86_64.wp_upto (a := 0) (N := n) (by omega_arith) (fun j t =>
      t.gpr .r13 = BitVec.ofNat 64 (n - j) ∧ Canon l t.mem B x ∧ val52 l t.mem B x = 2 ^ j * v % c ∧
      Frm B [(x, l.NB), (tmp, l.NB)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .r13] s t ∧ t.mxcsr = s.mxcsr)
    ?_ (fun t ⟨_, h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩)
    ⟨by rw [r0, Nat.sub_zero], by rw [m0]; exact hcx,
      by rw [m0, hv, Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hlt], by rw [m0]; exact Frm.refl _ _ _,
      k0.mono (by decide), x0⟩
  intro j _ hj t ⟨r, hcn, hval, F, k, xx⟩
  have hw0 : ∀ i < l.L, word t.mem B (0 + l.off i) = word s.mem B (0 + l.off i) := fun i hi =>
    frm_word0 hl F sx0 st0 hN hi
  have c0 : Canon l t.mem B 0 := fun i hi => by simp only [limb]; rw [hw0 i hi]; exact hm.lt i hi
  have v0 : val52 l t.mem B 0 = c := by
    rw [← hm.val]; unfold val52; exact lval_congr fun i hi => congrArg BitVec.toNat (hw0 i hi)
  rw [WP.block_append_iff]
  refine WP.mono (dbl1_core hl ((k.gpr (by decide)).trans hB) ((k.gpr (by decide)).trans h12) (hs.congr k.2.2)
    c0 v0 hm.big hx ht hZ sxt sx0 st0 hcn (by rw [hval]; exact Nat.mod_lt _ hc0))
    fun t1 ⟨c1, v1, F1, k1, x1⟩ => ?_
  refine WP.mono (sub13_ok (k := n - j) ((k1.gpr (by decide)).trans r) (by omega_arith) (by omega_arith))
    fun t2 ⟨r2, z2, k2, m2, x2⟩ => ?_
  refine ⟨by rw [z2]; exact congrArg some (decide_eq_decide.2 (by omega_arith)), ?_, ?_, ?_, ?_,
    ((k.trans k1).trans k2).mono (by decide), x2.trans (x1.trans xx)⟩
  · rw [r2, Nat.sub_sub]
  · rw [m2]; exact c1
  · rw [m2, v1, hval, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.pow_succ']
  · rw [m2]; exact F.trans F1

end VG.Proof.MillerRabin.X86_64.Ifma
