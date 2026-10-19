module

public import VerifiedGarbage.Proof.Ffdh.Lead
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH on x86-64: scan the public subgroup order -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

def ScanAt (s₀ : State) (p : Addr) (n j : Nat) (t : State) : Prop :=
  t.gpr .rsi = off p j ∧ t.gpr .rcx = BitVec.ofNat 64 (n - j) ∧ t.mem = s₀.mem ∧
    Keep [.rsi, .rcx, .rax, .rbp, .rdx] s₀ t

private theorem mask_step (c d : Bool) :
    ((0#64 - (BitVec.ofBool c).setWidth 64) &&&
      ((0#64 - (BitVec.ofBool d).setWidth 64) ^^^ (BitVec.ofInt 32 (-1)).signExtend 64)) &&& 1 =
      BitVec.ofNat 64 (c && !d).toNat := by
  cases c <;> cases d <;> rfl

private theorem byte_lt_one (b : Byte) :
    decide ((b.setWidth 64).toNat < (1 : BitVec 64).toNat) = decide (b = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  have hb := b.isLt
  rw [BitVec.toNat_setWidth]
  simp only [show (1 : BitVec 64).toNat = 1 from rfl]
  rw [Nat.mod_eq_of_lt (by omega), ← BitVec.toNat_inj]
  simp only [show (0 : Byte).toNat = 0 from rfl]
  omega

private theorem lt_two {m : Nat} (hm : m < 2 ^ 64) :
    decide ((BitVec.ofNat 64 m).toNat < (2 : BitVec 64).toNat) = decide (m < 2) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]; rfl

/-- One scan iteration advances exactly when the current byte is zero and
at least one later byte remains. -/
theorem scanStep_ok {s₀ : State} {p : Addr} {bs : List Byte} (hl : bs.length < 2 ^ 32) (hne : bs ≠ [])
    (hrd : ∀ i < bs.length, InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < bs.length), s₀.mem (p + BitVec.ofNat 64 i) = bs[i])
    {j : Nat} (hj : j ≤ lead bs) {t : State} (ht : ScanAt s₀ p bs.length j t) :
    WP isa (.block scanBody) t fun t' => ScanAt s₀ p bs.length (min (j + 1) (lead bs)) t' ∧
      t'.zf = some (decide (j + 1 = lead bs + 1)) := by
  have hL := lead_lt hne
  have hjl : j < bs.length := by omega
  obtain ⟨hsi, hcx, hm, kt⟩ := ht
  have hld : InRegions (t.rd ++ t.wr) (off p j) 1 := by rw [kt.2.1, kt.2.2]; exact hrd j hjl
  have hb : t.mem (off p j) = bs[j] := by rw [hm]; exact hval j hjl
  have hgo : (bs[j] = 0 ∧ 2 ≤ bs.length - j) ↔ j < lead bs := by
    constructor
    · rintro ⟨hz, h2⟩
      by_contra hc
      have he : j = lead bs := by omega
      subst he
      exact lead_nonzero hne (by omega) hz
    · intro hlt
      obtain ⟨_, hz⟩ := lead_zero j hlt
      exact ⟨hz, by omega⟩
  let c : Bool := decide (j < lead bs)
  have hflag : (decide (bs[j] = 0) && !decide (bs.length - j < 2)) = c := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not,
      Nat.not_lt, c]
    exact hgo
  have hmask : ((0#64 - (BitVec.ofBool (decide (bs[j] = 0))).setWidth 64) &&&
      ((0#64 - (BitVec.ofBool (decide (bs.length - j < 2))).setWidth 64) ^^^
        (BitVec.ofInt 32 (-1)).signExtend 64)) &&& 1 = BitVec.ofNat 64 c.toNat := by
    simpa only [hflag] using mask_step (decide (bs[j] = 0)) (decide (bs.length - j < 2))
  refine WP.mono (WP.keep [.rsi, .rcx, .rax, .rbp, .rdx] (Q := fun t' =>
      t'.gpr .rsi = off p j + BitVec.ofNat 64 c.toNat ∧
      t'.gpr .rcx = BitVec.ofNat 64 (bs.length - j) - BitVec.ofNat 64 c.toNat ∧ t'.mem = t.mem ∧
      t'.zf = some (decide (c.toNat = 0)))
    (by
      unfold scanBody
      xrun [State.ea, at0, hsi, hcx,
        show off p j + BitVec.ofInt 64 0 = off p j from by simp, hld, hb, byte_lt_one,
        lt_two (show bs.length - j < 2 ^ 64 by omega), hmask]
      cases c <;> rfl) rfl) fun t' ⟨⟨hsi', hcx', hm', hz⟩, k⟩ => ?_
  refine ⟨⟨?_, ?_, hm'.trans hm, (kt.trans k).mono (by decide)⟩, ?_⟩
  · rw [hsi']
    by_cases h : j < lead bs
    · simp only [c, h, decide_true, Bool.toNat_true, Nat.min_eq_left (by omega : j + 1 ≤ lead bs)]
      simp [off, BitVec.ofNat_add, BitVec.add_assoc]
    · simp only [c, h, decide_false, Bool.toNat_false, Nat.min_eq_right (by omega : lead bs ≤ j + 1)]
      have he : j = lead bs := by omega
      simp [he]
  · rw [hcx']
    apply BitVec.eq_of_toNat_eq
    by_cases h : j < lead bs <;>
      simp only [c, h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false,
        BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  · rw [hz]
    congr 1
    by_cases h : j < lead bs <;> simp [c, h] <;> omega

/-- Find the significant public bytes of q and save their pointer and length. -/
theorem scan_raw_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z) {sp : Nat} (hsp : sp < 32)
    {p : Addr} {bs : List Byte} (hp : word s.mem B (8 * sp) = p)
    (hk : word s.mem B (8 * sK) = BitVec.ofNat 64 bs.length)
    (hne : bs ≠ []) (hl : bs.length < 2 ^ 32) (hsrc : Src s B Z p bs) :
    WP isa (seqs (scan sp)) s fun t =>
      word t.mem B (8 * sEp) = off p (lead bs) ∧
      word t.mem B (8 * sEl) = BitVec.ofNat 64 (bs.length - lead bs) ∧
      t.gpr .rax = (bs[lead bs]'(lead_lt hne)).setWidth 64 ∧
      Frm B [(8 * sEp, 8), (8 * sEl, 8)] s.mem t.mem ∧
      Keep [.rsi, .rcx, .rax, .rbp, .rdx] s t := by
  have hn := hs.nowrap
  have hL := lead_lt hne
  unfold scan
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = p ∧
      t.gpr .rcx = BitVec.ofNat 64 bs.length ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.ld (by omega : 8 * sp + 8 ≤ Z),
      hs.ld (by unfold sK sFn; omega : 8 * sK + 8 ≤ Z), hp, hk]) rfl)
    fun s₁ ⟨⟨hsi₁, hcx₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := lead bs + 1) (by omega)
    (fun j t => ScanAt s₁ p bs.length (min j (lead bs)) t)
    (fun j _ hj t ht => by
      have e : min j (lead bs) = j := Nat.min_eq_left (by omega)
      rw [e] at ht
      exact WP.mono (scanStep_ok hl hne
        (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact hsrc.rd i hi)
        (fun i hi => by rw [hm₁]; exact hsrc.val i hi) (by omega) ht)
        fun _ ⟨ht', hz⟩ => ⟨hz, ht'⟩)
    (fun _ ht => ht) ⟨by rw [hsi₁]; simp, by rw [hcx₁]; simp, rfl, Keep.refl _ _⟩)
    fun s₂ h₂ => ?_)
  rw [Nat.min_eq_right (by omega)] at h₂
  obtain ⟨hsi₂, hcx₂, hm₂, k₂⟩ := h₂
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans hdi
  have hs₂ := hs.congr (k₂.2.2.trans k₁.2.2)
  have hld : InRegions (s₂.rd ++ s₂.wr) (off p (lead bs)) 1 := by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hsrc.rd _ hL
  have hEp : 8 * sEp + 8 ≤ Z := by unfold sEp sFn; omega
  have hEl : 8 * sEl + 8 ≤ Z := by unfold sEl sFn; omega
  let m := (s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))).writeW
    (off B (8 * sEl)) (BitVec.ofNat 64 (bs.length - lead bs))
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = m ∧ t.gpr .rax = (m (off p (lead bs))).setWidth 64)
    (by xrun [State.ea, hdr, at0, hdi₂, hdrOff, hsi₂, hcx₂,
      show off p (lead bs) + BitVec.ofInt 64 0 = off p (lead bs) from by simp,
      hs₂.st (d := 8 * sEp) (by omega), hs₂.st (d := 8 * sEl) (by omega), hld, m]) rfl)
    fun t ⟨⟨hm, hax⟩, k⟩ => ?_
  have o₁ := writeW_outside s₂.mem B (d := 8 * sEp) (off p (lead bs)) (by decide)
  have o₂ := writeW_outside (s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))) B
    (d := 8 * sEl) (BitVec.ofNat 64 (bs.length - lead bs)) (by decide)
  have hout : Z ≤ ofs B (off p (lead bs)) := hsrc.out _ hL
  have hbyte : m (off p (lead bs)) = bs[lead bs] := by
    dsimp only [m]
    rw [o₂ _ (Or.inr (by omega)), o₁ _ (Or.inr (by omega)), hm₂, hm₁]
    exact hsrc.val _ hL
  refine ⟨?_, ?_, by rw [hax, hbyte], ?_, ((k₁.trans k₂).trans k).mono (by decide)⟩
  · rw [hm]; dsimp only [m]
    rw [o₂.word (by decide) (by decide)]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro x hx
    rw [hm]; dsimp only [m]
    rw [o₂ x (hx (8 * sEl, 8) (by simp)), o₁ x (hx (8 * sEp, 8) (by simp)), hm₂, hm₁]

/-- Scan with the already initialized arithmetic workspace. -/
theorem scan_ok {s : State} {B : Addr} {Z w : Nat} (h : Outer s B Z w) {sp : Nat} (hsp : sp < 32)
    {p : Addr} {bs : List Byte} (hp : word s.mem B (8 * sp) = p)
    (hk : word s.mem B (8 * sK) = BitVec.ofNat 64 bs.length)
    (hne : bs ≠ []) (hl : bs.length < 2 ^ 32) (hsrc : Src s B Z p bs) :
    WP isa (seqs (scan sp)) s fun t =>
      word t.mem B (8 * sEp) = off p (lead bs) ∧
      word t.mem B (8 * sEl) = BitVec.ofNat 64 (bs.length - lead bs) ∧
      t.gpr .rax = (bs[lead bs]'(lead_lt hne)).setWidth 64 ∧
      Frm B [(8 * sEp, 8), (8 * sEl, 8)] s.mem t.mem ∧
      Keep [.rsi, .rcx, .rax, .rbp, .rdx] s t :=
  scan_raw_ok (B := B) (Z := Z) (sp := sp) (p := p) (bs := bs) h.scr h.rdi
    (by have hr := h.room; have hh := hdr_lt_slot w 8 (show 31 < 32 by decide); omega)
    hsp hp hk hne hl hsrc

end VG.Proof.Ffdh.X86_64
