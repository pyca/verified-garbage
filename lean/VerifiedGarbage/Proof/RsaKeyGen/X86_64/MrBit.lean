import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.MrMont

/-!
# A candidate on x86-64: one bit of Miller–Rabin's exponentiation

`MrCtx`: what Miller–Rabin keeps, `-c⁻¹` and `c`, the witness in Montgomery
form in `aB`, and `R mod c`, `c − R mod c` in `aR1`, `aRm1`. `mrExpBit_ok`:
`y := y² b^bit`, and the flag, from the top bit of `kV`.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What Miller–Rabin keeps: `-c⁻¹`, `c`, the witness `b R mod c` in `aB`,
`R mod c` and `c − R mod c`. -/
structure MrCtx (t : State) (B : Addr) (Z w : Nat) (mi : BitVec 64) (c bm : Nat) : Prop where
  good : Good t B Z w mi
  inv : ((word t.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0
  n : wv t.mem B (slot w aN) w = c
  b : wv t.mem B (slot w aB) w = bm
  r1 : wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % c
  rm1 : wv t.mem B (slot w aRm1) w = c - 2 ^ (64 * w) % c

/-- The bounds of the scratch space Miller–Rabin needs. -/
structure MrDims (B : Addr) (Z w : Nat) : Prop where
  z : slot w 8 ≤ Z
  x : slot w aRm1 + 8 * (w + 2) ≤ Z
  w4 : 4 ≤ w
  w64 : w ≤ 64

theorem shr63_ofNat (b : Bool) : BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 b.toNat := rfl

theorem neg_bit (b : Bool) : BitVec.setWidth 64 (0 : BitVec 32) - BitVec.ofNat 64 b.toNat = mask b := by
  cases b <;> decide

theorem sxm1' : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

/-- The flag's update. -/
theorem flag_mask (P m e bt : Bool) :
    (mask P ||| mask m) &&& (mask bt ^^^ BitVec.allOnes 64) ||| (mask e ||| mask m) &&& mask bt =
      mask (if bt then e || m else P || m) := by
  cases P <;> cases m <;> cases e <;> cases bt <;> decide

/-- The end of `mrExpBit`: the flag, `kV := 2 kV`, `kBits := kBits − 1`. -/
theorem bitTail_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {V : BitVec 64} {bt m e P : Bool} {n : Nat} (hV : word s.mem B (8 * kV) = V)
    (hbt : V >>> 63 = BitVec.ofNat 64 bt.toNat) (hG : word s.mem B (8 * kG) = mask m) (hbp : s.gpr .rbp = mask e)
    (hP : word s.mem B (8 * kFlag) = mask P) (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn' : n < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 63, .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
      .mov .rdx (.mem (hdr kG)), .alu .or .rbp (.reg .rdx), .alu .and .rbp (.reg .r15),
      .mov .rax (.mem (hdr kFlag)), .alu .or .rax (.reg .rdx), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
      .alu .and .rax (.reg .r15), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax,
      .mov .rax (.mem (hdr kV)), .alu .add .rax (.reg .rax), .store (hdr kV) .rax,
      .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]) s fun t =>
      t.mem = ((s.mem.writeW (off B (8 * kFlag)) (mask (if bt then e || m else P || m))).writeW (off B (8 * kV))
        (V + V)).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (n - 1)) ∧ t.zf = some (decide (n - 1 = 0)) ∧
      Keep [.rax, .rdx, .rbp, .r15] s t := by
  have := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r15] (Q := fun t => t.mem = ((s.mem.writeW (off B (8 * kFlag))
      (mask (if bt then e || m else P || m))).writeW (off B (8 * kV)) (V + V)).writeW (off B (8 * kBits))
      (BitVec.ofNat 64 (n - 1)) ∧ t.zf = some (decide (n - 1 = 0))) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kV (by decide), hl kG (by decide), hl kFlag (by decide),
      hl kBits (by decide), hs kV (by decide), hs kFlag (by decide), hs kBits (by decide), hV, hG, hP, hbp, hbt,
      neg_bit, sxm1', flag_mask, fun X => (hdrStore_hdr s.mem B X (show kFlag < 32 by decide) (show kV < 32 by decide)
        (by decide)).trans hV,
      fun X Y => (hdrStore_hdr _ B Y (show kV < 32 by decide) (show kBits < 32 by decide) (by decide)).trans
        ((hdrStore_hdr s.mem B X (show kFlag < 32 by decide) (show kBits < 32 by decide) (by decide)).trans hnb),
      ofNat64_pred hn1 hn', ofNat64_beq_zero (show n - 1 < 2 ^ 64 by omega)]) rfl) fun t ⟨⟨hm, hz⟩, k⟩ => ⟨hm, hz, k⟩

/-- The header survives changes away from its first 16 words. -/
theorem _root_.VG.Proof.Bignum.Hdr.of_frm {m m' : Mem} {B : Addr} {w : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)} (hH : Hdr m B w mi)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, 128 ≤ r.1) : Hdr m' B w mi := by
  have hh : ∀ i < 16, word m' B (8 * i) = word m B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => Or.inl (by have := hd r hr; omega)) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- `MrCtx` survives changes away from what it keeps. -/
theorem MrCtx.of_frm {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B rs s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) (hh : ∀ r ∈ rs, 128 ≤ r.1)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (dB : ∀ r ∈ rs, slot w aB + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aB)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1) :
    MrCtx t B Z w mi c bm := by
  have hn := hc.good.scr.nowrap
  have hx := hd.x
  have hb : slot w aRm1 + 8 * (w + 2) ≥ slot w aB + 8 * w := by unfold slot aRm1 aB; omega
  have hb1 : slot w aRm1 + 8 * (w + 2) ≥ slot w aR1 + 8 * w := by unfold slot aRm1 aR1; omega
  have hb0 : slot w aRm1 + 8 * (w + 2) ≥ slot w aN + 8 * w := by unfold slot aRm1 aN; omega
  have h128 : 128 ≤ slot w aN := by unfold slot aN hdrBytes; omega
  refine ⟨⟨hs, hdi, Hdr.of_frm hc.good.hdr hf hh⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have := hd.w4
    rw [hf.word_eq (d := slot w aN) (fun r hr => by have := dN r hr; omega) (by omega)]; exact hc.inv
  · rw [hf.wv_eq dN (by omega)]; exact hc.n
  · rw [hf.wv_eq dB (by omega)]; exact hc.b
  · rw [hf.wv_eq d1 (by omega)]; exact hc.r1
  · rw [hf.wv_eq dm (by omega)]; exact hc.rm1

end VG.Proof.RsaKeyGen.X86_64
