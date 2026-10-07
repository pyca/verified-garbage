import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub

/-!
# A candidate on x86-64: copies and differences of arrays

`copyB_ok`: `copyWords` between two arrays of the scratch space;
`copyToExt_ok` and `copyFromExt_ok` with the bases loaded, from an array to
an extra one and back; `subB_ok`: the borrow loop `[t] := [a] − [n]`.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `copyWords` from `w` words at `eS` to `eD`, both in the scratch space. -/
theorem copyB_ok {s : State} {B : Addr} {Z w eS eD : Nat} (hs : Scr s B Z) (hsi : s.gpr .rsi = off B eS)
    (hbx : s.gpr .rbx = off B eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hS : eS + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z) (hsep : eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD) :
    WP isa copyWords s fun t => wv t.mem B eD w = wv s.mem B eS w ∧ Outside B eD (8 * w) s.mem t.mem ∧
      Keep [.rax, .r14] s t := by
  have hn := hs.nowrap
  exact WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega) (fun j hj => hs.ld (by omega))
    (fun j hj => hs.st (by omega)) (fun j hj b hb => by rw [ofs_off B (by omega)]; omega))
    fun t ⟨hv, _, ho, k⟩ => ⟨hv, ho, k⟩

/-- `[d] := [a]` for an array `a` and an extra array `d`. -/
theorem copyToExt_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a d : Nat} (ha : a < 8) (hd : 7 < d)
    (hdZ : slot w d + 8 * (w + 2) ≤ Z) :
    WP isa (seqs [.block (([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a)))] : List Instr) ++ extBase d .rbx),
      copyWords]) s fun t => wv t.mem B (slot w d) w = wv s.mem B (slot w a) w ∧
      Outside B (slot w d) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbx, .rsi, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sA := Nat.le_trans (slot_le (w := w) ha) hZ
  have hsep : slot w a + 8 * (w + 2) ≤ slot w d := by
    have := slot_le (w := w) ha
    have : slot w 8 ≤ slot w d := by unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    omega
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rsi] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w a) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr a) (by unfold sArr; omega), hg.hdr.hw,
      hg.hdr.harr a ha]) rfl) fun s₁ ⟨⟨h12, hsi, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := d) (by omega) (r := .rbx) (by decide) rfl rfl)
    fun s₂ ⟨hbx, hm₂, k₂⟩ => ?_
  refine WP.mono (copyB_ok (hg₁.scr.congr k₂.2.2) ((k₂.gpr (by decide)).trans hsi) hbx
    ((k₂.gpr (by decide)).trans h12) hw hw' (by omega) (by omega) (Or.inr (by omega)))
    fun t ⟨hv, ho, k⟩ => ⟨by rw [hv, hm₂, hm₁], by rw [hm₂, hm₁] at ho; exact ho, ((k₁.trans k₂).trans k).mono (by decide)⟩

/-- `[a] := [d]` for an extra array `d` and an array `a`. -/
theorem copyFromExt_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a d : Nat} (ha : a < 8) (hd : 7 < d)
    (hdZ : slot w d + 8 * (w + 2) ≤ Z) :
    WP isa (seqs [.block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr a)))] : List Instr) ++ extBase d .rsi),
      copyWords]) s fun t => wv t.mem B (slot w a) w = wv s.mem B (slot w d) w ∧
      Outside B (slot w a) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbx, .rsi, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sA := Nat.le_trans (slot_le (w := w) ha) hZ
  have hsep : slot w a + 8 * (w + 2) ≤ slot w d := by
    have := slot_le (w := w) ha
    have : slot w 8 ≤ slot w d := by unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    omega
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w a) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr a) (by unfold sArr; omega), hg.hdr.hw,
      hg.hdr.harr a ha]) rfl) fun s₁ ⟨⟨h12, hbx, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := d) (by omega) (r := .rsi) (by decide) rfl rfl)
    fun s₂ ⟨hsi, hm₂, k₂⟩ => ?_
  refine WP.mono (copyB_ok (hg₁.scr.congr k₂.2.2) hsi ((k₂.gpr (by decide)).trans hbx)
    ((k₂.gpr (by decide)).trans h12) hw hw' (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨hv, ho, k⟩ => ⟨by rw [hv, hm₂, hm₁], by rw [hm₂, hm₁] at ho; exact ho, ((k₁.trans k₂).trans k).mono (by decide)⟩

end VG.Proof.RsaKeyGen.X86_64
