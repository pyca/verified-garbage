module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # An RSA key on ARMv7: halvings under a mask, words of constants, a flag cleared -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

section
variable {P : KP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `r11 := 0`. -/
theorem St.pmov11 : VP (St P E A L V LS) (.block [.mov .r11 (.imm 0)])
    (fun σ s => St P E A L V LS σ s ∧ s.gpr .r11 = 0) :=
  VP.kv mov11_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
    wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_rest (u.rest (ws := [.r11]) (by simp)) u.mem,
      hw.of_upd u (by decide) (by decide) (by decide)⟩, u.gpr⟩

/-- `half aTmp2` with `r11 = 0`: `[aTmp2] := [aTmp2] / 2`. -/
theorem St.phalfT2 (h2 : aTmp2 ∈ L) :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r11 = 0) (half aTmp2)
      (St P E (fun σ => upd (A σ) aTmp2 (A σ aTmp2 / 2)) (aTmp2 :: L) V LS) :=
  VP.kv halfT2_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r11⟩ =>
    WP.mono (half_ok hw (j := aTmp2) (by decide) (by decide) (by rw [r11]; decide)) fun t ⟨ht, k, v, r⟩ =>
      ⟨e, h.write1 k (by decide) (by simp) r.sp r.rd r.wr (by
        rw [v, r11, h.arrs aTmp2 h2]; simp) (by simp), ht⟩

/-- `halfSel j`: `[j]` halved if the header word `sH` is 1. -/
theorem St.phalfSel {j : Nat} (c1 : Cert (copy aTmp j)) (c2 : Cert (copy aTmp2 j)) (cs : Cert (sel j aTmp aTmp2 sH))
    (hj : j ∈ L) (hjN : j < nArr) (h1 : aTmp ∉ L) (h2 : aTmp2 ∉ L) (hH : sH ∈ LS) (bit : ∀ σ, E σ → V σ sH ≤ 1) :
    VP (St P E A L V LS) (halfSel j)
      (St P E (fun σ => upd (A σ) j (if V σ sH = 0 then A σ j else A σ j / 2)) (j :: L) V LS) := by
  have j1 : j ≠ aTmp := fun x => h1 (x ▸ hj)
  have j2 : j ≠ aTmp2 := fun x => h2 (x ▸ hj)
  simp only [halfSel, seqs]
  refine VP.seq (St.pcopy c1 (by decide) hj (Ne.symm j1)) ?_
  refine VP.seq (St.pcopy c2 (by decide) (List.mem_cons_of_mem _ hj) (Ne.symm j2)) ?_
  refine VP.seq St.pmov11 (VP.seq (St.phalfT2 (by simp)) ?_)
  refine (St.psel cs hjN (by simp) (by simp) j1 j2 hH bit).mono (fun _ _ h => h) fun σ s h =>
    h.mono (fun i hi => ⟨?_, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  · rcases List.mem_cons.mp hi with rfl | hi
    · simp
    · simp [hi]
  · have v1 : upd (upd (upd (A σ) aTmp (A σ j)) aTmp2 (upd (A σ) aTmp (A σ j) j)) aTmp2
        (upd (upd (A σ) aTmp (A σ j)) aTmp2 (upd (A σ) aTmp (A σ j) j) aTmp2 / 2) aTmp = A σ j := by
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
    have v2 : upd (upd (upd (A σ) aTmp (A σ j)) aTmp2 (upd (A σ) aTmp (A σ j) j)) aTmp2
        (upd (upd (A σ) aTmp (A σ j)) aTmp2 (upd (A σ) aTmp (A σ j) j) aTmp2 / 2) aTmp2 = A σ j / 2 := by
      rw [upd_self, upd_self, upd_ne _ _ j1]
    rw [v1, v2]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [upd_self, upd_self]
    · have i0 : i ≠ aTmp := fun x => h1 (x ▸ hi)
      have i2 : i ≠ aTmp2 := fun x => h2 (x ▸ hi)
      by_cases ij : i = j
      · subst ij; rw [upd_self, upd_self]
      · rw [upd_ne _ _ ij, upd_ne _ _ ij, upd_ne _ _ i2, upd_ne _ _ i2, upd_ne _ _ i0]

/-- `setWd j o x`: word `o / 4` of `[j]` := `x`, above the number. -/
theorem St.psetWd {j o x : Nat} (cert : Cert (.block (setWd j o x))) (hj : j ∈ L) (ho : o % 4 = 0)
    (how : o / 4 < 20) (hx : encodable (BitVec.ofNat 32 x) = true)
    (hl : ∀ σ, E σ → A σ j < 2 ^ (32 * (o / 4))) :
    VP (St P E A L V LS) (.block (setWd j o x))
      (St P E (fun σ => upd (A σ) j (A σ j + 2 ^ (32 * (o / 4)) * (x % 2 ^ 32))) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (setWd j o x)]
    have hj' := h.live_lt j hj
    refine setWd_ok hw hj' (by decide) ho (by have := h.pre.wge; omega) hx (by rw [h.arrs j hj]; exact hl σ e)
      fun t ht k v r => WP.block_nil ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, h.arrs j hj]) (by simp),
        ht⟩

/-- `setHi j sh c x`: word `i` of `[j]` := `x`, above the number, for `W 2^sh = 4 i + c`. -/
theorem St.psetHi {j sh c x : Nat} {i : KP → Nat} (cert : Cert (.block (setHi j sh c x))) (hj : j ∈ L)
    (hsh : 1 ≤ sh ∧ sh ≤ 2) (hc : encodable (BitVec.ofNat 32 c) = true) (hx : encodable (BitVec.ofNat 32 x) = true)
    (hi : ∀ σ, E σ → In P σ → P.W * 2 ^ sh = 4 * i P + c ∧ i P < P.W)
    (hl : ∀ σ, E σ → In P σ → A σ j < 2 ^ (32 * i P)) :
    VP (St P E A L V LS) (.block (setHi j sh c x))
      (St P E (fun σ => upd (A σ) j (A σ j + 2 ^ (32 * i P) * (x % 2 ^ 32))) (j :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    rw [← List.append_nil (setHi j sh c x)]
    have hj' := h.live_lt j hj
    obtain ⟨i1, i2⟩ := hi σ e h.pre
    refine setHi_ok hw hj' (by decide) hsh hc hx i1 i2 (by rw [h.arrs j hj]; exact hl σ e h.pre)
      fun t ht k v r => WP.block_nil ⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, h.arrs j hj]) (by simp),
        ht⟩

/-- `dZero`: the flag `sOk := 0`. -/
theorem St.pdZero : VP (St P E A L V LS) (.block dZero)
    (St P E A L (fun σ => upd (V σ) sOk (b2n false)) (sOk :: LS)) :=
  VP.kv dZero_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    unfold dZero
    refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
    have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
    have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
    refine h1.str hw1 (by decide) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    rwa [u1.gpr] at ht

end

end VG.Proof.RsaKeyGen.Arm.Key
