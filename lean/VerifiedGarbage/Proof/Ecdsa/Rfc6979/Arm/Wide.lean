module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
public import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Spec.Rc2

/-!
# Deterministic ECDSA on 32-bit ARM: P-521's shifts

For a curve whose order has fewer bits than its scalars' bytes (`wide`:
P-521's 521 bits in 66 bytes): the `Q` bytes at an offset in the frame,
shifted right in place through the words at `scratch + 2560` (`conv_ok`, by
`loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`, with `out` and `d` kept in
`r2` and `r3` meanwhile, as those use `r4` and `r5`), for `core`'s digest
and for the candidate.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.Arm (Scr)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_imm dpVal)
open VG.Proof.Weierstrass.Arm (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

/-- `scratch`'s first 4096 bytes, as the conversions address them from `r12`. -/
theorem scr_of (hL : L.Ok) {t : State} (hwr : t.wr = [L.FR, L.OUT, L.SCR]) (h12 : t.gpr .r12 = L.scr) :
    Scr t (State.addr L.scr) 4096 :=
  ⟨by rw [h12], ⟨8192, by omega_arith, by omega_arith, by rw [hwr]; simp⟩, by have := hL.nc; rw [toNat_addr]; omega_arith,
    Nat.le_refl _⟩

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (h12 : s'.gpr .r12 = s.gpr .r12)
    (hwr : s'.wr = s.wr) : Scr s' base size :=
  ⟨h12 ▸ h.wb, hwr ▸ h.wr, h.nowrap, h.small⟩

theorem allOnes_movt : ((0xffff : BitVec 16) ++ ((0xffff : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    BitVec.allOnes 32 := by decide

/-- `conv o s`: the `Q` bytes at `r8 + o`, in the frame, shifted right by `s`
bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    {o s : Nat} (ho₂ : o + 66 ≤ 396) (hoe : encodable (BitVec.ofNat 32 o) = true) (hs₁ : 1 ≤ s)
    (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → t'.gpr r = t.gpr r) ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66⟩ := P.sizesW hW
  have nB := hL.nB
  have nc := hL.nc
  have hfp := fp_fit hL
  have := L.sp.isLt
  have hw2 : (cfgOf P).w / 2 = P.w := by
    simp only [cfgOf, cfgR, show P.R.E.C.len = 66 from hQ66, show P.R.E.n = 9 from hw9]; decide
  have hlen : (cfgOf P).len = P.Q := rfl
  simp only [Cfg.conv, hw2, hlen, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun u₁ v₁ => wp_mov (op2_reg _ _) fun u₂ v₂ => ?_
  refine wp_dp (op2_imm hoe) fun u₃ v₃ => wp_mov (op2_reg _ _) fun u₄ v₄ => ?_
  have K₄ : Rest [.r1, .r2, .r3, .r12] t u₄ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans (v₄.rest (by simp))
  have h12 : u₄.gpr .r12 = L.scr := by
    rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hc.r11]
  have hS₄ : Scr u₄ (State.addr L.scr) 4096 := scr_of hL (by rw [K₄.wr, hc.wr]) h12
  have hr1 : u₄.gpr .r1 = L.fp + BitVec.ofNat 32 o := by
    rw [v₄.other _ (by decide), v₃.gpr, dpVal, v₂.other _ (by decide), v₁.other _ (by decide), hc.r8]
  have ha₁ : State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 (24 + o) := hL.fpA (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (loadBytes_ok hS₄ (len := P.Q) (n := P.w) (o := 2560) (src := .r1) (by decide) (by omega_arith)
    (by rw [hr1, fp_toNat hL (by omega_arith)]; have := hL.nA; omega_arith) (by omega_arith) (by omega_arith)
    (fun d hd => by rw [hr1, ha₁, Offset.add_add, K₄.rd, K₄.wr]; exact hc.inFr (by omega_arith) (by omega_arith))
    (by rw [hr1, ha₁]; exact (hL.stk_scr (by omega_arith) (by omega_arith)))) fun u₅ ⟨hv₅, k₅, O₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shrWords_ok (scr_keep hS₄ (k₅.gpr _ (by decide)) k₅.wr) (n := P.w) (o := 2560) (sh := s)
    (by omega_arith) hs₁ hs₂) fun u₆ ⟨hv₆, k₆, O₆⟩ => ?_
  refine wp_movw fun u₇ v₇ => wp_movt fun u₈ v₈ => ?_
  have h10 : u₈.gpr .r10 = BitVec.allOnes 32 := by rw [v₈.gpr, v₇.gpr]; exact allOnes_movt
  have K₈ : Rest [.r4, .r5, .r10] u₅ u₈ :=
    (k₆.mono (by simp)).trans <| (v₇.rest (by simp)).trans (v₈.rest (by simp))
  have hS₈ : Scr u₈ (State.addr L.scr) 4096 := scr_keep hS₄
    (by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide)]) (by rw [K₈.wr, k₅.wr])
  have h8 : u₈.gpr .r8 = L.fp := by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide), K₄.gpr _ (by decide), hc.r8]
  have hdst : State.addr (u₈.gpr .r8) + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by
    rw [h8, hL.fpA0, Offset.add_add]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hS₈ (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .r8) (by decide)
    (by decide) true (by rw [h10]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [h8]; omega_arith) (by omega_arith)
    (fun e m hem => by
      rw [hdst, Offset.add_add, K₈.wr, k₅.wr, K₄.wr]; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₉ ⟨hb₉, k₉, O₉⟩ => ?_
  rw [hdst] at hb₉ O₉
  refine wp_mov (op2_reg _ _) fun u₁₀ v₁₀ => wp_mov (op2_reg _ _) fun u₁₁ v₁₁ => WP.block_nil ?_
  -- Through the conversion, every register but those it writes.
  have K : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r10 → r ≠ .r12 →
      u₉.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 h10' h12' => by
    rw [k₉.gpr _ (by simp [h4, h5]), K₈.gpr _ (by simp [h4, h5, h10']), k₅.gpr _ (by simp [h4]),
      K₄.gpr _ (by simp [h1, h2, h3, h12'])]
  have hr2 : u₉.gpr .r2 = t.gpr .r4 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  have hr3 : u₉.gpr .r3 = t.gpr .r5 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide)]
  have hg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → u₁₁.gpr r = t.gpr r :=
    fun r h1 h2 h3 h10' h12' => by
      by_cases h4 : r = .r4
      · subst h4; rw [v₁₁.other _ (by decide), v₁₀.gpr, hr2]
      by_cases h5 : r = .r5
      · subst h5; rw [v₁₁.gpr, v₁₀.other _ (by decide), hr3]
      rw [v₁₁.other _ h5, v₁₀.other _ h4, K r h1 h2 h3 h4 h5 h10' h12']
  have m₄ : u₄.mem = t.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have m₈ : u₈.mem = u₆.mem := by rw [v₈.mem, v₇.mem]
  have hm : u₁₁.mem = u₉.mem := by rw [v₁₁.mem, v₁₀.mem]
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩]
      t.mem u₁₁.mem := by
    have f₅ := frame_of_outside (O₅.trans O₆) (by omega_arith)
    have f₉ := frame_of_outside O₉ (by omega_arith)
    rw [BitVec.add_zero, m₈] at f₉
    rw [show 8 * P.w = 72 by omega_arith, m₄] at f₅
    rw [hm]
    exact (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₉.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hp : ∀ r ∈ ptrRegs, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r10 ∧ r ≠ .r12 := by decide
  refine ⟨hc.keep hL (by rw [v₁₁.rd, v₁₀.rd, k₉.rd, K₈.rd, k₅.rd, K₄.rd])
      (by rw [v₁₁.wr, v₁₀.wr, k₉.wr, K₈.wr, k₅.wr, K₄.wr]) (by rw [v₁₁.sp, v₁₀.sp, k₉.sp, K₈.sp, k₅.sp, K₄.sp])
      (fun r hr => hg r (hp r hr).1 (hp r hr).2.1 (hp r hr).2.2.1 (hp r hr).2.2.2.1 (hp r hr).2.2.2.2) hf
      fun r hr => ?_, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_low L (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₉
    simp only [ite_true] at hb₉
    rw [hm, hb₉, m₈, hv₆, hv₅, hr1, ha₁, ecdsa_bytesAt, m₄]

end VG.Proof.Ecdsa.Rfc6979.Arm
