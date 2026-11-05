module
-- separate module: its proofs (the buffers X and h) build in parallel with `Steps`, which `Cand` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Wide
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: the digest into `X`

The byte loop `copyLoop`, `r6` bytes from `r4` to `r5` with `Ctx` kept, for
a destination the code may write apart from the source (`cp_ok`), and `X`
(`prepX_ok`): `Q - m` zero bytes, then the digest's first `m = min(D, Q)`,
its length the smaller of the frame's `D` and `Q` (`minDQ_ok`, without a
branch: the borrow of `D - Q` as a mask, `subc` then `sube`). If `big`
(P-521): `core`'s digest, `Q - 1 - D` zero bytes, the digest and a zero
byte, shifted right by `8 - sh` bits, which is the digest's number shifted
left by `sh` bits (`prepC_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Impl.RsaOaep.PPC64LE (copyLoop)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## Steps with the carry -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem stepSubc {d n m : Reg}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem →
      s'.gpr d = BitVec.ofNat 64 ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + 1) →
      s'.ca = decide (2 ^ 64 ≤ (s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.subc d n m :: is)) s Q :=
  VG.Proof.Mont.PPC64LE.wp_step exec_subc (k _ ⟨(Kp.write s _ (List.mem_singleton_self d)).gpr, rfl, rfl, rfl, rfl⟩
    rfl (by simp [State.writeCarry, State.write]) rfl)

theorem stepSube {d n m : Reg}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem →
      s'.gpr d = BitVec.ofNat 64 ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + s.ca.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.sube d n m :: is)) s Q :=
  VG.Proof.Mont.PPC64LE.wp_step exec_sube (k _ ⟨(Kp.write s _ (List.mem_singleton_self d)).gpr, rfl, rfl, rfl, rfl⟩
    rfl (by simp [State.writeCarry, State.write]))

end

/-! ## Bytes -/

theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    (Spec.Sha256.bytesAt m p k).take n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- `k` zero doublewords at `r11 + o + 8 j`, `r9 = 0`. -/
theorem zeros_ok {o : Nat} (ho : 96 + o + 72 ≤ 688) (ho' : 232 ≤ o) (ho4 : o % 4 = 0) :
    ∀ k ≤ 9, ∀ (u : State), u.gpr .r11 = L.B + BitVec.ofNat 64 96 → u.gpr .r9 = 0 →
      (∀ j < 9, InRegions u.wr (L.B + BitVec.ofNat 64 (96 + o + 8 * j)) 8) →
      WP isa (.block ((List.range k).map fun j => .store .d .r9 .r11 (o + 8 * j))) u fun u' =>
        Kp [] u u' ∧ Frame [⟨L.B + BitVec.ofNat 64 (96 + o), 72⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (96 + o)) (8 * k) = List.replicate (8 * k) 0
  | 0, _, u, _, _, _ => wp_nil ⟨Kp.refl _ _, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, h11, h9, hw => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeros_ok ho ho' ho4 k (by omega) u h11 h9 hw) fun u₁ ⟨k₁, f₁, b₁⟩ => ?_
    refine stepStd (a := L.B + BitVec.ofNat 64 (96 + o + 8 * k)) (by decide) ⟨by omega, by omega⟩
      (by rw [k₁.gpr _ (by decide), h11, fr_add, Nat.add_assoc]) (by rw [k₁.wr]; exact hw k (by omega))
      fun u₂ k₂ g₂ m₂ => wp_nil ⟨k₁.trans k₂, ?_, ?_⟩
    · refine f₁.trans ?_
      rw [m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega)
        (by have := (L.B).isLt; omega))
    · rw [m₂, k₁.gpr _ (by decide), h9, show 8 * (k + 1) = 8 * k + 8 by omega, Proof.Hmac.Common.bytesAt_add,
        Offset.add_add, ← List.replicate_append_replicate, bytesAt_writeW_zero _ _ (Nat.le_refl _)]
      refine congrArg (· ++ _) ?_
      rw [← b₁]
      exact bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega)

/-- `Q ^ ((D ^ Q) & mask)`: `D` with the mask all ones, `Q` with it zero. -/
theorem sel_min {d q : Nat} (_hd : d < 2 ^ 63) (hq : q < 2 ^ 63) :
    BitVec.ofNat 64 q ^^^ ((BitVec.ofNat 64 d ^^^ BitVec.ofNat 64 q) &&&
      BitVec.ofNat 64 ((d + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (d + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
        (decide (2 ^ 64 ≤ d + (2 ^ 64 - 1 - q) + 1)).toNat)) = BitVec.ofNat 64 (min d q) := by
  by_cases h : q ≤ d
  · rw [decide_eq_true (by omega : 2 ^ 64 ≤ d + (2 ^ 64 - 1 - q) + 1), Nat.min_eq_right h]
    rw [show (d + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (d + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
      (true).toNat = 2 ^ 64 by simp only [Bool.toNat_true]; omega, show BitVec.ofNat 64 (2 ^ 64) = 0#64 from rfl,
      BitVec.and_zero, BitVec.xor_zero]
  · rw [decide_eq_false (by omega : ¬ 2 ^ 64 ≤ d + (2 ^ 64 - 1 - q) + 1), Nat.min_eq_left (by omega)]
    rw [show (d + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (d + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
      (false).toNat = 2 ^ 64 - 1 by simp only [Bool.toNat_false]; omega,
      show BitVec.ofNat 64 (2 ^ 64 - 1) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_comm (BitVec.ofNat 64 q), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `r6 = min(D, Q)`, with the frame in `r11`: `r9`, `r10` and `r12` change. -/
theorem minDQ_ok {t : State} (h11 : t.gpr .r11 = L.B + BitVec.ofNat 64 96)
    (hdl : t.mem.readW (L.B + BitVec.ofNat 64 304) 64 = BitVec.ofNat 64 P.v.H.D)
    (hin : InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 304) 8) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Kp [.r6, .r9, .r10, .r12] t u → u.mem = t.mem → u.gpr .r6 = BitVec.ofNat 64 (min P.v.H.D P.Q) →
      WP isa (.block is) u Q) :
    WP isa (.block ((cfgOf P).minDQ ++ is)) t Q := by
  have hs := P.sizes
  simp only [Cfg.minDQ, List.cons_append, List.nil_append]
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide) (by rw [h11, fr_add]; rfl)
    hin fun t₁ k₁ m₁ v₁ => ?_
  refine stepLi (show (cfgOf P).len < 2 ^ 15 by show P.Q < _; omega) fun t₂ k₂ m₂ v₂ => ?_
  refine stepSubc fun t₃ k₃ m₃ v₃ c₃ => ?_
  refine stepSube fun t₄ k₄ m₄ v₄ => ?_
  refine stepXor fun t₅ k₅ m₅ v₅ => ?_
  refine stepAnd fun t₆ k₆ m₆ v₆ => ?_
  refine stepXor fun t₇ k₇ m₇ v₇ => ?_
  refine k t₇ (((((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono).trans
    k₇.mono)) (by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]) ?_
  have e6 : t₂.gpr .r6 = BitVec.ofNat 64 P.v.H.D := by rw [k₂.gpr _ (by decide), v₁, hdl]
  have e9 : t₂.gpr .r9 = BitVec.ofNat 64 P.Q := v₂
  have hD : (BitVec.ofNat 64 P.v.H.D).toNat = P.v.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hQ : (BitVec.ofNat 64 P.Q).toNat = P.Q := by rw [BitVec.toNat_ofNat]; omega
  have a9 : t₆.gpr .r9 = BitVec.ofNat 64 P.Q := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), e9]
  have a12 : t₆.gpr .r12 = (BitVec.ofNat 64 P.v.H.D ^^^ BitVec.ofNat 64 P.Q) &&& t₄.gpr .r10 := by
    rw [v₆, v₅, k₅.gpr .r10 (by decide), k₄.gpr .r6 (by decide), k₃.gpr .r6 (by decide), e6,
      k₄.gpr .r9 (by decide), k₃.gpr .r9 (by decide), e9]
  have a10 : t₄.gpr .r10 = BitVec.ofNat 64 ((P.v.H.D + (2 ^ 64 - 1 - P.Q) + 1) % 2 ^ 64 +
      (2 ^ 64 - 1 - (P.v.H.D + (2 ^ 64 - 1 - P.Q) + 1) % 2 ^ 64) +
      (decide (2 ^ 64 ≤ P.v.H.D + (2 ^ 64 - 1 - P.Q) + 1)).toNat) := by
    rw [v₄, v₃, c₃, e6, e9, hD, hQ, BitVec.toNat_ofNat]
  rw [v₇, a9, a12, a10]
  exact sel_min (by omega) (by omega)

/-! ## `X` -/

theorem sub_min (B : Addr) {a b c : Nat} (h : c ≤ b) :
    B + BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 c = B + BitVec.ofNat 64 (a + (b - c)) := by
  rw [show a + b = a + (b - c) + c by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- The frame's base in `r11`, `r9 = 0` and nine zero doublewords at `o`. -/
theorem zero9_ok {t : State} (hc : Ctx L g lr m₀ t) {o : Nat} (ho : 96 + o + 72 ≤ 688) (ho' : 232 ≤ o)
    (ho4 : o % 4 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Kp [.r9, .r11] t u → Frame [⟨L.B + BitVec.ofNat 64 (96 + o), 72⟩] t.mem u.mem →
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + o)) 72 = List.replicate 72 0 →
      u.gpr .r11 = L.B + BitVec.ofNat 64 96 → WP isa (.block is) u Q) :
    WP isa (.block (.addSp .r11 0 :: Cfg.zero9 o ++ is)) t Q := by
  simp only [Cfg.zero9, List.cons_append]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLi (by decide) fun t₂ k₂ m₂ v₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok (L := L) ho ho' ho4 9 (Nat.le_refl _) t₂ (by rw [k₂.gpr _ (by decide), hb]) v₂
    (fun j hj => by rw [k₂.wr, k₁.wr]; exact hc.inFrW (by omega) (by omega))) fun u ⟨k₃, f₃, b₃⟩ => ?_
  exact k u ((k₁.mono.trans k₂.mono).trans k₃.mono) (by rw [m₂, m₁] at f₃; exact f₃) b₃
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb])

/-- The arguments of `X`'s copy: `X` cleared, `r6 = m = min(D, Q)`, the
digest in `r4`, `X + Q - m` in `r5`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fX)) 72 = List.replicate 72 0 ∧
      u.gpr .r6 = BitVec.ofNat 64 (min P.v.H.D P.Q) ∧
      u.gpr .r5 = L.B + BitVec.ofNat 64 (96 + fX + (P.Q - min P.v.H.D P.Q)) ∧ u.gpr .r4 = L.dg := by
  have hs := P.sizes
  simp only [Cfg.xArgs, List.cons_append, List.append_assoc]
  refine WP.of_syms (zero9_ok hc (o := fX) (by decide) (by decide) (by decide) fun u₁ k₁ f₁ b₁ h11 => ?_)
  have hX : ∀ {d : Nat}, d + 8 ≤ 400 ∨ 472 ≤ d → d + 8 ≤ 736 →
      u₁.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    f₁.readW (r := ⟨L.B + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by simp only [fX]; omega) (by omega) (by simp only [fX]; omega)) (by decide)
  refine minDQ_ok h11 ((hX (d := 304) (by omega) (by omega)).trans (hc.dl hT))
    (by rw [k₁.rd, k₁.wr]; exact hc.inFr (by omega) (by omega)) fun u₂ k₂ m₂ v₂ => ?_
  refine stepAddSp (show fX + (cfgOf P).len < 2 ^ 15 by show fX + P.Q < _; simp only [fX]; omega)
    fun u₃ k₃ m₃ v₃ => ?_
  refine stepSub fun u₄ k₄ m₄ v₄ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 280) (by decide) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), h11, fr_add]; rfl)
    (by rw [k₄.rd, k₄.wr, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hc.inFr (by omega) (by omega))
    fun u₅ k₅ m₅ v₅ => wp_nil fun hsy => ?_
  have K : Kp [.r4, .r5, .r6, .r9, .r10, .r11, .r12] t u₅ :=
    (((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono
  have hm : u₅.mem = u₁.mem := by rw [m₅, m₄, m₃, m₂]
  have hmin : min P.v.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [preserved] at hr))
    (hm ▸ f₁) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by decide) (by decide))
    hsy, hm ▸ f₁, hm ▸ b₁, by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂], ?_, ?_⟩
  · rw [k₅.gpr _ (by decide), v₄, v₃, k₃.gpr _ (by decide), v₂, k₂.sp, k₁.sp, hc.sp, fr_add,
      show (cfgOf P).len = P.Q from rfl, ← Nat.add_assoc, sub_min _ hmin]
  · rw [v₅, m₄, m₃, m₂, hX (d := 280) (by omega) (by omega), hc.pDg]

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.v.H.D ≤ dn) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fX)) P.Q =
        List.replicate (P.Q - min P.v.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min P.v.H.D P.Q) := by
  have hnB := hL.nB
  have hng := hL.ng
  have hs := P.sizes
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, h6, h5, h4⟩ => ?_)
  have hm : min P.v.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  have hm8 : 16 ≤ min P.v.H.D P.Q := by omega
  have hdn' : min P.v.H.D P.Q ≤ dn := by omega
  refine WP.mono (cp_ok hL hc₅ (p := L.B + BitVec.ofNat 64 (96 + fX + (P.Q - min P.v.H.D P.Q))) (q := L.dg)
      (n := min P.v.H.D P.Q) (by omega) (by omega) h4 h5 h6
      (fun i hi => by rw [Offset.add_add]; exact hc₅.inFrW (n := 1) (by simp only [fX]; omega) (by simp only [fX]; omega))
      (safe_high L (by simp only [fX]; omega) (by simp only [fX]; omega))
      (fun i hi => hc₅.inDg (o := i) (n := 1) (by omega) (by omega))
      ((hL.kg.symm.sub_left (Region.sub_prefix hdn')).sub_right (Offset.sub_base _ (by simp only [fX]; omega)))
      (by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by simp only [fX]; omega), Nat.mod_eq_of_lt (by simp only [fX]; omega)]
          simp only [fX]; omega))
    fun u ⟨hc', _, hf, hb⟩ => ?_
  have hdg : Spec.Sha256.bytesAt u₅.mem L.dg (min P.v.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.v.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.kg.symm.sub_left (Region.sub_prefix hdn')).sub_right (Offset.sub_base _ (by simp only [fX]; omega)))
      (by omega)
  refine ⟨hc', hf₁.trans ?_, ?_⟩
  · exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by simp only [fX]; omega)⟩
  · rw [show P.Q = (P.Q - min P.v.H.D P.Q) + min P.v.H.D P.Q by omega, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, hb, ← show P.Q = (P.Q - min P.v.H.D P.Q) + min P.v.H.D P.Q by omega,
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by simp only [fX]; omega) (by simp only [fX]; omega)) (by omega),
      hdg]
    rw [← bytesAt_take _ _ (k := 72) (by omega), hb₁, List.take_replicate, Nat.min_eq_left (by omega)]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `big`: the arguments of the copy of `core`'s digest: it cleared, `r6 = D`,
the digest in `r4`, `fXc + Q - 1 - D` in `r5`. -/
theorem xcArgs_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fXc)) 72 = List.replicate 72 0 ∧
      u.gpr .r6 = BitVec.ofNat 64 P.v.H.D ∧ u.gpr .r5 = L.B + BitVec.ofNat 64 (96 + fXc + (P.Q - 1 - P.v.H.D)) ∧
      u.gpr .r4 = L.dg := by
  have hnB := hL.nB
  obtain ⟨hw9, hQ66, hQD⟩ := P.sizesW hW
  have hs := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  simp only [Cfg.xcArgs, List.cons_append]
  refine WP.of_syms (zero9_ok hc (o := fXc) (by decide) (by decide) (by decide) fun u₁ k₁ f₁ b₁ h11 => ?_)
  have hX : ∀ {d : Nat}, d + 8 ≤ 472 ∨ 544 ≤ d → d + 8 ≤ 736 →
      u₁.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    f₁.readW (r := ⟨L.B + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by simp only [fXc]; omega) (by omega) (by simp only [fXc]; omega)) (by decide)
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide) (by rw [h11, fr_add]; rfl)
    (by rw [k₁.rd, k₁.wr]; exact hc.inFr (by omega) (by omega)) fun u₂ k₂ m₂ v₂ => ?_
  refine stepAddSp (show fXc + (cfgOf P).len - 1 < 2 ^ 15 by rw [hlen]; simp only [fXc]; omega)
    fun u₃ k₃ m₃ v₃ => ?_
  refine stepSub fun u₄ k₄ m₄ v₄ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 280) (by decide) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), h11, fr_add]; rfl)
    (by rw [k₄.rd, k₄.wr, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hc.inFr (by omega) (by omega))
    fun u₅ k₅ m₅ v₅ => wp_nil fun hsy₅ => ?_
  have K₅ : Kp [.r4, .r5, .r6, .r9, .r11] t u₅ :=
    (((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono
  have hm₅ : u₅.mem = u₁.mem := by rw [m₅, m₄, m₃, m₂]
  have hc₅ : Ctx L g lr m₀ u₅ := hc.keep hL K₅.rd K₅.wr K₅.sp (fun r hr => K₅.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [preserved] at hr))
    (hm₅ ▸ f₁) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by decide) (by decide))
    hsy₅
  have h6 : u₅.gpr .r6 = BitVec.ofNat 64 P.v.H.D := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, hX (d := 304) (by omega) (by omega),
      hc.dl hT]
  have h5 : u₅.gpr .r5 = L.B + BitVec.ofNat 64 (96 + fXc + (P.Q - 1 - P.v.H.D)) := by
    rw [k₅.gpr _ (by decide), v₄, v₃, k₃.gpr _ (by decide), v₂, hX (d := 304) (by omega) (by omega), hc.dl hT,
      k₂.sp, k₁.sp, hc.sp, fr_add, hlen, show 96 + (fXc + P.Q - 1) = 96 + fXc + (P.Q - 1) by simp only [fXc]; omega,
      sub_min _ (by omega)]
  have h4 : u₅.gpr .r4 = L.dg := by rw [v₅, m₄, m₃, m₂, hX (d := 280) (by omega) (by omega), hc.pDg]
  exact ⟨hc₅, hm₅ ▸ f₁, hm₅ ▸ b₁, h6, h5, h4⟩

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.v.H.D ≤ dn) {t : State}
    (hc : Ctx L g lr m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fXc)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.v.H.D) * 2 ^ P.R.sh) := by
  have hnB := hL.nB
  have hng := hL.ng
  obtain ⟨hw9, hQ66, hQD⟩ := P.sizesW hW
  have hs := P.sizes
  have hsh := P.R.sh7 hW
  have hlen : (cfgOf P).len = P.Q := rfl
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq (WP.mono (xcArgs_ok hL hT hW hc) fun u₅ ⟨hc₅, f₁, b₁, h6, h5, h4⟩ => ?_)
  have hdg : Spec.Sha256.bytesAt u₅.mem L.dg P.v.H.D = Spec.Sha256.bytesAt t.mem L.dg P.v.H.D :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.kg.symm.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by simp only [fXc]; omega)))
      (by omega)
  refine WP.seq (WP.mono (cp_ok hL hc₅ (p := L.B + BitVec.ofNat 64 (96 + fXc + (P.Q - 1 - P.v.H.D))) (q := L.dg)
      (n := P.v.H.D) (by omega) (by omega) h4 h5 h6
      (fun i hi => by rw [Offset.add_add]; exact hc₅.inFrW (n := 1) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
      (safe_high L (by simp only [fXc]; omega) (by simp only [fXc]; omega))
      (fun i hi => hc₅.inDg (o := i) (n := 1) (by omega) (by omega))
      ((hL.kg.symm.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by simp only [fXc]; omega)))
      (by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by simp only [fXc]; omega), Nat.mod_eq_of_lt (by simp only [fXc]; omega)]
          simp only [fXc]; omega))
    fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_)
  rw [hsc]
  refine WP.mono (conv_ok hL (c := cfgOf P) (o := fXc) (s := 8 - P.R.sh) (hlen.trans hQ66) hw9 hc₆ (by decide) (by decide)
    (by omega) (by omega)) fun u₇ ⟨hc₇, _, hf₇, hb₇⟩ => ?_
  refine ⟨hc₇, ?_, ?_⟩
  · have F₁ : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + fXc), 72⟩] t.mem u₅.mem :=
      f₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    have F₆ : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + fXc), 72⟩] u₅.mem u₆.mem := by
      exact hf₆.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ (by omega) (by simp only [fXc]; omega)⟩
    have F₇ : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + fXc), 72⟩] u₆.mem u₇.mem :=
      hf₇.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
    exact (F₁.trans F₆).trans F₇
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₅.mem (L.B + BitVec.ofNat 64 (96 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      have h1 := bytesAt_take u₅.mem (L.B + BitVec.ofNat 64 (96 + fXc)) (n := a + n) (k := 72) (by omega)
      rw [b₁, List.take_replicate, Nat.min_eq_left (by omega), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1.symm (by simp [Spec.Sha256.bytesAt])).2
    have hY : Spec.Sha256.bytesAt u₆.mem (L.B + BitVec.ofNat 64 (96 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.v.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.v.H.D ++ List.replicate 1 0) := by
      have e := Proof.Hmac.Common.bytesAt_add u₆.mem (L.B + BitVec.ofNat 64 (96 + fXc)) (P.Q - 1 - P.v.H.D)
        (P.v.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₆.mem
        (L.B + BitVec.ofNat 64 (96 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.v.H.D)) P.v.H.D 1
      rw [show P.Q - 1 - P.v.H.D + (P.v.H.D + 1) = P.Q by omega] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₆.mem (L.B + BitVec.ofNat 64 (96 + fXc)) (P.Q - 1 - P.v.H.D) =
          List.replicate (P.Q - 1 - P.v.H.D) 0 := by
        rw [bytesAt_frame hf₆ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega)]
        have := hz 0 (P.Q - 1 - P.v.H.D) (by omega)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₆.mem (L.B + BitVec.ofNat 64 (96 + fXc + (P.Q - 1 - P.v.H.D) + P.v.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₆ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega)) (by simp only [fXc]; omega) (by simp only [fXc]; omega))
          (by omega), show 96 + fXc + (P.Q - 1 - P.v.H.D) + P.v.H.D = 96 + fXc + (P.Q - 1 - P.v.H.D + P.v.H.D)
            by omega]
        exact hz (P.Q - 1 - P.v.H.D + P.v.H.D) 1 (by omega)
      rw [e, e', hb₆, hdg, p₁, p₃]
    have hQ : P.Q = 66 := hQ66
    rw [hQ] at hY ⊢
    rw [hb₇, hY, Rfc6979.ofBytes_zeros, Rfc6979.ofBytes_append_zeros, show 8 * 1 = 8 from rfl,
      shift_back _ _ (by omega)]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
