module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreCTA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: the registers at the cuts of the factors and the modulus

After the checks, the code is cut before `Precompute.core`, where the state
satisfies `vg_rsa_public_precompute`'s `Pre.C1` for data that the public data
fixes (`at_C1`), after it (`pins105`), and after each block that loads values
of the header (`pins*`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Pins At pins_at_list)

/-- The factors' first block. -/
abbrev B1blk : List Instr :=
  ([.load .d .r30 .r23 oOut, .load .d .r3 .r23 oNLen, .addi .r3 .r3 7, .lsr .d .r3 .r3 3,
    .lsl .r3 .r3 4, .add .r30 .r30 .r3] : List Instr) ++ setupP oBP oPLen

/-- The front and the checks, then `c`. -/
abbrev NC (c : Prog isa) : Prog isa := NF (.seq Crt.loadX (.seq Crt.checks c))

/-- The front, the checks and `n`'s values with `R² mod n` into `X`'s array 6, then `c`. -/
abbrev NA (c : Prog isa) : Prog isa := NC (.seq (.block PrivPre.setupN) (.seq Precompute.core (.seq PrivPre.xIn c)))

/-- The registers at the cut after a factor's working space. -/
abbrev pVals (s₀ : State) (oA w : Nat) (o : Nat) : List (BitVec 64) :=
  [off (off (cS s₀) oA) (slot w 0), BitVec.ofNat 64 (2 * w), off (off (cS s₀) oA) (slot w 0), cS s₀,
    off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (w + 2)),
    off (s₀.gpr .r3) o]

theorem pins112 : Pins (At C0 privF 112) [.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r30] := by
  refine pins_at_list (fun s₀ => pVals s₀ (slot (cwX s₀) 8) (cwP s₀) (16 * cw s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NA (.seq (.block B1blk) (.block []))) rfl
      (partA_ok h.1 fun _ hA0 => partN_ok (pre_facts h.1) hA0 fun t hA => partB1_ok (pre_facts h.1) hA fun v V => wp_skip ?_)))
    fun _ s₀ s₀' h h' => ?_
  · simp only [pVals, List.map_cons, List.map_nil, V.r10, V.r11, V.r21, V.r29, V.r30,
      V.keep.gpr .r23 (by decide), V.keep.gpr .r27 (by decide), V.keep.gpr .r28 (by decide), hA.r23, hA.r27, hA.r28]
  · obtain ⟨eS, -, ek, ep, -, e3, -⟩ := data_vals h h'
    simp only [pVals, cwX, cw, cwP, eS, ek, ep, e3]

theorem pins151 : Pins (At C0 privF 151) [.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r30] := by
  refine pins_at_list (fun s₀ => pVals s₀ (slot (cwX s₀) 8 + slot (cwP s₀) 24) (cwQ s₀)
      (16 * cw s₀ + 8 * cwP s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NA (.seq (.block B1blk) (.seq (PrivPre.prime 4)
      (.seq (.block (setupP oBQ oQLen)) (.block []))))) rfl
      (partA_ok h.1 fun _ hA0 => partN_ok (pre_facts h.1) hA0 fun t hA => partB1_ok (pre_facts h.1) hA fun v V => partB2_ok (pre_facts h.1) hA V
        fun x y X => wp_skip ?_)))
    fun _ s₀ s₀' h h' => ?_
  · have k := X.xk.trans X.yk
    simp only [pVals, List.map_cons, List.map_nil, X.y10, X.y11, X.y21, X.y29, X.yk.gpr .r30 (by decide), X.x30,
      k.gpr .r23 (by decide), k.gpr .r27 (by decide), k.gpr .r28 (by decide), hA.r23, hA.r27, hA.r28]
  · obtain ⟨eS, -, ek, ep, eq, e3, -⟩ := data_vals h h'
    simp only [pVals, cwX, cw, cwP, cwQ, eS, ek, ep, eq, e3]

/-- From the checks to the end of the factors, then `c`. -/
abbrev NB (c : Prog isa) : Prog isa :=
  NA (.seq (.block B1blk) (.seq (PrivPre.prime 4) (.seq (.block (setupP oBQ oQLen)) (.seq (PrivPre.prime 5) c))))

/-- `vg_rsa_public_precompute`'s data: `pre`, `n`, the working space, `k`,
its size and `n`'s bytes. -/
def pdOf (s₀ : State) : Pre.PD := ⟨s₀.gpr .r3, s₀.gpr .r5, cS s₀, ck s₀, cZ s₀, nB s₀⟩

theorem pdOf_eq {d : PDat} {s₀ s₀' : State} (h : C0 d s₀) (h' : C0 d s₀') : pdOf s₀ = pdOf s₀' := by
  obtain ⟨eS, eZ, ek, -, -, e3, e5, -, -, en⟩ := data_vals h h'
  simp only [pdOf, eS, eZ, ek, e3, e5, en]

local macro "oa" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only
  [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith))

/-- After the checks and `setupN`: `Pre.C1`. -/
theorem setupN_C1 {s₀ u : State} (hP : PF s₀) (hA : A s₀ u) :
    WP isa (.block PrivPre.setupN) u (Pre.C1 (pdOf s₀)) := by
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  refine WP.mono (setupN_ok hP hA) fun v ⟨⟨v19, v12, v6, v21, v11, v10, v5, v8, v9, vm⟩, kv⟩ => ?_
  have kAv := hA.keep.trans kv
  have bN : Spec.Rsa.bytesAt v.mem (s₀.gpr .r5) (ck s₀) = nB s₀ := by
    rw [vm]
    exact bytes_frame hA.frame hP.dN (Nat.le_of_lt (BitVec.isLt _))
  have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
  refine ⟨⟨hA.scr.congr kv.wr, pre16 hP kAv.wr, k64, k1024, (show slot (cw s₀) 8 ≤ cZ s₀ by oa), sep16 hP, hlen, v19, v10,
    v5, v8, v9, v11, v21, v6, v12⟩, by rw [kAv.rd, kAv.wr]; exact hP.rN, hP.sN, fun i hi => ?_⟩
  simp only [pdOf] at hi ⊢
  rw [← List.getElem_of_eq bN (by rw [Spec.Rsa.bytesAt, List.length_map, List.length_range]; omega_arith)]
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

/-- A fact of the state at a cut, from the initial state. -/
theorem at_wp {α : Type} {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {P : State → State → Prop}
    (hv : ∀ a s₀, Φ a s₀ → WP isa (Code.seqL (F.take n)) s₀ (P s₀)) {a : α} {u : State}
    (h : At Φ F n a u) : ∃ s₀, Φ a s₀ ∧ P s₀ u := by
  obtain ⟨s₀, t, h₀, e⟩ := h
  obtain ⟨_, _, x, y⟩ := hv a s₀ h₀
  obtain ⟨-, rfl⟩ := Exec.det e x
  exact ⟨s₀, h₀, y⟩

theorem at_C1 {d : PDat} {u : State} (h : At C0 privF 95 d u) : ∃ s₀, C0 d s₀ ∧ Pre.C1 (pdOf s₀) u :=
  at_wp (P := fun s₀ => Pre.C1 (pdOf s₀))
    (fun _ _ h => wp_seqL_nil (WP.of_flat (c := NC (.seq (.block PrivPre.setupN) (.block []))) rfl
      (partA_ok h.1 fun _ hA =>
        WP.seq (WP.mono (setupN_C1 (pre_facts h.1) hA) fun _ h1 => wp_skip h1)))) h

/-- The registers after `core`, for `xIn` and the factors' first block. -/
theorem pins105 : Pins (At C0 privF 105) [.r11, .r19, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cw s₀), s₀.gpr .r3, cS s₀, off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NC (.seq (.block PrivPre.setupN) (.seq Precompute.core
      (.block [])))) rfl
      (partA_ok h.1 fun _ hA => ?_)))
    fun _ s₀ s₀' h h' => ?_
  · have hP := pre_facts h.1
    have room := hP.room
    have k64 := hP.k64; have k1024 := hP.k1024
    have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
    refine WP.seq (WP.mono (setupN_ok hP hA) fun v ⟨⟨v19, v12, v6, v21, v11, v10, v5, v8, v9, vm⟩, kv⟩ => ?_)
    have kAv := hA.keep.trans kv
    refine WP.seq (WP.mono (Pre.core_ok (hA.scr.congr kv.wr) (pre16 hP kAv.wr) dw k64 k1024 (by oa) v19 v6 v12 v10
      v5 v8 v9 v11 (by rw [kAv.rd, kAv.wr]; exact hP.rN) hP.sN (sep16 hP)) fun t₁ ⟨_, kt⟩ => wp_skip ?_)
    have kvt := kv.trans kt
    simp only [List.map_cons, List.map_nil, kt.gpr .r11 (by decide), v11, kt.gpr .r19 (by decide), v19,
      kvt.gpr .r23 (by decide), kvt.gpr .r27 (by decide), kvt.gpr .r28 (by decide), hA.r23, hA.r27, hA.r28]
  · obtain ⟨eS, -, ek, -, -, e3, -⟩ := data_vals h h'
    simp only [cwX, cw, eS, ek, e3]

theorem pins190 : Pins (At C0 privF 190) [.r14, .r17, .r23] := by
  refine pins_at_list (fun s₀ => [off (s₀.gpr .r3) 0, BitVec.ofNat 64 (2 * cw s₀), cS s₀])
    (fun _ s₀ h => WP.of_flat (c := NB (.block [.load .d .r14 .r23 oOut, .load .d .r17 .r23 oNLen, .addi .r17 .r17 7,
        .lsr .d .r17 .r17 3, .lsl .r17 .r17 1])) (by decide +kernel)
      (partA_ok h.1 fun _ hA0 => partN_ok (pre_facts h.1) hA0 fun _ hA => partB_ok (pre_facts h.1) hA fun t hB => ?_))
    fun _ s₀ s₀' h h' => ?_
  · have hP := pre_facts h.1
    refine WP.mono (maskBlk_ok hP hB.scr hB.r23 hB.hOut hB.hNL) fun u ⟨⟨e14, e17, _⟩, k⟩ => ?_
    simp only [List.map_cons, List.map_nil, e14, e17, k.gpr .r23 (by decide), hB.r23]
  · obtain ⟨eS, -, ek, -, -, e3, -⟩ := data_vals h h'
    simp only [cw, eS, ek, e3]

end VG.Proof.Bignum.PPC64LE.PrivPre
