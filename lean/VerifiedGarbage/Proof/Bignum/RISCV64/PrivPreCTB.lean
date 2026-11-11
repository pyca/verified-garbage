module
-- separate module: the precomputation's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreCTA
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPinsA
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: the registers at the cuts of the factors and the modulus

After the checks, the code is cut before `Precompute.core`, where the state
satisfies `vg_rsa_public_precompute`'s `Pre.C1` for data that the public data
fixes (`at_C1`), after it (`pins112`), and after each block that loads
values of the header (`pins*`): the factors' working spaces (`partBv_ok`,
`partBy_ok`), the blocks of `prime` that load `pre`'s cursor and the mask
(`primeHead_ok`), and `maskN`'s first block.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr At pins_at_list)
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Crt (wordsOf wp_nil wp_seqL_nil)

/-- The front and the checks, then `c`. -/
abbrev NC (c : Prog isa) : Prog isa := NF (.seq Crt.loadX (.seq Crt.checks c))

/-- The front, the checks, `n`'s values and `R² mod n` into `X`'s array 6, then `c`. -/
abbrev NA (c : Prog isa) : Prog isa :=
  NC (.seq (.block PrivPre.setupN) (.seq Precompute.core (.seq PrivPre.xIn c)))

/-- The registers `xIn` starts from. -/
abbrev rsN : List Reg := [.t0, .s5, .s6, .s11]

theorem pins112 : Pins (At C0 privF 112) rsN := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (cw s₀), s₀.gpr .a0, cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NC (.seq (.block PrivPre.setupN) (.seq Precompute.core (.block []))))
      (by decide +kernel)
      (partA_ok h.1 fun t hA => ?_)))
    fun _ s₀ s₀' h h' => ?_
  · have hP := pre_facts h.1
    have room := hP.room
    have k64 := hP.k64; have k1024 := hP.k1024
    have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX8 := e (cwX s₀) 8; have eN8 := e (cw s₀) 8
    have hcw : cwX s₀ = 2 * cw s₀ := rfl
    refine WP.seq (WP.mono (setupN_ok hP hA) fun v ⟨⟨v5, v7, v8, v0, va7, va2, va5, va6, vm⟩, kv⟩ => ?_)
    have kAv := hA.keep.trans kv
    refine WP.seq (WP.mono (Pre.core_ok (hA.scr.congr kv.2.2) (pre16 hP kAv.2.2) dw k64 k1024 (by omega_arith)
      v5 v8 v7 va7 va2 va5 va6 v0 (by rw [kAv.2.1, kAv.2.2]; exact hP.rN) hP.sN (sep16 hP)) fun t₁ ⟨_, kt⟩ => ?_)
    have kvt := kv.trans kt
    exact wp_nil (by
      simp only [rsN, List.map_cons, List.map_nil, kt.gpr (r := .t0) (by decide), kt.gpr (r := .s5) (by decide),
        kvt.gpr (r := .s6) (by decide), kvt.gpr (r := .s11) (by decide), v0, v5, hA.s6, hA.s11])
  · obtain ⟨eS, -, ek, -, -, e0, -⟩ := data_vals h h'
    simp only [cwX, cw, eS, ek, e0]

/-- To `q`'s working space, then `c`. -/
abbrev NQ (c : Prog isa) : Prog isa :=
  NA (.seq (.block (curBlock ++ setupP oBP oPLen)) (.seq (PrivPre.prime 4) (.seq (.block (setupP oBQ oQLen)) c)))

/-- From the checks to the end of the factors, then `c`. -/
abbrev NB (c : Prog isa) : Prog isa := NQ (.seq (PrivPre.prime 5) c)

/-- The registers a factor's `prime` starts from. -/
abbrev rsP : List Reg := [.a7, .s5, .t0, .s6, .s11, .ra]

abbrev valsP (s₀ : State) (oA w : Nat) : List (BitVec 64) :=
  [Mont.off (Mont.off (cS s₀) oA) (slot w 0), BitVec.ofNat 64 (8 * (w + 2)), BitVec.ofNat 64 w, cS s₀,
    BitVec.ofNat 64 (8 * (cwX s₀ + 2)), Mont.off (Mont.off (cS s₀) oA) (slot w 0)]

theorem pargs_vals {s BX P Z L oA wA wX xj Pv o k b} (H : PArgs s BX P Z L oA wA wX xj Pv o k b) :
    rsP.map s.gpr = [Mont.off (Mont.off BX oA) (slot wA 0), BitVec.ofNat 64 (8 * (wA + 2)), BitVec.ofNat 64 wA, BX,
      BitVec.ofNat 64 (8 * (wX + 2)), Mont.off (Mont.off BX oA) (slot wA 0)] := by
  simp only [rsP, List.map_cons, List.map_nil, H.h7, H.h5, H.ht0, H.h6, H.h11, H.hra]

theorem pins119 : Pins (At C0 privF 119) rsP := by
  refine pins_at_list (fun s₀ => valsP s₀ (slot (cwX s₀) 8) (cwP s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NA (.seq (.block (curBlock ++ setupP oBP oPLen)) (.block [])))
      (by decide +kernel)
      (partA_ok h.1 fun _ hA => partN_ok (pre_facts h.1) hA fun t hN => partBv_ok (pre_facts h.1) hN fun v V => wp_nil (pargs_vals V.pa))))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, -, ek, ep, -⟩ := data_vals h h'
  simp only [valsP, cwX, cw, cwP, eS, ek, ep]

theorem pins158 : Pins (At C0 privF 158) rsP := by
  refine pins_at_list (fun s₀ => valsP s₀ (oAQ s₀) (cwQ s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NQ (.block [])) (by decide +kernel)
      (partA_ok h.1 fun _ hA => partN_ok (pre_facts h.1) hA fun t hN => partBy_ok (pre_facts h.1) hN fun y Y => wp_nil (pargs_vals Y.pa))))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, -, ek, ep, eq, -⟩ := data_vals h h'
  simp only [valsP, oAQ, cwX, cw, cwQ, eS, ek, ep, eq]

/-- The registers after `prime`'s header block. -/
abbrev rsM : List Reg := [.t3, .t4, .t5, .s6, .s11]

theorem phead_vals {s BX P Z L oA wA wX xj Pv o k b} (H : PArgs s BX P Z L oA wA wX xj Pv o k b) {u v : State}
    (V : PHead s BX P oA wA o Pv b u v) :
    rsM.map v.gpr = [Mont.off P o, Mont.off (Mont.off BX oA) (slot wA 1), BitVec.ofNat 64 wA, BX,
      BitVec.ofNat 64 (8 * (wX + 2))] := by
  simp only [rsM, List.map_cons, List.map_nil, V.t3, V.t4, V.t5, V.keep.gpr (r := .s6) (by decide),
    V.keep.gpr (r := .s11) (by decide), H.h6, H.h11]

theorem pins155 : Pins (At C0 privF 155) rsM := by
  refine pins_at_list (fun s₀ => [Mont.off (s₀.gpr .a0) (16 * cw s₀),
      Mont.off (Mont.off (cS s₀) (slot (cwX s₀) 8)) (slot (cwP s₀) 1), BitVec.ofNat 64 (cwP s₀), cS s₀,
      BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NA (.seq (.block (curBlock ++ setupP oBP oPLen))
      (Win.powerPF 4 (.seq (.block primeHB) (.block []))))) (by decide +kernel)
      (partA_ok h.1 fun _ hA => partN_ok (pre_facts h.1) hA fun t hN => partBv_ok (pre_facts h.1) hN fun v V =>
        primeHead_ok V.pa fun u x X => wp_nil (phead_vals V.pa X))))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, -, ek, ep, -, e0, -⟩ := data_vals h h'
  simp only [cwX, cw, cwP, eS, ek, ep, e0]

theorem pins194 : Pins (At C0 privF 194) rsM := by
  refine pins_at_list (fun s₀ => [Mont.off (s₀.gpr .a0) (16 * cw s₀ + 8 * cwP s₀),
      Mont.off (Mont.off (cS s₀) (oAQ s₀)) (slot (cwQ s₀) 1), BitVec.ofNat 64 (cwQ s₀), cS s₀,
      BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NQ (Win.powerPF 5 (.seq (.block primeHB) (.block []))))
      (by decide +kernel)
      (partA_ok h.1 fun _ hA => partN_ok (pre_facts h.1) hA fun t hN => partBy_ok (pre_facts h.1) hN fun y Y =>
        primeHead_ok Y.pa fun u x X => wp_nil (phead_vals Y.pa X))))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, -, ek, ep, eq, e0, -⟩ := data_vals h h'
  simp only [oAQ, cwX, cw, cwP, cwQ, eS, ek, ep, eq, e0]

/-- `vg_rsa_public_precompute`'s data: `pre`, `n`, the working space, `k`,
its size and `n`'s bytes. -/
def pdOf (s₀ : State) : Pre.PD := ⟨s₀.gpr .a0, s₀.gpr .a2, cS s₀, ck s₀, cZ s₀, nB s₀⟩

theorem pdOf_eq {d : PDat} {s₀ s₀' : State} (h : C0 d s₀) (h' : C0 d s₀') : pdOf s₀ = pdOf s₀' := by
  obtain ⟨eS, eZ, ek, -, -, e0, e2, -, -, en⟩ := data_vals h h'
  simp only [pdOf, eS, eZ, ek, e0, e2, en]

/-- After the checks and `setupN`: `Pre.C1`. -/
theorem setupN_C1 {s₀ u : State} (hP : PF s₀) (hB : A s₀ u) :
    WP isa (.block PrivPre.setupN) u (Pre.C1 (pdOf s₀)) := by
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8; have eN8 := e (cw s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  refine WP.mono (setupN_ok hP hB) fun v ⟨⟨v5, v7, v8, v0, va7, va2, va5, va6, vm⟩, kv⟩ => ?_
  have kBv := hB.keep.trans kv
  have bN : Spec.Rsa.bytesAt v.mem (s₀.gpr .a2) (ck s₀) = nB s₀ := by
    rw [vm]
    exact bytes_frame hB.frame hP.dN (Nat.le_of_lt (BitVec.isLt _))
  have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
  refine ⟨⟨hB.scr.congr kv.2.2, pre16 hP kBv.2.2, k64, k1024, (show slot (cw s₀) 8 ≤ cZ s₀ by omega_arith),
    sep16 hP, hlen, v5, va7, va2, va5, va6, v0, (kv.gpr (by decide)).trans hB.s6, v8, v7⟩,
    by rw [kBv.2.1, kBv.2.2]; exact hP.rN, hP.sN, fun i hi => ?_⟩
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

theorem at_C1 {d : PDat} {u : State} (h : At C0 privF 102 d u) : ∃ s₀, C0 d s₀ ∧ Pre.C1 (pdOf s₀) u :=
  at_wp (P := fun s₀ => Pre.C1 (pdOf s₀))
    (fun _ _ h => wp_seqL_nil (WP.of_flat (c := NC (.seq (.block PrivPre.setupN) (.block []))) (by decide +kernel)
      (partA_ok h.1 fun _ hA => WP.seq (WP.mono (setupN_C1 (pre_facts h.1) hA) fun _ h1 => wp_nil h1)))) h

theorem pins197 : Pins (At C0 privF 197) [.t3, .t5, .s6] := by
  refine pins_at_list (fun s₀ => [s₀.gpr .a0, BitVec.ofNat 64 (2 * cw s₀), cS s₀])
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NB (.seq (.block maskBlk) (.block []))) (by decide +kernel)
      (partA_ok h.1 fun _ hA => partN_ok (pre_facts h.1) hA fun _ hN => partB_ok (pre_facts h.1) hN fun _ hB =>
        WP.seq (WP.mono (maskBlk_ok (pre_facts h.1) hB) fun x ⟨⟨e3, e5, _, _⟩, k⟩ => wp_nil (by
          simp only [List.map_cons, List.map_nil, e3, e5, k.gpr (r := .s6) (by decide), hB.s6])))))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, -, ek, -, -, e0, -⟩ := data_vals h h'
  simp only [cw, eS, ek, e0]

end VG.Proof.Bignum.RISCV64.PrivPre
