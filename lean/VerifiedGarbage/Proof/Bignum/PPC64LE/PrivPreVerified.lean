module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreCTA
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreCTA
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.PPC64LE.PrivPreCT`, which only this module used -/

section

/-! ### `Bignum.PPC64LE.PrivPreCTB`, which only this module used -/

section

/-!
# An RSA private key's precomputed values on PPC64LE: the registers at the cuts of the factors and the modulus

After the checks, the code is cut before `Precompute.core`, where the state
satisfies `vg_rsa_public_precompute`'s `Pre.C1` for data that the public data
fixes (`at_C1`), after it (`pins106`), and after each block that loads values
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
abbrev NC (c : Prog isa) : Prog isa :=
  NF (.seq Crt.loadX (.seq (.block PrivPre.pqLens) (.seq (Crt.checksWith PrivPre.checkPQs) c)))

/-- The front, the checks and `n`'s values with `R² mod n` into `X`'s array 6, then `c`. -/
abbrev NA (c : Prog isa) : Prog isa := NC (.seq (.block PrivPre.setupN) (.seq Precompute.core (.seq PrivPre.xIn c)))

/-- The registers at the cut after a factor's working space. -/
abbrev pVals (s₀ : State) (oA w : Nat) (o : Nat) : List (BitVec 64) :=
  [off (off (cS s₀) oA) (slot w 0), BitVec.ofNat 64 (2 * w), off (off (cS s₀) oA) (slot w 0), cS s₀,
    off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (w + 2)),
    off (s₀.gpr .r3) o]

theorem pins113 : Pins (At C0 privF 113) [.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r30] := by
  refine pins_at_list (fun s₀ => pVals s₀ (slot (cwX s₀) 8) (cwP s₀) (16 * cw s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NA (.seq (.block B1blk) (.block []))) rfl
      (partA_ok h.1 fun _ hA0 => partN_ok (pre_facts h.1) hA0 fun t hA => partB1_ok (pre_facts h.1) hA fun v V => wp_skip ?_)))
    fun _ s₀ s₀' h h' => ?_
  · simp only [pVals, List.map_cons, List.map_nil, V.r10, V.r11, V.r21, V.r29, V.r30,
      V.keep.gpr .r23 (by decide), V.keep.gpr .r27 (by decide), V.keep.gpr .r28 (by decide), hA.r23, hA.r27, hA.r28]
  · obtain ⟨eS, -, ek, ep, -, e3, -⟩ := data_vals h h'
    simp only [pVals, cwX, cw, cwP, eS, ek, ep, e3]

theorem pins152 : Pins (At C0 privF 152) [.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r30] := by
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

theorem at_C1 {d : PDat} {u : State} (h : At C0 privF 96 d u) : ∃ s₀, C0 d s₀ ∧ Pre.C1 (pdOf s₀) u :=
  at_wp (P := fun s₀ => Pre.C1 (pdOf s₀))
    (fun _ _ h => wp_seqL_nil (WP.of_flat (c := NC (.seq (.block PrivPre.setupN) (.block []))) rfl
      (partA_ok h.1 fun _ hA =>
        WP.seq (WP.mono (setupN_C1 (pre_facts h.1) hA) fun _ h1 => wp_skip h1)))) h

/-- The registers after `core`, for `xIn` and the factors' first block. -/
theorem pins106 : Pins (At C0 privF 106) [.r11, .r19, .r23, .r27, .r28] := by
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
      v5 v9 v11 (by rw [kAv.rd, kAv.wr]; exact hP.rN) hP.sN (sep16 hP)) fun t₁ ⟨_, kt⟩ => wp_skip ?_)
    have kvt := kv.trans kt
    simp only [List.map_cons, List.map_nil, kt.gpr .r11 (by decide), v11, kt.gpr .r19 (by decide), v19,
      kvt.gpr .r23 (by decide), kvt.gpr .r27 (by decide), kvt.gpr .r28 (by decide), hA.r23, hA.r27, hA.r28]
  · obtain ⟨eS, -, ek, -, -, e3, -⟩ := data_vals h h'
    simp only [cwX, cw, eS, ek, e3]

theorem pins191 : Pins (At C0 privF 191) [.r14, .r17, .r23] := by
  refine pins_at_list (fun s₀ => [off (s₀.gpr .r3) 0, BitVec.ofNat 64 (2 * cw s₀), cS s₀])
    (fun _ s₀ h => WP.of_flat (c := NB (.block [.load .d .r14 .r23 oOut, .load .d .r17 .r23 oNLen, .addi .r17 .r17 7,
        .lsr .d .r17 .r17 3, .lsl .r17 .r17 1])) (by kernel_rfl)
      (partA_ok h.1 fun _ hA0 => partN_ok (pre_facts h.1) hA0 fun _ hA => partB_ok (pre_facts h.1) hA fun t hB => ?_))
    fun _ s₀ s₀' h h' => ?_
  · have hP := pre_facts h.1
    refine WP.mono (maskBlk_ok hP hB.scr hB.r23 hB.hOut hB.hNL) fun u ⟨⟨e14, e17, _⟩, k⟩ => ?_
    simp only [List.map_cons, List.map_nil, e14, e17, k.gpr .r23 (by decide), hB.r23]
  · obtain ⟨eS, -, ek, -, -, e3, -⟩ := data_vals h h'
    simp only [cw, eS, ek, e3]

end VG.Proof.Bignum.PPC64LE.PrivPre

end

end

/-!
# An RSA private key's precomputed values on PPC64LE: constant time

The code's list of programs (`privF`) is cut after each block that loads
values of the header (`PrivPreCTA.lean`, `PrivPreCTB.lean`): there the
registers the taint analysis needs public have values that the public data
fixes. `Precompute.core`, whose branches are on `n`, is
`vg_rsa_public_precompute`'s (`Pre.core_rel`), from `Pre.C1` for data the
public data fixes.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint two_taintR At seg chain_cons chain_start
  at_zero_inv)

/-- The first block, the registers saved and the arguments stored, by the
taint analysis from the stack's first argument once loaded. -/
theorem front_rel : RelCT isa (Two C0) (.block (PrivPre.save ++ PrivPre.args)) fun _ _ => True := by
  unfold PrivPre.save
  simp only [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

theorem priv_run (d : PDat) (s : State) (h : C0 d s) : WP isa (Code.seqL privF) s fun _ => True :=
  let ⟨tr, t, e, _⟩ := fn_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem relCT_to_flat {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q) :
    RelCT isa P (Code.seqL c.flat) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_flat.mpr e₁) (exec_flat.mpr e₂)

/-- `Precompute.core`, as `vg_rsa_public_precompute`'s. -/
theorem core_seg : RelCT isa (Two (At C0 privF 96)) (seg privF 96 106) fun _ _ => True := by
  rw [show seg privF 96 106 = Code.seqL (Code.flat Precompute.core) from rfl]
  refine RelCT.mono (relCT_to_flat Pre.core_rel) (fun s₁ s₂ ⟨d, h₁, h₂, hsp⟩ => ?_) fun _ _ _ => trivial
  obtain ⟨s₀, c0, c1⟩ := at_C1 h₁
  obtain ⟨s₀', c0', c1'⟩ := at_C1 h₂
  exact ⟨pdOf s₀, c1, by rw [pdOf_eq c0 c0']; exact c1', hsp⟩

theorem fn_rel : RelCT isa (Two C0) PrivPre.code fun _ _ => True := by
  refine chain_start (chain_cons priv_run (m := 1) (by decide) ?_ ?_)
  · exact RelCT.mono (P := Two C0) (RelCT.seqL_single front_rel)
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons priv_run (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 9) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 17) (by decide) (two_taint _ pins9 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 25) (by decide) (two_taint _ pins17 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 33) (by decide) (two_taint _ pins25 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 41) (by decide) (two_taint _ pins33 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 50) (by decide) (two_taint _ pins41 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 51) (by decide) (two_taint _ pins50 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 96) (by decide) (two_taintR _ pins51 (by taint_decide_rel)) ?_
  refine chain_cons priv_run (m := 106) (by decide) core_seg ?_
  refine chain_cons priv_run (m := 113) (by decide) (two_taint _ pins106 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 152) (by decide) (two_taintR _ pins113 (by taint_decide_rel)) ?_
  refine chain_cons priv_run (m := 191) (by decide) (two_taintR _ pins152 (by taint_decide_rel)) ?_
  exact two_taint _ pins191 (by taint_decide)

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub PrivPre.code :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, ⟨hr, hsp, ha, hn⟩⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`pp_implies`); with correctness (`fn_correct`) and constant time (`fn_ct`),
the code is verified (`pp_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE

/-- A state meeting `fnContract.pre`: a 512-bit modulus, one-byte factors,
`pre` at `0x1000`, and the stack arguments at `sp + 96 = 0x6060`: the working
space at `0x8000`, of 1056 words. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 20 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x3100
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6061 then 0x80 else if a = 0x6068 then 0x20 else if a = 0x6069 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6060, 16⟩]
  wr := [⟨0x1000, 160⟩, ⟨0x8000, 8448⟩]

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pp_implies : fnContract.Implies (Spec.Rsa.privatePrecomputeContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs,
      fnContract, stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, fnContract,
      stackArgs_two, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_two, stackArgs_two, a0, a1],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs,
      fnContract, stackArgs_two, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState

/-- `vg_rsa_private_precompute`. -/
theorem pp_verified : Verified target VG.Impl.Bignum.PPC64LE.PrivPre.code (Spec.Rsa.privatePrecomputeContract abi) :=
  Verified.of_correct fn_correct fn_ct pp_implies

end VG.Proof.Bignum.PPC64LE.PrivPre
