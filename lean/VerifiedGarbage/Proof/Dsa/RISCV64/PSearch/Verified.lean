module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Top
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Finish
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Hash
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Sat
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

-- separate module: the contract from the body (`search_verified`), which builds beside the seed's attempt (`Attempt`), both of which the widths' instances import

/-! # DSA parameter search on RISC-V meets its contract -/

@[expose] public section

/-! ## DSA parameter search on RISC-V: the body

`body_vp`: from the call's entry, the header written (`entry_vp`), the
search and the exit of the width `state[1]` selects (`dispatch_vp`, each
width given by a `GeoOk`), and our caller's registers restored
(`restore_vp`): `Ret`.
-/

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.Dsa.Generation (stAt)

/-- A width's proofs, for every call with its `p_len` (and so its `q_len`). -/
structure GeoOk (g : Geo) (pL qL : Nat) where
  HO : HashOk g.G
  hgp : g.pLen = pL
  hgq : g.qLen = qL
  hq : qL < 2048
  hlb : HO.md.lenBytes qL =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * qL / 256), BitVec.ofNat 8 (8 * qL % 256)]
  att : ∀ G : GP, (∃ σ, CIn STK0 σ ∧ mkG σ = G) → G.pLen = pL → G.qLen = qL →
    AttemptOk G (padCl G HO.md) (fun _ => True) g.attempt

section
variable {G : GP}

/-- The controller's last iteration is not a rejected seed's. -/
theorem lastPos_stAt : stAt G.pLen G.randB (lastPos G) ≠ 2 := by
  have hp := Generation.iters_pos G.pLen G.randB G.left 0
  have h := Generation.iters_at (pLen := G.pLen) (R := G.randB) (left := G.left) (nIt G - 1) (by unfold nIt; omega)
  have e : nIt G - (nIt G - 1) = 1 := by unfold nIt; omega
  rw [e] at h
  exact Generation.stAt_last h

/-- A width's search and exit. -/
theorem gen_vp {g : Geo} {pL qL : Nat} (K : GeoOk g pL qL) (hex : ∃ σ, CIn STK0 σ ∧ mkG σ = G)
    (hp : G.pLen = pL) (hq : G.qLen = qL) :
    VP (fun σ s => GI G STK0 σ (eV G) entryLS s ∧ (fun _ => True) σ) g.generate (Fin G) := by
  obtain ⟨σ₀, pre₀, hG₀⟩ := hex
  have hl : G.left ≤ 4096 := by rw [← hG₀]; exact pre₀.left
  have hRL : G.randB.length = G.randLen := by rw [← hG₀]; simp [mkG, Spec.Rsa.bytesAt]
  have hR64 : G.randLen < 2 ^ 64 := by rw [← hG₀]; exact (σ₀.gpr .a4).isLt
  have hq2 : G.qLen < 2048 := by rw [hq]; exact K.hq
  exact VP.seq (search_vp g K.HO.md rfl (by rw [hq]; exact K.hlb) (K.hgq.trans hq.symm) hq2
    (K.att G ⟨σ₀, pre₀, hG₀⟩ hp hq) hl hRL hR64) (finish_vp g (K.hgp.trans hp.symm) (K.hgq.trans hq.symm) lastPos_stAt)

/-- Returned: our caller's registers back, and the contract's results. -/
structure Ret (G : GP) (σ t : State) : Prop where
  pre : CIn STK0 σ
  hG : mkG σ = G
  abi : abiPreserved σ t
  status : ((t.gpr .a0).setWidth 32).toNat = (resG G).status
  out : Spec.Rsa.bytesAt t.mem G.out G.outLen = outB G
  used : Spec.Rsa.wordsAt t.mem G.used 1 = [BitVec.ofNat 64 (resG G).used]
  state : Spec.Rsa.wordsAt t.mem G.state 4 = [BitVec.ofNat 64 (resG G).remaining, BitVec.ofNat 64 G.pLen,
    BitVec.ofNat 64 (Spec.Dsa.parameterEntropy G.pLen), BitVec.ofNat 64 (resG G).requested]

theorem restore_vp : VP (Fin G) (.block restore) (Ret G) := by
  refine VP.pub (G := G) (fun σ s h => ⟨h.s6, by rw [h.sp, ← h.hG]; rfl⟩) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block restore), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s h => ?_
  have hal : G.scr.toNat % 8 = 0 := by have := h.pre.alC; rw [← h.hG]; exact this
  have hfit : G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 := by have := h.pre.nC; rw [← h.hG]; exact this
  have big : 8 * (64 * G.pLen + 1024) ≤ G.scrLen * 8 := by
    have := h.pre.scrLen
    rw [h.hG] at this
    simp only [Spec.Dsa.generationScratchWords] at this
    omega
  have hE : hEnd ≤ G.scrLen * 8 := by simp only [hEnd, fSave]; omega
  refine WP.mono (restore_ok' h.s6 hal (by omega) h.saved h.ra h.sp fun o ho => ?_)
    fun t ⟨abi, m, a0⟩ => ⟨h.pre, h.hG, abi, by rw [a0]; exact h.status, by rw [m]; exact h.out,
      by rw [m]; exact h.used, by rw [m]; exact h.state⟩
  refine ⟨G.rScr, List.mem_append_right _ ?_, Offset.contains_base _ (by omega) (by omega)⟩
  rw [h.wr, h.pre.wr, h.hG]; simp

/-- The width `state[1]` selects. -/
theorem body_vp {g1 g2 g3 : Geo} (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    VP (AE G) (code g1 g2 g3) (Ret G) := by
  refine VP.intro (P := ∃ σ, CIn STK0 σ ∧ mkG σ = G) (fun hex => ?_) |>.mono
    (fun σ s h => ⟨⟨σ, h.2.1, h.2.2⟩, h⟩) fun _ _ h => h
  have hl : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32) := by
    obtain ⟨σ₀, pre₀, hG₀⟩ := hex
    have hq : G.qLen = Spec.Dsa.generationQLen G.pLen := rfl
    have := pre₀.lens
    rw [hG₀] at this
    simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
    rw [hq, Spec.Dsa.generationQLen]
    rcases (by omega : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) with e | e | e <;> simp [e]
  unfold code
  refine entry_vp.seq ((dispatch_vp (X := fun _ => True) g1 g2 g3 (fun e => ?_) (fun e => ?_) (fun e => ?_)).seq
    restore_vp)
  · exact gen_vp K1 hex e (by omega)
  · exact gen_vp K2 hex e (by omega)
  · exact gen_vp K3 hex e (by omega)

end

end VG.Proof.Dsa.RISCV64.PSearch

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The contract, with the table, for the 512 bytes of stack the tests use. -/
abbrev searchK : Contract isa := Spec.Dsa.parameterSearchContract (abi.withConsts kT) 512

theorem map_toNat_inj {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

theorem map_toNat_inj64 {a b : List (BitVec 64)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two calls with the same public data have the same public parameters. -/
theorem mkG_eq {s₁ s₂ : State} (h : searchK.pub s₁ s₂) : mkG s₁ = mkG s₂ := by
  obtain ⟨h, hy⟩ := (pub_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mp h
  have ht := hy _ List.mem_cons_self
  sig_pub [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, List.append_eq] at h
  obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7⟩ := h
  have l1 : ((Spec.Rsa.wordsAt s₁.mem (s₁.gpr .a7) 4).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt s₂.mem (s₂.gpr .a7) 4).map (·.toNat)).length := by simp [Spec.Rsa.wordsAt]
  obtain ⟨hw, hb⟩ := List.append_inj hl l1
  have ew := map_toNat_inj64 hw
  have eb := map_toNat_inj hb
  simp only [Spec.Rsa.wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq,
    Nat.mul_zero, BitVec.add_zero, Nat.mul_one] at ew
  obtain ⟨w0, w1, -⟩ := ew
  have e8 : (BitVec.ofNat 64 8 : BitVec 64) = 8 := rfl
  rw [e8] at w1
  simp only [mkG]
  rw [w0, w1, eb, hsp, r0, r1, r2, r3, r4, r5, r6, r7, ht]

section
variable {g1 g2 g3 : Geo}

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : searchK.pre s) : WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ searchK.post s t := by
  have hpre := cin_of_pre (n := 511) s hs
  refine WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩ rfl) fun u hu => ⟨hu.abi, ?_⟩
  refine (post_consts (c₀ := (Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed))
    (cs := [])).mpr ?_
  sig_post [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, List.append_eq]
  exact ⟨hu.status, hu.out, hu.used, hu.state⟩

/-- The code leaks only what its contract makes public. -/
theorem code_ct (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    ConstantTime isa searchK.pre searchK.pub (code g1 g2 g3) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  have p₁ := cin_of_pre (n := 511) s₁ h₁
  have p₂ := cin_of_pre (n := 511) s₂ h₂
  have hG := mkG_eq hp
  exact ((body_vp (G := mkG s₁) K1 K2 K3).ct _ _ _ _ _ _ ⟨s₁, s₂, ⟨⟨rfl, p₁, rfl⟩, rfl⟩, ⟨⟨rfl, p₂, hG.symm⟩, rfl⟩⟩ e₁ e₂).1

/-- `vg_dsa_parameter_search` over the three widths meets its contract. -/
theorem search_verified (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    Verified target (code g1 g2 g3) searchK :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok K1 K2 K3 hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct K1 K2 K3,
    ⟨satState, sat⟩⟩

end

end VG.Proof.Dsa.RISCV64.PSearch
