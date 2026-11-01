module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Contracts
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Loop
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream

/-!
# ML-DSA on PPC64LE: `vg_mldsa_bit_pack`

The value of a coefficient `x` is `b - x`, plus `q` if that is negative (`bm`,
as `bMinus` computes it, with `b` in `r4` and `q` in `r7`), which is
`b - (x mod± q)` for a reduced `x` (`Pack/Arith.lean`). The loop is proven
once for every width (`packLoop_ok`), and the function by its five cases.
Constant time: the branch on the width by `sel_ct`, and each loop by the
taint analysis.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE (toNat_setWidth64)
open VG.Proof.MlDsa.Pack

/-! ## `b - x` modulo `q` -/

/-- `b - x`, plus `q` if it is negative, as `bMinus` computes it in 64 bits. -/
def bm (b x : BitVec 64) : BitVec 64 := b - x + ((b - x) >>> 63) * BitVec.ofNat 64 q

theorem bm_toNat {b x : BitVec 64} (hb : b.toNat ≤ 2 ^ 19) (hx : x.toNat < q) :
    (bm b x).toNat = (b.toNat + q - x.toNat) % q := by
  rw [q_eq] at hx ⊢
  unfold bm
  rw [q_eq]
  by_cases h : x.toNat ≤ b.toNat
  · have e : (b - x) >>> 63 = 0#64 := by bv_omega
    rw [e, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    bv_omega
  · have e : (b - x) >>> 63 = 1#64 := by bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega)]
    bv_omega

/-- `b = B` in `r4` and `q` in `r7`. -/
def RB (B : Nat) (s : State) : Prop := s.gpr .r4 = BitVec.ofNat 64 B ∧ s.gpr .r7 = BitVec.ofNat 64 q

theorem RB_stable (B : Nat) : Stable (RB B) := fun _ _ h k =>
  ⟨by rw [k.gpr (by decide), h.1], by rw [k.gpr (by decide), h.2]⟩

/-- `r9 ← b - r9` modulo `q`, from a state of `RB B`. -/
theorem bMinus_ok {B : Nat} {s : State} (hR : RB B s) :
    WP isa (.block bMinus) s fun s' =>
      (s'.gpr .r9 = bm (BitVec.ofNat 64 B) (s.gpr .r9) ∧ s'.mem = s.mem) ∧ Keep [.r0, .r9] s s' := by
  refine WP.keep _ ?_ rfl
  unfold bMinus addQNeg
  refine wp_sub fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => wp_mul fun s₄ u₄ => wp_add fun s₅ u₅ =>
    wp_nil ⟨?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]⟩
  rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other .r9 (by decide), u₃.other .r7 (by decide),
    u₂.gpr, u₂.other .r7 (by decide), hR.1, hR.2]
  rfl

/-- The value `bpLd` loads of a word. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (bm (BitVec.ofNat 64 B) (w.setWidth 64)).toNat

theorem bpLd_ok (B : Nat) : LdOk bpLd (bpVal B) (RB B) := fun j s hR hj hin => by
  unfold bpLd
  refine wp_lwz (by decide) hj rfl hin fun s₁ u₁ => ?_
  have hR₁ : RB B s₁ := ⟨by rw [u₁.other _ (by decide), hR.1], by rw [u₁.other _ (by decide), hR.2]⟩
  refine WP.mono (bMinus_ok hR₁) fun s₂ ⟨⟨g₂, m₂⟩, k₂⟩ => ⟨⟨by rw [g₂, u₁.gpr], by rw [m₂, u₁.mem]⟩,
    ((upd_keep u₁).trans k₂).mono (by decide)⟩

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ 2 ^ 19)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      vals (bpVal b) m f := by
  have hbq : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [bpVal, bm_toNat (by omega) (by rw [toNat_setWidth64]; exact hx), hbq, toNat_setWidth64,
    sub_modPm hx (by rw [q_eq]; omega) (hle i hi)]

/-! ## The function -/

/-- What `bitPack` leaves. -/
def BpPost (s₀ s' : State) : Prop :=
  bytesAt s'.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat =
    bitPack ((polyAt s₀.mem (s₀.gpr .r3)).map fun c => modPm c.val q) (lo s₀ .r4) (lo s₀ .r5)

theorem bp_wp {s₀ : State} (hp : BpPre s₀) : WP isa Impl.MlDsa.PPC64LE.Pack.bitPack s₀ (BpPost s₀) := by
  unfold Impl.MlDsa.PPC64LE.Pack.bitPack
  refine WP.seq (WP.mono (mov2Q_ok (a := .r3) (b := .r6) (by decide) (by decide) (by decide) s₀)
    fun s₁ ⟨⟨g10, g11, g7, m₁⟩, k₁⟩ => ?_)
  have ab := mem_bitPackParams hp.ab
  have go : ∀ {d c nb B : Nat}, Shape d c nb → lo s₀ .r5 = B → B ≤ 2 ^ 19 →
      loadBVal B = BitVec.ofNat 64 B → bitlen (lo s₀ .r4 + B) = d → ∀ s : State, Same s₁ s →
      WP isa (withB B (packLoop bpLd d c nb)) s (BpPost s₀) := by
    intro d c nb B hs hB hB19 hBl hd s hS
    have hlen := hp.len
    rw [hB, hd] at hlen
    have hBq : (BitVec.ofNat 64 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega
    refine WP.seq (WP.mono (loadB_ok .r4 hBl s) fun s₂ ⟨⟨g4, m₂⟩, k₂⟩ => ?_)
    refine WP.mono (packLoop_ok (bpLd_ok B) (RB_stable B) hs (pf := s₀.gpr .r3) (po := s₀.gpr .r6)
      (m₀ := s₀.mem) (rd := s₀.rd) (wr := s₀.wr) (sE := s₂)
      ⟨g4, by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g7]⟩
      (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hp.wr, hlen]; exact List.mem_singleton_self _)
      (by rw [← hlen]; exact hp.disj) (fun i hi => ?_)
      (by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g10]) (by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g11])
      (by rw [k₂.2.1, hS.1.2.1, k₁.2.1]) (by rw [k₂.2.2, hS.1.2.2, k₁.2.2]) (by rw [m₂, hS.2, m₁])
      (Keep.refl _ _))
      fun s₃ ⟨hbytes, _, _⟩ => ?_
    · obtain ⟨h₁, h₂⟩ := hp.bnd i hi
      rw [hB] at h₂
      have hx := hp.red i hi
      rw [bpVal, bm_toNat (by omega) (by rw [toNat_setWidth64]; exact hx), hBq, toNat_setWidth64,
        ← sub_modPm hx (by rw [q_eq]; omega) h₂, ← hd, ← hB]
      exact lt_bitlen (sub_modPm_le h₁ (by rw [hB]; exact h₂))
    · rw [BpPost, hlen, hbytes, bitPack_eq, ← hB, ← hd, hB,
        bitPack_vals hp.red hB19 (fun i hi => by rw [← hB]; exact (hp.bnd i hi).2)]
  refine sel_ok .r5 (by decide) 2 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n2 => ?_)
  · have e5 : lo s₁ .r5 = lo s₀ .r5 := by simp only [lo]; rw [k₁.gpr (by decide)]
    rw [e5] at e
    exact go (d := 3) (c := 8) (nb := 3) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 2 by omega]; decide) s₂ h₂
  have e5 : ∀ s, Same s₁ s → lo s .r5 = lo s₀ .r5 := fun s h => by
    simp only [lo]; rw [h.1.gpr (by decide), k₁.gpr (by decide)]
  rw [e5 s₁ ⟨Keep.refl _ _, rfl⟩] at n2
  refine sel_ok .r5 (by decide) 4 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n4 => ?_)
  · rw [e5 s₂ h₂] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 4 by omega]; decide) s₃ (h₂.trans h₃)
  rw [e5 s₂ h₂] at n4
  refine sel_ok .r5 (by decide) 4096 (by decide) (by decide) _ _ s₃ (fun s₄ h₄ e => ?_) (fun s₄ h₄ n4096 => ?_)
  · rw [e5 s₃ (h₂.trans h₃)] at e
    exact go (d := 13) (c := 8) (nb := 13) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 4095 by omega]; decide) s₄ ((h₂.trans h₃).trans h₄)
  rw [e5 s₃ (h₂.trans h₃)] at n4096
  refine sel_ok .r5 (by decide) 131072 (by decide) (by decide) _ _ s₄ (fun s₅ h₅ e => ?_) (fun s₅ h₅ n17 => ?_)
  · rw [e5 s₄ ((h₂.trans h₃).trans h₄)] at e
    exact go (d := 18) (c := 4) (nb := 9) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 131071 by omega]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)
  · rw [e5 s₄ ((h₂.trans h₃).trans h₄)] at n17
    have e : lo s₀ .r5 = 524288 := by omega
    exact go (d := 20) (c := 2) (nb := 5) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 524287 by omega]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)

/-! ## Constant time -/

theorem bitPack_ct :
    ConstantTime isa (bitPackContract PPC64LE.abi).pre (bitPackContract PPC64LE.abi).pub
      Impl.MlDsa.PPC64LE.Pack.bitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.PPC64LE.Pack.bitPack
  refine RelCT.seq (R := Agr .r5) (((relct_noMem (by rfl)).wpDep
    (F := fun (σ s' : State) => ((s'.gpr .r10 = σ.gpr .r3 ∧ s'.gpr .r11 = σ.gpr .r6 ∧
      s'.gpr .r7 = BitVec.ofNat 64 q ∧ s'.mem = σ.mem) ∧ Keep [.r10, .r11, .r7] σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (mov2Q_ok (by decide) (by decide) (by decide) a),
      WP.withSp (mov2Q_ok (by decide) (by decide) (by decide) b)⟩).mono (fun _ _ h => h)
    fun a' b' ⟨_, σ₁, σ₂, ⟨_, _, hpub⟩, ⟨⟨⟨g₁, h₁, _⟩, k₁⟩, p₁⟩, ⟨⟨⟨g₂, h₂, _⟩, k₂⟩, p₂⟩⟩ => by
      sig_pub [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
      obtain ⟨hsp, e3, -, e5, e6, -⟩ := hpub
      refine ⟨by rw [p₁, p₂, hsp], by rw [g₁, g₂, e3], by rw [h₁, h₂, e6], ?_⟩
      simp only [lo]; rw [k₁.gpr (by decide), k₂.gpr (by decide), e5]) ?_
  exact sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
    (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
      (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
        (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide)) (leaf_ct (by taint_decide)))))

/-! ## `Verified` -/

/-- A state satisfying the precondition. -/
def bpSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 2 | .r5 => 2 | .r6 => 0x2000 | .r7 => 96 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 96⟩]

example : ∃ pre post leak, bitPackContract PPC64LE.abi =
    bitPackSig.contract PPC64LE.target.abi pre post true 0 leak := ⟨_, _, _, rfl⟩

theorem bitPack_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Pack.bitPack (bitPackContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, bitPack_ct, ?_⟩
  · obtain ⟨t, s', he, hpost⟩ := bp_wp (BpPre.of hs)
    refine ⟨t, s', he, abi_of (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel) he, ?_⟩
    sig_post [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hpost
  · refine ⟨bpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | (simp only [bitPackParams]; decide +kernel)
        | (unfold Reduced; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Pack
