module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Interleaved counter mode and GHASH on AArch64: the counter mode

Untrusted: everything here is checked by Lean. `aesPart_ok`: `aesPart nr o`
(`Impl.Gcm.AArch64.Stitch`) leaves in `v0`–`v7` the eight text blocks at
`x9 + o` XORed with the keystream of the counter blocks `k … k + 7`, where
`w10` is the counter of the counter block at `x20 + 48` plus `k`: byte `t` of
`breg j` is byte `16 (k + j) + t` of the keystream (`keyStream`, as for
`vg_aes_ctr32_aes`) XORed with the text's. Each round loads its round key
into `v30` (`round_st`, `last_st` of `Proof/Aes/AArch64/Aese/Rounds.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.Impl.Gcm.AArch64.Stitch
open VG.Proof.Aes.AArch64.Aese (st KeyIs rnds round_st last_st keyIs_readW getD_st exec_ldrq ctrVec_st
  vbyte_xor vbyte_readW setV_v_self setV_v_of_ne setV_setV Fr exec_addImm_w sw32)
open VG.Proof.Aes.AArch64 (keyStream)
open VG.Spec.Aes (roundKey cipher addRoundKey)
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV v_write gpr_write_self
  gpr_write_of_ne mem_write rd_write wr_write sp_write)

/-! ## Registers -/

theorem breg_inj : ∀ i < 8, ∀ j < 8, breg i = breg j → i = j := by decide

theorem breg_ne_K (j : Nat) : breg j ≠ K := by unfold breg; split <;> decide
theorem breg_ne_P (j : Nat) : breg j ≠ P := by unfold breg; split <;> decide

/-- The registers `aesPart` writes. -/
abbrev aesV : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, K, P]

theorem breg_mem (j : Nat) : breg j ∈ aesV := by unfold breg; split <;> decide

/-! ## What the part needs -/

section
variable (s : State)

abbrev kp : Addr := s.gpr .x21
abbrev cbA : Addr := s.gpr .x20 + BitVec.ofNat 64 48
/-- The counter block, and its counter. -/
abbrev cbk : Spec.Gcm.Block := Spec.Gcm.blockAt s.mem (cbA s)
abbrev c0 : BitVec 32 := (cbk s).extractLsb' 0 32
end

/-- `aesPart nr o` can run from `s`, the counter in `w10` being the
counter block's plus `k`. -/
structure APre (nr o k : Nat) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  o_le : o ≤ 128
  keys : ∀ r ≤ nr, InRegions (s.rd ++ s.wr) (kp s + BitVec.ofNat 64 (16 * r)) 16
  ctr : InRegions (s.rd ++ s.wr) (cbA s + BitVec.ofNat 64 0) 16
  data : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16
  x10 : s.read .w .x10 = c0 s + BitVec.ofNat 32 k

/-- The key schedule of `nr` rounds at `x21`. -/
abbrev sch (nr : Nat) (s : State) : List Byte := Spec.Aes.bytesAt s.mem (kp s) (16 * (nr + 1))

/-- What it leaves: the blocks, and only `x10`, `x12` and `aesV` written. -/
structure APost (nr o k : Nat) (s s' : State) : Prop where
  out : ∀ j < 8, ∀ t < 16, vbyte (s'.v (breg j)) t =
    keyStream nr (sch nr s) (cbk s) (16 * (k + j) + t) ^^^
      s.mem (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) + BitVec.ofNat 64 t)
  x10 : s'.read .w .x10 = c0 s + BitVec.ofNat 32 (k + 8)
  fr : Fr [.x10, .x12] aesV s s'

/-! ## The counter blocks -/

/-- `ctr1 j`: counter block `k + j` into `breg j`. -/
theorem ctr1_ok (j : Nat) (hj : j < 8) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 48) 16) :
    WP isa (.block (ctr1 j)) s fun s' =>
      s'.v (breg j) = setLane (s.mem.readW (s.gpr .x20 + BitVec.ofNat 64 48) 128) 32 3
        (rev32 (s.read .w .x10 + BitVec.ofNat 32 j)) ∧ Fr [.x12] [breg j] s s' := by
  rw [ctr1, WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (by omega_arith), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (off := 48) (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp [State.setV, State.write, State.read, sw32]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]

/-- The counter block `k + j`, as `ctr1` builds it. -/
abbrev cvec (s : State) (k j : Nat) : BitVec 128 :=
  setLane (s.mem.readW (s.gpr .x20 + BitVec.ofNat 64 48) 128) 32 3
    (rev32 (c0 s + BitVec.ofNat 32 k + BitVec.ofNat 32 j))

theorem ctrs_ok {nr o k : Nat} {s : State} (hp : APre nr o k s) :
    WP isa (.block ((List.range 8).flatMap ctr1)) s fun s' =>
      (∀ j < 8, s'.v (breg j) = cvec s k j) ∧ Fr [.x12] aesV s s' := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 48) 16 := by
    have := hp.ctr; rwa [cbA, BitVec.add_zero] at this
  refine wp_range_flatMap (M := isa) (fun i s' => (∀ j < i, s'.v (breg j) = cvec s k j) ∧
      Fr [.x12] aesV s s') (fun i s₁ hi ⟨e₁, f₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), Fr.refl _ _ _⟩
  refine WP.mono (ctr1_ok i hi s₁ (by rw [f₁.rd, f₁.wr, f₁.gpr _ (by decide)]; exact hin))
    fun s' ⟨e, f⟩ => ⟨fun j hj => ?_, f₁.trans (f.mono (fun r h => h)
      (fun r h => by simp only [List.mem_singleton] at h; subst h; exact breg_mem i))⟩
  by_cases hji : j = i
  · subst hji
    have hx := hp.x10
    simp only [State.read] at hx
    rw [e, f₁.mem]
    simp only [State.read, f₁.gpr _ (by decide : Reg.x20 ∉ [Reg.x12]), f₁.gpr _ (by decide : Reg.x10 ∉ [Reg.x12])]
    rw [hx]
  · rw [f.v _ (by simp only [List.mem_singleton]; exact fun h => hji (breg_inj j (by omega_arith) i hi h)),
      e₁ j (by omega_arith)]

/-! ## The rounds -/

theorem fr_setV {gs : List Reg} {vs : List VReg} (s : State) {r : VReg} (x : BitVec 128) (h : r ∈ vs) :
    Fr gs vs s (s.setV r x) :=
  ⟨fun _ _ => rfl, fun _ hr' => setV_v_of_ne _ _ fun e => hr' (e ▸ h), rfl, rfl, rfl, rfl⟩

theorem fr_widen {vs : List VReg} {s s' : State} (h : Fr [] vs s s') (gs : List Reg) : Fr gs vs s s' :=
  h.mono (fun _ h => by simp at h) fun _ h => h

/-- The block registers hold the states before the `AddRoundKey` of round key `r`. -/
def RI (w : List Byte) (x : Nat → Spec.Aes.State) (r : Nat) (s : State) : Prop :=
  ∀ j < 8, addRoundKey (st (s.v (breg j))) (roundKey w r) = rnds w (x j) r

theorem aesround_run (j : Nat) (s : State) :
    runBlock isa [.vop (.aese (breg j) K), .vop (.aesmc (breg j) (breg j))] s =
      some (s.setV (breg j) (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K))))) :=
  Proof.Aes.AArch64.Aese.rnd_run K (breg j) s

/-- The eight states through a full round with the key in `v30`. -/
theorem rnd8_ok {w : List Byte} {x : Nat → Spec.Aes.State} {r : Nat} {s : State}
    (hk : KeyIs (s.v K) (roundKey w r)) (hI : RI w x r s) :
    WP isa (.block ((List.range 8).flatMap fun j =>
        [.vop (.aese (breg j) K), .vop (.aesmc (breg j) (breg j))])) s fun s' =>
      RI w x (r + 1) s' ∧ Fr [] aesV s s' ∧ s'.v K = s.v K := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, addRoundKey (st (s'.v (breg j))) (roundKey w (r + 1)) = rnds w (x j) (r + 1)) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, hK⟩ => ⟨e, f, hK⟩
  refine WP.of_runBlock ⟨_, aesround_run i s₁, ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [setV_v_self]
      refine round_st (k := s₁.v K) (by rw [k₁]; exact hk) ?_
      rw [u₁ j (Nat.le_refl _) hi]; exact hI j hi
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i)
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, k₁]

/-- Round key `r` into `v30`, and the eight states through the round. -/
theorem rnd_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {r : Nat}
    (hr : r + 1 ≤ nr) {s : State} (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x r s) :
    WP isa (.block (rnd r)) s fun s' => RI (sch nr s₀) x (r + 1) s' ∧ Fr [.x12] aesV s₀ s' := by
  have hR := hp.rounds
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hf.rd, hf.wr, hf.gpr _ (by decide)]; exact hp.keys r (by omega_arith)
  rw [rnd, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_arith) hin, ?_⟩
  have hk : KeyIs ((s.setV K (s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 128)).v K)
      (roundKey (sch nr s₀) r) := by
    rw [setV_v_self, hf.mem, hf.gpr _ (by decide)]
    exact keyIs_readW _ _ (by omega_arith)
  have hI' : RI (sch nr s₀) x r (s.setV K (s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16 * r)) 128)) :=
    fun j hj => by rw [setV_v_of_ne _ _ (breg_ne_K j)]; exact hI j hj
  exact WP.mono (rnd8_ok hk hI') fun s' ⟨e, f, _⟩ =>
    ⟨e, (hf.trans (fr_setV _ _ (by decide))).trans (fr_widen f _)⟩

theorem rnds_ok {nr o k : Nat} {s₀ : State} (hp : APre nr o k s₀) {x : Nat → Spec.Aes.State} {s : State}
    (hf : Fr [.x12] aesV s₀ s) (hI : RI (sch nr s₀) x 0 s) :
    ∀ n, n + 1 ≤ nr → WP isa (.block ((List.range n).flatMap rnd)) s fun s' =>
      RI (sch nr s₀) x n s' ∧ Fr [.x12] aesV s₀ s' := by
  intro n hn
  refine wp_range_flatMap (M := isa) (fun r s' => RI (sch nr s₀) x r s' ∧ Fr [.x12] aesV s₀ s')
    (fun r s₁ hr ⟨e₁, f₁⟩ => rnd_ok hp (by omega_arith) f₁ e₁) n (Nat.le_refl _) s ⟨hI, hf⟩

/-! ## The last round and the text -/

theorem aese_run (j : Nat) (s : State) :
    runBlock isa [.vop (.aese (breg j) K)] s =
      some (s.setV (breg j) (aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K)))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]

/-- `aese` of the eight states with the key in `v30`. -/
theorem aese8_ok (s : State) :
    WP isa (.block ((List.range 8).flatMap fun j => [.vop (.aese (breg j) K)])) s fun s' =>
      (∀ j < 8, s'.v (breg j) = aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K))) ∧
      Fr [] aesV s s' ∧ s'.v K = s.v K := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, s'.v (breg j) = aesMapBytes aesSbox (aesShiftRows (s.v (breg j) ^^^ s.v K))) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, hK⟩ => ⟨e, f, hK⟩
  refine WP.of_runBlock ⟨_, aese_run i s₁, ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; rw [setV_v_self, u₁ j (Nat.le_refl _) hi, k₁]
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i)
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, k₁]

theorem eor3_run (j o : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho : o + 16 * j < 65536) (ho' : (o + 16 * j) % 16 = 0) :
    runBlock isa [.ldrq P .x9 (o + 16 * j), .vop (.eor3 (breg j) (breg j) P K)] s =
      some ((s.setV P (s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128)).setV (breg j)
        (s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K)) := by
  rw [runBlock_cons]
  rw [exec_ldrq ⟨ho', ho⟩ hin, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (breg_ne_P j), setV_v_of_ne _ _ (by decide : K ≠ P)]

/-- The text blocks at `x9 + o` added to the states and the last round key (in `v30`). -/
theorem fin8_ok {o : Nat} (ho : o ≤ 128) (s : State)
    (hin : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho16 : o % 16 = 0) :
    WP isa (.block ((List.range 8).flatMap fun j =>
        [.ldrq P .x9 (o + 16 * j), .vop (.eor3 (breg j) (breg j) P K)])) s fun s' =>
      (∀ j < 8, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      Fr [] aesV s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, _⟩ => ⟨e, f⟩
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x9 + BitVec.ofNat 64 (o + 16 * i)) 16 := by
    rw [f₁.rd, f₁.wr, f₁.gpr _ (by decide)]; exact hin i hi
  refine WP.of_runBlock ⟨_, eor3_run i o s₁ hin₁ (by omega_arith) (by omega_arith), ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; rw [setV_v_self, u₁ j (Nat.le_refl _) hi, k₁, f₁.mem, f₁.gpr _ (by decide)]
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji), setV_v_of_ne _ _ (breg_ne_P j)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), setV_v_of_ne _ _ (breg_ne_P j), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    rw [setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i), setV_v_of_ne _ _ fun h => hr (by rw [h]; decide)]
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, setV_v_of_ne _ _ (by decide : K ≠ P), k₁]

/-! ## The part -/

theorem keyStream_byte {nr k j t : Nat} {w : List Byte} {icb : Spec.Gcm.Block} (ht : t < 16) :
    keyStream nr w icb (16 * (k + j) + t) = (cipher nr w (Proof.Aes.ctrState icb (k + j))).getD t 0 := by
  rw [keyStream, show (16 * (k + j) + t) / 16 = k + j by omega_arith, show (16 * (k + j) + t) % 16 = t by omega_arith]

theorem aesPart_ok {nr o k : Nat} {s : State} (hp : APre nr o k s) (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart nr o)) s (APost nr o k s) := by
  have hR := hp.rounds
  unfold aesPart
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ctrs_ok hp) fun s₁ ⟨e₁, f₁⟩ => ?_
  -- The counter blocks, as AES states.
  let x : Nat → Spec.Aes.State := fun j => Proof.Aes.ctrState (cbk s) (k + j)
  have hx : ∀ j < 8, st (cvec s k j) = x j := fun j _ => by
    show _ = Proof.Aes.ctrState _ _
    rw [cvec, BitVec.add_assoc, ← BitVec.ofNat_add, c0, cbk, cbA, ← ctrVec_st, BitVec.add_zero]
  have hI₁ : RI (sch nr s) x 0 s₁ := fun j hj => by rw [e₁ j hj, hx j hj]; rfl
  refine WP.mono (rnds_ok hp f₁ hI₁ (nr - 1) (by omega_arith)) fun s₂ ⟨e₂, f₂⟩ => ?_
  -- The last round.
  have g₂ : s₂.gpr .x21 = s.gpr .x21 := f₂.gpr _ (by decide)
  have hin : ∀ r ≤ nr, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16 :=
    fun r hr => by rw [f₂.rd, f₂.wr, g₂]; exact hp.keys r hr
  unfold lastRnd
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_arith) (hin (nr - 1) (by omega_arith)), ?_⟩
  generalize hK₁ : s₂.mem.readW (s₂.gpr .x21 + BitVec.ofNat 64 (16 * (nr - 1))) 128 = K₁
  refine WP.mono (aese8_ok _) fun s₃ ⟨e₃, f₃, _⟩ => ?_
  rw [WP.block_cons_iff]
  have hin₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 16 := by
    rw [f₃.rd, f₃.wr, f₃.gpr _ (by decide), rd_setV, wr_setV, gpr_setV]
    exact hin nr (Nat.le_refl _)
  refine ⟨_, exec_ldrq (by omega_arith) hin₃, ?_⟩
  generalize hK₂ : s₃.mem.readW (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 128 = K₂
  have g₃ : ∀ r, s₃.gpr r = s₂.gpr r := fun r => by rw [f₃.gpr r (by simp)]; rfl
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, mem_setV, f₂.mem]
  have hin₄ : ∀ j < 8, InRegions ((s₃.setV K K₂).rd ++ (s₃.setV K K₂).wr)
      ((s₃.setV K K₂).gpr .x9 + BitVec.ofNat 64 (o + 16 * j)) 16 := fun j hj => by
    rw [rd_setV, wr_setV, gpr_setV, f₃.rd, f₃.wr, g₃, rd_setV, wr_setV, f₂.rd,
      f₂.wr, f₂.gpr _ (by decide)]
    exact hp.data j hj
  refine WP.mono (fin8_ok hp.o_le _ hin₄ ho16) fun s₄ ⟨e₄, f₄⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (imm := 8) (by decide), WP.block_nil ?_⟩
  -- The keys, and the last round of each block.
  have hk₁ : KeyIs K₁ (roundKey (sch nr s) (nr - 1)) := by
    rw [← hK₁, f₂.mem, g₂]; exact keyIs_readW _ _ (by omega_arith)
  have hk₂ : KeyIs K₂ (roundKey (sch nr s) nr) := by
    rw [← hK₂, m₃, g₃, g₂]; exact keyIs_readW _ _ (by omega_arith)
  have g₉ : s₃.gpr .x9 = s.gpr .x9 := by rw [g₃, f₂.gpr _ (by decide)]
  refine ⟨fun j hj t ht => ?_, ?_, ?_⟩
  · rw [v_write, e₄ j hj, v_setV_of_ne _ _ (breg_ne_K j), e₃ j hj, v_setV_of_ne _ _ (breg_ne_K j),
      v_setV_self, v_setV_self, mem_setV, gpr_setV, m₃, g₉,
      show ∀ A M C : BitVec 128, A ^^^ M ^^^ C = (A ^^^ C) ^^^ M from fun A M C => by ac_rfl, vbyte_xor,
      vbyte_readW _ _ ht, keyStream_byte ht, ← getD_st _ ht,
      last_st hk₁ hk₂ (e₂ j hj)]
  · have hx := hp.x10
    have g₁₀ : s₄.gpr .x10 = s.gpr .x10 := by
      rw [f₄.gpr _ (by simp), gpr_setV, g₃, f₂.gpr _ (by decide)]
    simp only [State.read] at hx ⊢
    rw [gpr_write_self, sw32, g₁₀, hx, BitVec.add_assoc, ← BitVec.ofNat_add]
  · have f₄' : Fr [] aesV s₃ s₄ := (fr_setV _ _ (by decide)).trans f₄
    have f₃' : Fr [] aesV s₂ s₃ := (fr_setV _ _ (by decide)).trans f₃
    refine ((f₂.trans (fr_widen (f₃'.trans f₄') _)).mono (fun r h => List.mem_cons_of_mem _ h)
      (fun _ h => h)).trans ⟨fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact gpr_write_of_ne _ _ _ hr.1

end VG.Proof.Gcm.AArch64.Stitch
