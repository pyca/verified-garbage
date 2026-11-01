module

import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Layout
import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Crypt
import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Camellia.PreparedEncrypt
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Layout
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Crypt
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Prepared
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Camellia.PreparedEncrypt
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Camellia.Common
meta import VerifiedGarbage.Proof.Camellia.CtrCipher
meta import VerifiedGarbage.Proof.Camellia.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Camellia.AArch64.ModeCore
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.Prepared

/-!
# The serial core's two functions meet their contracts

`prepare_verified` and `crypt_verified`: `vg_camellia_prepare_encrypt_keys`
and `vg_camellia_encrypt_prepared` against
`Proof.Camellia.Prepared.prepareEncryptContract` and
`encryptPreparedContract`, with `layout`. Each runs the serial core's half
(`prepare_wp`, `crypt_wp`) from the state narrowed to the core's 418 slots
of the working space, and then from the whole working space
(`Exec.widen`). The preparation changes only the table's 528 bytes, a
block only its own 16. A block is encrypted under the words of any table
its working space holds: the run from it is the run from the table the
precondition gives (`Exec.det`). Constant time by the taint analysis with
public values in vector registers: the pointers, `ws_len` and `rounds` are
public.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Modes.AArch64 (ScrIn runBlock_app)
open VG.Spec.Camellia.Prepared (Holds Keeps)

/-! ## Narrowing the working space -/

/-- `s` with its writable region the core's slots at `ws`. -/
abbrev narrowWs (s : State) (ws : Addr) : State := s.withRegions s.rd [⟨ws, 8 * core.total⟩]

/-- A run from the narrowed state is a run from `s`, to the state with `s`'s regions. -/
theorem exec_widenWs {c : Prog isa} {s s' : State} {t : List Leak} {ws : Addr} {len : Nat}
    (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * core.total ≤ len) (h : Exec isa c (narrowWs s ws) t s') :
    Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have hc : Covers [⟨ws, 8 * core.total⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨ws, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by show 0 + 8 * core.total ≤ len; omega⟩
  have := Exec.widen h (Covers.append (Covers.refl _) hc) hc
  rw [show (narrowWs s ws).rd = s.rd from rfl] at this
  rwa [State.withRegions_withRegions, State.withRegions_self] at this

theorem size_eq : layout.size = 3344 := rfl

theorem toNat_ofNat_rounds {R : BitVec 64} : BitVec.ofNat 64 R.toNat = R := by
  apply BitVec.eq_of_toNat_eq; simp

/-- The callee-saved registers and the rest of the ABI. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hv : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : abiPreserved s s' :=
  ⟨hg, Exec.sp he, hv⟩

/-! ## The preparation -/

/-- `vg_camellia_prepare_encrypt_keys` on AArch64. -/
def prepAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 272⟩
    let ws : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩
    s.rd = [sched] ∧ s.wr = [ws] ∧ sched.Disjoint ws ∧ (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + (s.gpr .x3).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .x3).toNat
  post s s' :=
    Holds layout s'.mem (s.gpr .x2) (s.gpr .x1).toNat
        (Spec.Camellia.Prepared.wordsAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) .encrypt ∧
      Keeps (s.gpr .x2) (s.gpr .x3).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- The preparation from the narrowed state: the table ready, only its 528
bytes changed, `x21` kept. -/
theorem prepareEncrypt_wp {s : State} {B p : Addr} {R : Nat} (hB : s.gpr .x2 = B) (hp : s.gpr .x0 = p)
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : R = 18 ∨ R = 24)
    (hs : ScrIn s B core.total) (hin : (⟨p, 272⟩ : Region) ∈ s.rd) (hfit : p.toNat + 272 ≤ 2 ^ 64)
    (hdis : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * core.total⟩) :
    WP isa prepareEncrypt s fun t => Ready t.mem B (R, schedWords s.mem p R) ∧
      Frame [⟨B, 528⟩] s.mem t.mem ∧ t.gpr .x21 = s.gpr .x21 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s sb .x2
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x9 .x21
  have e : runBlock isa [movR sb .x2, movR .x9 .x21] s = some s₂ := by
    rw [show [movR sb .x2, movR .x9 .x21] = [movR sb .x2] ++ [movR .x9 .x21] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂]
  have b₂ : s₂.gpr sb = B := by rw [o₂ _ (by decide), r₁, hB]
  have x9₂ : s₂.gpr .x9 = s.gpr .x21 := by rw [r₂, o₁ _ (by decide)]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have hk : VG.Proof.Camellia.AArch64.KeyArgs s₂ [⟨B, 8 * core.total⟩] (R, schedWords s.mem p R) :=
    ⟨p, by rw [o₂ _ (by decide), o₁ _ (by decide), hp], by rw [o₂ _ (by decide), o₁ _ (by decide), hx1], hR,
      by rw [mem₂], by rw [rd₂']; exact hin, hfit, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hdis⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, e, ?_⟩)
  have w := WP.gprs (rs := [.x9]) (prepare_wp b₂ ⟨by rw [wr₂']; exact hs.wr, hs.fit⟩ List.mem_cons_self hk)
    (by lit_decide) (by lit_decide)
  refine WP.seq (WP.mono w fun t h => ?_)
  obtain ⟨⟨tr, -, -, -, -, tf, trd, twr⟩, t9⟩ := h
  obtain ⟨u, eu, ru, -, mu, rdu, wru⟩ := Modes.AArch64.movR_ok t .x21 .x9
  refine WP.of_runBlock ⟨u, eu, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mu]; exact tr
  · rw [mu, ← mem₂]; exact tf
  · rw [ru, t9 _ List.mem_cons_self, x9₂]
  · rw [rdu, trd, rd₂']
  · rw [wru, twr, wr₂']

theorem prep_correct (s : State) (hs : prepAArch64.pre s) :
    ∃ t s', Exec isa prepareEncrypt s t s' ∧ abiPreserved s s' ∧ prepAArch64.post s s' := by
  obtain ⟨hrd, hwr, dSW, fitK, fitW, hR, hsz⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * core.total ≤ (s.gpr .x3).toNat * 8 := by
    show 3344 ≤ _; omega
  have w := prepareEncrypt_wp (s := narrowWs s (s.gpr .x2)) (R := (s.gpr .x1).toNat) rfl rfl
    toNat_ofNat_rounds.symm hR ⟨by simp, by show (s.gpr .x2).toNat + 3344 ≤ 2 ^ 64; omega⟩
    (by simp [hrd]) fitK (dSW.sub_right (Region.sub_prefix hl))
  obtain ⟨t, s', he, ⟨hr, hf, h21, -, -⟩, hg⟩ := WP.gprs (rs := [.x19, .x20, .x22, .x23, .x24, .x25, .x26,
    .x27, .x28, .x30]) w (by lit_decide) (by lit_decide)
  have he' := exec_widenWs hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', abi_of he' (Exec.preservedV he' (by lit_decide)) fun r hr' => ?_,
    ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact h21
      | exact hg _ (by simp)
  · exact holds_of_ready hr .encrypt
  · exact keeps_of_frame (e := 0) (by simpa only [narrowWs, State.withRegions_mem, State.withRegions_gpr,
      BitVec.add_zero] using hf) (by decide) fitW (by omega)

theorem prepTaint_agree (s₁ s₂ : State) (_ : prepAArch64.pre s₁) (_ : prepAArch64.pre s₂)
    (hp : prepAArch64.pub s₁ s₂) : VectorTaint.Agree (VectorTaint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

theorem prep_ct : ConstantTime isa prepAArch64.pre prepAArch64.pub prepareEncrypt :=
  VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3]) prepTaint_agree
    (by taint_decide)

/-- A state satisfying the preparation's precondition. -/
def prepSat : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 418 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 418 * 8⟩]

theorem prepare_verified :
    Verified AArch64.target prepareEncrypt (Proof.Camellia.Prepared.prepareEncryptContract layout AArch64.abi) :=
  Verified.of_correct prep_correct prep_ct (by
    sig_implies [Proof.Camellia.Prepared.prepareEncryptContract, Proof.Camellia.Prepared.prepareEncryptSig,
      prepAArch64, AArch64.abi, AArch64.argRegs, size_eq] [prepSat] using prepSat)

/-! ## A block -/

/-- `vg_camellia_encrypt_prepared` on AArch64. -/
def cryptAArch64 : Contract AArch64.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x0).toNat = 18 ∨ (s.gpr .x0).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .x2).toNat ∧
      ∃ w, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w .encrypt
  post s s' :=
    (∀ w, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w .encrypt →
      Spec.Camellia.blocksAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (s.gpr .x0).toNat w) .encrypt
          (Spec.Camellia.blocksAt s.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .x1) (s.gpr .x2).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- A block from the narrowed state: encrypted under the ready table's
words, only its 16 bytes changed. -/
theorem encryptPrepared_wp {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr .x1 = B)
    (hx0 : s.gpr .x0 = BitVec.ofNat 64 k.1) (hs : ScrIn s B core.total) (ready : Ready s.mem B k) :
    WP isa encryptPrepared s fun t =>
      Frame [⟨B + BitVec.ofNat 64 768, 16⟩] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (B + BitVec.ofNat 64 768) 16 =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (B + BitVec.ofNat 64 768) 16) := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s sb .x1
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x1 .x0
  have e : runBlock isa [movR sb .x1, movR .x1 .x0] s = some s₂ := by
    rw [show [movR sb .x1, movR .x1 .x0] = [movR sb .x1] ++ [movR .x1 .x0] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂]
  have b₂ : s₂.gpr sb = B := by rw [o₂ _ (by decide), r₁, hB]
  have x1₂ : s₂.gpr .x1 = BitVec.ofNat 64 k.1 := by rw [r₂, o₁ _ (by decide), hx0]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, e, ?_⟩)
  refine WP.mono (crypt_wp b₂ ⟨by rw [wr₂, wr₁]; exact hs.wr, hs.fit⟩ (by rw [mem₂]; exact ready) x1₂)
    fun t h => ⟨?_, ?_⟩
  all_goals obtain ⟨-, -, -, -, -, tf, tc, -, -⟩ := h
  · rw [← mem₂]; exact tf
  · rw [tc, mem₂]

theorem blocks_of {B : Addr} {m m' : Mem} {K : Spec.Camellia.Subkeys}
    (h : Spec.Aes.bytesAt m' (B + BitVec.ofNat 64 768) 16 =
      Spec.Camellia.cipher K (Spec.Aes.bytesAt m (B + BitVec.ofNat 64 768) 16)) :
    Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb K .encrypt (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Camellia.ecb_eq]
  simp only [Spec.Camellia.blocksAt, layout, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
    BitVec.add_zero]
  rw [Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.bytesAt_eq_blockAt, Spec.Camellia.cipher,
    Proof.Camellia.ofFn_toList] at h
  refine congrArg (fun b => [b]) ?_
  exact Vector.toList_inj.mp h

theorem blocks_of_ecb {B : Addr} {m m' : Mem} {K : Spec.Camellia.Subkeys}
    (h : Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb K .encrypt (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks)) :
    Spec.Aes.bytesAt m' (B + BitVec.ofNat 64 768) 16 =
      Spec.Camellia.cipher K (Spec.Aes.bytesAt m (B + BitVec.ofNat 64 768) 16) := by
  rw [Proof.Camellia.ecb_eq] at h
  simp only [Spec.Camellia.blocksAt, layout, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
    BitVec.add_zero] at h
  rw [Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.bytesAt_eq_blockAt, Spec.Camellia.cipher,
    Proof.Camellia.ofFn_toList, (List.cons.inj h).1]
  rfl

theorem crypt_correct (s : State) (hs : cryptAArch64.pre s) :
    ∃ t s', Exec isa encryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptAArch64.post s s' := by
  obtain ⟨-, hwr, fitW, hR, hsz, w₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * core.total ≤ (s.gpr .x2).toNat * 8 := by
    show 3344 ≤ _; omega
  have hsN : ScrIn (narrowWs s (s.gpr .x1)) (s.gpr .x1) core.total :=
    ⟨by simp, by show (s.gpr .x1).toNat + 3344 ≤ 2 ^ 64; omega⟩
  have run := fun (w : List (BitVec 64)) (h : Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w .encrypt) =>
    encryptPrepared_wp (s := narrowWs s (s.gpr .x1)) (k := ((s.gpr .x0).toNat, w)) rfl
      toNat_ofNat_rounds.symm hsN (ready_of_holds hR h)
  obtain ⟨t, s', he, ⟨hf, -⟩, hg⟩ := WP.gprs (rs := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
    .x27, .x28, .x30]) (run w₀ hH) (by lit_decide) (by lit_decide)
  have he' := exec_widenWs hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', abi_of he' (Exec.preservedV he' (by lit_decide))
    fun r hr' => hg r (by simpa [preserved] using hr'), fun w hw => ?_, ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, hc⟩ := run w hw
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    exact blocks_of hc
  · exact keeps_of_frame hf (by decide) fitW (by show 784 ≤ _; omega)

theorem cryptTaint_agree (s₁ s₂ : State) (_ : cryptAArch64.pre s₁) (_ : cryptAArch64.pre s₂)
    (hp : cryptAArch64.pub s₁ s₂) : VectorTaint.Agree (VectorTaint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, hsp⟩ := hp
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

theorem crypt_ct : ConstantTime isa cryptAArch64.pre cryptAArch64.pub encryptPrepared :=
  VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2]) cryptTaint_agree
    (by taint_decide)

/-- A working space at `0x2000` holding the table of no words (all zeros)
for 18 rounds. -/
def cryptSatMem : Mem := fun a =>
  if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2000 + 3344 then layout.encode 18 [] .encrypt (a.toNat - 0x2000) else 0

theorem cryptSat_holds : Holds layout cryptSatMem 0x2000 18 [] .encrypt := by
  intro r hr i hi
  have hr' : r.1 + i < 3344 := by
    rw [layout_table] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only [Spec.Camellia.scheduleLength] at hi ⊢ <;> omega
  have ht : ((0x2000 : Addr) + BitVec.ofNat 64 (r.1 + i)).toNat = 0x2000 + (r.1 + i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x2000 : Addr).toNat = 0x2000 from rfl]; omega
  have hc : 0x2000 ≤ 0x2000 + (r.1 + i) ∧ 0x2000 + (r.1 + i) < 0x2000 + 3344 := ⟨by omega, by omega⟩
  simp only [cryptSatMem, ht, hc, and_self, ↓reduceIte]
  rw [show 0x2000 + (r.1 + i) - 0x2000 = r.1 + i by omega]

/-- A state satisfying the block's precondition. -/
def cryptSat : State where
  gpr r := match r with | .x0 => 18 | .x1 => 0x2000 | .x2 => 418 | _ => 0
  sp := 0x8000
  mem := cryptSatMem
  rd := []
  wr := [⟨0x2000, 418 * 8⟩]

theorem crypt_implies :
    cryptAArch64.Implies (Proof.Camellia.Prepared.encryptPreparedContract layout AArch64.abi) where
  pre := by
    sig_implies_pre [Proof.Camellia.Prepared.encryptPreparedContract, Spec.Camellia.Prepared.cryptSig,
      cryptAArch64, AArch64.abi, AArch64.argRegs]
  post := by
    sig_implies_post [Proof.Camellia.Prepared.encryptPreparedContract, Spec.Camellia.Prepared.cryptSig,
      cryptAArch64, AArch64.abi, AArch64.argRegs]
  pub := by
    sig_implies_pub [Proof.Camellia.Prepared.encryptPreparedContract, Spec.Camellia.Prepared.cryptSig,
      cryptAArch64, AArch64.abi, AArch64.argRegs]
  sat := by
    refine ⟨cryptSat, ?_⟩
    sig_pre [Proof.Camellia.Prepared.encryptPreparedContract, Spec.Camellia.Prepared.cryptSig, AArch64.abi,
      AArch64.argRegs]
    sig_and_intros
    all_goals first
      | decide
      | exact ⟨_, cryptSat_holds⟩
      | (rw [size_eq]; decide)

theorem crypt_verified :
    Verified AArch64.target encryptPrepared (Proof.Camellia.Prepared.encryptPreparedContract layout AArch64.abi) :=
  Verified.of_correct crypt_correct crypt_ct crypt_implies

end VG.Proof.Camellia.AArch64.Serial
