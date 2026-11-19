module

public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Front
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root

/-! ### `EcKey.Compressed.X86_64.DecompressContract`, which this module and modules that import it used -/

section

/-! # Decompression's signature obligations on x86-64 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 2 * C.len + 1⟩
    let pk : Region := ⟨s.gpr .rsi, C.len + 1⟩
    let ws : Region := ⟨s.gpr .rdx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      ret.Disjoint out ∧ ret.Disjoint ws ∧
      (s.gpr .rdi).toNat + 2 * C.len + 1 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (C.len + 1)) with
    | some Q => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 8).pre s) :
    (decompressContract I.curve root).Implies (I.decompressPublicKeyContract abi 8) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨h.1, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨h.1, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  sat := hsat

theorem decompress_post_patch (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (decompressContract C root).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (decompressContract C root).post s b) :
    (decompressContract C root).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hn : 2 * C.len + 1 ≤ 2 ^ 64 := by
    obtain ⟨_, _, _, _, _, _, _, hf, _⟩ := hs
    omega_using [hf]
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 2 * C.len + 1)
    (by rw [hs.2.1]; simp) hn
  simpa only [decompressContract, State.patch_gpr, VG.X86_64.EcKey.bytesAt_patch hb] using hp

def decompressSatState (len : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x8000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, len + 1⟩]
  wr := [⟨0x1000, 2 * len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.Parity`, which only this module used -/

section

/-! # Select and check the canonical root's parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.X86_64.QY + 8 ≤ size) (ht : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.parityMask c)) s fun s' =>
      s'.gpr .rcx = mask (sv c base s Impl.Ecdh.X86_64.QY % 2 ≠
        (word s.mem base (c.sl D)).toNat % 2) ∧ Keeps [.rdx, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.X86_64.parityMask, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, readSrc32, execAlu, Option.map_some, Option.bind_some, State.load64,
    State.setReg32, ea_sc, hs.rdi, ld_sc hs hy, ld_sc hs ht,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change (0 : BitVec 64) - ((word s.mem base (c.sl Impl.Ecdh.X86_64.QY) ^^^
      word s.mem base (c.sl D)) &&& 1) = _
    rw [xor_low_mask, slot_parity _ _ _ _ hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .rcx = mask P) :
    WP isa (.block [.mov .rdx (.reg .rcx), .alu .xor .rdx (.imm (-1))]) s fun s' =>
      s'.gpr .rdx = mask (¬ P) ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [h]
    by_cases hp : P <;> simp [mask, hp]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.Frame`, which this module and modules that import it used -/

section

/-! # Frames for the converter's scratch slots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdsa.X86_64

theorem unch_same {base : Addr} {W : List (Nat × Nat)} {a b c : Mem}
    (h₁ : Unch base W a b) (h₂ : Unch base W b c) : Unch base W a c :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem slot_frame {c : Cfg} {base : Addr} {a b : Mem} {i len : Nat} {slots : List Nat}
    (hi : i ∈ slots) (hlen : len ≤ 8 * c.n) (h : Outside base (c.sl i) len a b) :
    Unch base (slW c slots) a b :=
  (h.mono (o' := c.sl i) (n' := 8 * c.n) (Nat.le_refl _) (by omega_using [hlen])).unch.mono fun w hw => by
    obtain rfl := List.mem_singleton.mp hw
    exact List.mem_map_of_mem hi

theorem slots_widen {c : Cfg} {base : Addr} {a b : Mem} {slots slots' : List Nat}
    (h : Unch base (slW c slots) a b) (hsub : ∀ i ∈ slots, i ∈ slots') :
    Unch base (slW c slots') a b := h.mono fun w hw => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact List.mem_map_of_mem (hsub i hi)

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.Candidate`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86_64.RootPow`, which this module and modules that import it used -/

section

/-! # The root exponentiation's workspace layout -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

/-- The square-root power uses the same accumulator and temporary as the
existing powers, and a table separate from Montgomery's temporary area. -/
theorem rootPow_lay {c : Cfg} (hc : BaseCfgOk c) {j : Nat} (hj : j < 3)
    (hsep : j ≠ 1 ∨ c.n ≠ 9) :
    PowLay (Impl.EcKey.Compressed.X86_64.rootPow c ACC j) size :=
  powLay_of hc (jm := MP) (by decide) _ hj (base := W2) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide) ⟨by have := hc.n0; omega_using [this], Nat.le_refl _⟩ hsep

/-- The precise writes of one root exponentiation. -/
abbrev rootPowerWrites (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    powW (Impl.EcKey.Compressed.X86_64.rootPow c ACC j)

theorem rootPower_apart {c : Cfg} {i j : Nat} (hi : i < 45) (hw : i ∉ [EXPP, ACC, PT, TMP]) :
    ∀ w ∈ rootPowerWrites c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  change ∀ w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++ slW c [ACC, PT, TMP], _
  apply apart_append
  · intro w h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact sl_apart c (by intro h; exact hw (h ▸ (by simp)))
    · exact (apart_tbl hi j (.inl (by intro h; exact hw (h ▸ (by simp))))) _ (by simp)
  · exact apart_slW (fun h => hw (List.mem_cons_of_mem _ h))

/-- Materializing an exponent and running the field power. -/
theorem rootPower_ok {c : Cfg} (hc : BaseCfgOk c) {e j : Nat}
    (hj : j < 3) (hsep : j ≠ 1 ∨ c.n ≠ 9) (he : e < 2 ^ (64 * c.n))
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86_64.rootPower c e j).inline s fun s' =>
      KeepRegs (powClob c.n) s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
        powW (Impl.EcKey.Compressed.X86_64.rootPow c ACC j)) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have h0 := hc.n0
  have hE := sl_le c h7 (i := EXPP) (by decide)
  rw [Impl.EcKey.Compressed.X86_64.rootPower]
  change WP isa (.seq (.block (setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n))
      (pow (Impl.EcKey.Compressed.X86_64.rootPow c ACC j)))) s _
  refine WP.seq (WP.mono (setConst_ok hs hE he) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ h0 (by omega_using [h7]) hE (bitsAt_le c h7 hj)
    (sl_apart_bits c (i := EXPP) (j := j) (by decide) (.inl (by decide)) (64 * c.n) (by omega_using [])))
    fun s₂ ⟨bits₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have keep₂ {i : Nat} (hi : i < 45) (hiE : i ≠ EXPP) (hiT : i ≠ TMP) :
      sv c base s₂ i = sv c base s i := by
    have hsl := sl_le c h7 hi
    rw [sv, O₂.wordsVal (sl_apart_bits c hi (.inl hiT) (64 * c.n) (by omega_using [])) (by omega_using [hn, hsl]),
      O₁.wordsVal (sl_apart c hiE) (by omega_using [hn, hsl])]
  have hM₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = c.C.p
    rw [keep₂ (by decide) (by decide) (by decide)]
    exact hM.val)
  have B₂ : wordsVal s₂.mem base (c.sl W2) c.n < c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl W2) c.n = sv c base s₂ W2 from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hB
  have O₂' : wordsVal s₂.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl ONEP) c.n = sv c base s₂ ONEP from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hO
  refine WP.mono (pow_ok (rootPow_lay hc (j := j) hj hsep)
    (unitMod_pow_two hc.p_odd (64 * c.n)) hs₂ hM₂ B₂ O₂'
    (by simpa only [e₁, Impl.EcKey.Compressed.X86_64.rootPow] using bits₂) he) fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ?_
  refine ⟨?_, (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  · exact ((k₁.mono (by simp [powClob, clob])).trans (k₂.mono (by simp [powClob, clob]))).trans k₃
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
    rw [keep₂ (by decide) (by decide) (by decide)] at v₃
    exact v₃

/-- The three-mod-four candidate uses an exponent derived from the prime. -/
theorem rootThree_ok {c : Cfg} (hc : BaseCfgOk c) (hp : c.C.p % 4 = 3)
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86_64.rootCandidate c).inline s fun s' =>
      KeepRegs (powClob c.n) s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n 2, 64 * c.n)] ++
        powW (Impl.EcKey.Compressed.X86_64.rootPow c ACC 2)) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.X86_64.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide) (.inl (by decide))
    (by have := hc.p_lt; have := hc.p_ge; omega_arith) hs hM hB hO

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! # The machine root candidate's shared refinement interface -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (W0 W2)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

/-- Writes shared by exponentiation and the P-224 descent. -/
def candidateSlots : List Nat := [ACC, PT, TMP, EXPP, EXPN, T0, T1, T2, T3, T4, T5, W0]
def candidateWrites (c : Cfg) : List (Nat × Nat) := slW c candidateSlots ++
  [(bitsAt c.n 1, 64 * c.n), (bitsAt c.n 2, 64 * c.n)]

structure CandidatePost (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (base : Addr) (s s' : State) : Prop where
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (candidateWrites c) s.mem s'.mem
  lt : sv c base s' ACC < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

/-- This is discharged by the assembly proofs for each root method. -/
def CandidateCorrect (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), Scr s base size →
    ModOkW c.MP' size c.C.p s.mem base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (Impl.EcKey.Compressed.X86_64.rootCandidate c).inline s (CandidatePost c root base s)

theorem candidate_fixed (c : Cfg) : FixedOk c (candidateWrites c) :=
  (fixedOk_slW (l := candidateSlots) (by decide)).append (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact fixedOk_tbl 1 _ (by simp)
    · exact fixedOk_tbl 2 _ (by simp))

theorem candidate_apart {c : Cfg} {i : Nat} (hi : i < 45) (hw : i ∉ candidateSlots) :
    ∀ w ∈ candidateWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  apply apart_append (apart_slW hw)
  intro w h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact (apart_tbl (c := c) hi 1 (.inl (by intro he; exact hw (he ▸ (by decide))))) _ (by simp)
  · exact (apart_tbl (c := c) hi 2 (.inl (by intro he; exact hw (he ▸ (by decide))))) _ (by simp)

theorem candidateThree_correct {c : Cfg} (hc : BaseCfgOk c) (hp : c.C.p % 4 = 3) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := by
  intro base s hs hM hB hO
  refine WP.mono (rootThree_ok hc hp hs hM hB hO) fun s' ⟨k, U, lt, v⟩ => ?_
  refine ⟨k, U.mono ?_, lt, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, powW,
      Impl.EcKey.Compressed.X86_64.rootPow] at hw
    rcases hw with (rfl | rfl) | rfl | rfl | rfl
    all_goals simp [candidateWrites, candidateSlots, slW, MP'_n, MP'_tmp]
  · simpa only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow] using v

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.DecompressFinish`, which only this module used -/

section

/-! # Write the checked uncompressed encoding and restore the ABI -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.EcKey.X86_64 (lead_ok)

theorem decompressFinish_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.decompressFinish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (([.mov32 .rax (.imm 4), .alu .and .rax (.reg .rcx), .store8 { base := .rsi, disp := 0 } .rax] :
      List Instr) ++
    (storeBytes c.C.len c.n .rsi 1 (c.sl E) ++ (storeBytes c.C.len c.n .rsi (1 + c.C.len) (c.sl Impl.Ecdh.X86_64.QY) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Spill.restoreCode .rdi Cfg.saved)))) := by
  simp only [Impl.EcKey.Compressed.X86_64.decompressFinish, List.append_assoc]; rfl

/-- The result, the return value and the callee-saved registers. -/
theorem decompressFinish_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hrsi : s.gpr .rsi = out) (hw : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 2 * c.C.len⟩ ⟨base, size⟩) (hfit : out.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.decompressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++ toBytes c.C.len (sv c base s Impl.Ecdh.X86_64.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧
      (∀ r, r ∉ [.rax, .rcx, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have hn := hs.nowrap
  obtain hX := sl_le c h7 (i := E) (by decide)
  obtain hY := sl_le c h7 (i := Impl.Ecdh.X86_64.QY) (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain h1 : ∀ e, out + BitVec.ofNat 64 1 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 (1 + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  obtain hq : ∀ d, d + c.C.len ≤ 1 + 2 * c.C.len → (out + BitVec.ofNat 64 d).toNat + c.C.len ≤ 2 ^ 64 :=
    fun d hd => by
      rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega_using [hfit, hd]),
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_using [hfit, hd]
  obtain hwr : ∀ {t : State} {d : Nat}, (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ t.wr →
      d + c.C.len ≤ 1 + 2 * c.C.len →
      ∀ e m, e + m ≤ c.C.len → InRegions t.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m :=
    fun hw' hd e m hm => ⟨_, hw', by rw [Offset.add_add]; exact Offset.contains_base out (by omega_using [hd, hm]) (by omega_using [hfit, hd, hm])⟩
  obtain hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  obtain hscd : ∀ {d k : Nat}, d + k ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, k⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  obtain hout : out + BitVec.ofNat 64 0 = out := BitVec.add_zero out
  rw [decompressFinish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega_using [hn0, hF])) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain hrsi₁ : s₁.gpr .rsi = out := by rw [k₁.1 _ (by decide), hrsi]
  rw [WP.block_append_iff]
  obtain hc0 : (⟨out, 1 + 2 * c.C.len⟩ : Region).Contains out 1 := by
    have := Offset.contains_base out (d := 0) (n := 1) (k := 1 + 2 * c.C.len) (by omega_using []) (by omega_using [])
    rwa [hout] at this
  refine WP.mono (lead_ok hrsi₁ ⟨_, by rw [k₁.2.2.2]; exact hw, hc0⟩ b (by rw [e₁, hf]))
    fun s₂ ⟨e₂, O₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain U₂ := O₂.unch_far (by have := hscd (d := 0) (k := 1) (by omega_using []); rwa [hout] at this)
  obtain hrsi₂ : s₂.gpr .rsi = out := by rw [k₂.gpr _ (by decide), hrsi₁]
  obtain hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  obtain x₂ : wordsVal s₂.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_using [hX]) (by omega_using [hn, hX]), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂ (dst := .rsi) (d := 1) (a := c.sl E) (by decide) (by decide) b
    hrcx₂ hX (by omega_arith) hc.len_lo hc.len_hi (by rw [hrsi₂]; exact hq 1 (by omega_using []))
    (by rw [hrsi₂]; exact hwr (by rw [k₂.wr, k₁.2.2.2]; exact hw) (by omega_using []))
    (by rw [hrsi₂]; exact hdsc hX (by omega_using []))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hrsi₂] at e₃ O₃
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain U₃ := O₃.unch_far (hscd (d := 1) (by omega_using []))
  obtain hrsi₃ : s₃.gpr .rsi = out := by rw [k₃.gpr _ (by decide), hrsi₂]
  obtain hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hrcx₂]
  obtain y₃ : wordsVal s₃.mem base (c.sl Impl.Ecdh.X86_64.QY) c.n = sv c base s Impl.Ecdh.X86_64.QY := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_using [hY]) (by omega_using [hn, hY]),
      U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_using [hY]) (by omega_using [hn, hY]), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₃ (dst := .rsi) (d := 1 + c.C.len) (a := c.sl Impl.Ecdh.X86_64.QY)
    (by decide) (by decide) b hrcx₃ hY (by omega_arith) hc.len_lo hc.len_hi (by rw [hrsi₃]; exact hq _ (by omega_using []))
    (by rw [hrsi₃]; exact hwr (by rw [k₃.wr, k₂.wr, k₁.2.2.2]; exact hw) (by omega_using []))
    (by rw [hrsi₃]; exact hdsc hY (by omega_using []))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hrsi₃] at e₄ O₄
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain U₄ := O₄.unch_far (hscd (d := 1 + c.C.len) (by omega_using []))
  obtain hrcx₄ : s₄.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₄.gpr _ (by decide), hrcx₃]
  obtain lead : Spec.Ecdsa.bytesAt s₄.mem out 1 = [if b then 4 else 0] := by
    rw [bytesAt_keep O₄ (Offset.base_disjoint out (by omega_using []) (by omega_using [hfit])) (by omega_using [hfit]) (by omega_using []),
      bytesAt_keep O₃ (Offset.base_disjoint out (by omega_using []) (by omega_using [hfit])) (by omega_using [hfit]) (by omega_using [])]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, hout, e₂]
  obtain first : Spec.Ecdsa.bytesAt s₄.mem (out + BitVec.ofNat 64 1) c.C.len =
      if b then toBytes c.C.len (sv c base s E) else List.replicate c.C.len 0 := by
    rw [bytesAt_keep O₄ (Offset.disjoint out (by omega_using []) (by omega_using [hfit]) (by omega_using [hfit])) (by omega_using [hfit]) (by omega_using [hfit]), e₃, x₂]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  obtain hsv₅ : Spill.Saved s₅.mem base g Cfg.saved := by
    rw [k₅.2.1]
    obtain h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (Saved.unch (Saved.unch (hm₁ ▸ hsv) h48 U₂) h48 U₃) h48 U₄
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₅ (by decide) (fun p hp => ?_)
    (by rw [hs₅.rdi]; exact hsv₅)) fun s₆ ⟨g₆, r₆, m₆, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₅.rdi]; exact ⟨_, List.mem_append_right _ hs₅.wr, hs₅.contains (by have : size = 8192 := rfl; omega_arith) (by decide)⟩
  refine ⟨?_, ?_, g₆, fun r hr => ?_⟩
  · rw [m₆, k₅.2.1, bytesAt_add, show 2 * c.C.len = c.C.len + c.C.len by omega_using [], bytesAt_add, lead, first,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, e₄, y₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, ← List.replicate_append_replicate]; rfl
    · simp only [ite_true]; rfl
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₆ _ hra, e₅, hrcx₄, mask_bit]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [r₆ r (by simp [Cfg.saved, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      k₅.1 r (by simp [hr.1]), k₄.gpr r (by simp [hr.1, hr.2.2.1]), k₃.gpr r (by simp [hr.1, hr.2.2.1]),
      k₂.gpr r (by simp [hr.1]), k₁.1 r (by simp [hr.2.1])]

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.Peer`, which only this module used -/

section

/-! # Compressed tag, canonical x and curve constants -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/TagCheck.lean`, which only this module imported.
section

/-! # Accept exactly SEC 1 tags 02 and 03, retaining the parity bit -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

private theorem tag_key : ∀ b : Byte,
    ((b.setWidth 64 &&& BitVec.signExtend 64 (-2 : BitVec 32)) ^^^
      BitVec.signExtend 64 (2 : BitVec 32) = 0) = (b = 2 ∨ b = 3) := by
  decide

theorem decompressTag_ok {c : Cfg} {s : State} {base q : Addr}
    (hs : Scr s base size) (hq : s.gpr .r9 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.decompressTag c)) s fun s' =>
      s'.gpr .rdx = mask (s.mem q = 2 ∨ s.mem q = 3) ∧
      word s'.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      KeepRegs [.rdx] s s' ∧ Outside base (c.sl D) 8 s.mem s'.mem := by
  rw [show Impl.EcKey.Compressed.X86_64.decompressTag c =
    [.movzx8 .rdx { base := .r9 }, .store (sc (c.sl D)) .rdx,
      .alu .and .rdx (.imm (-2)), .alu .xor .rdx (.imm 2)] ++
    ([.alu .cmp .rdx (.imm 1)] ++ [.alu .sbb .rdx (.reg .rdx)]) from rfl,
    WP.block_append_iff]
  refine WP.mono (show WP isa (.block
    [.movzx8 .rdx { base := .r9 }, .store (sc (c.sl D)) .rdx,
      .alu .and .rdx (.imm (-2)), .alu .xor .rdx (.imm 2)]) s
    (fun t => t.gpr .rdx =
      ((s.mem q).setWidth 64 &&& BitVec.signExtend 64 (-2 : BitVec 32)) ^^^
        BitVec.signExtend 64 (2 : BitVec 32) ∧
      t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem q).setWidth 64) ∧
      KeepRegs [.rdx] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.map_some, Option.bind_some, State.load8, State.store64, ea_base, hq, hin,
      ea_sc, hs.rdi, st_sc hs hD, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      RegUpd.wr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmpOne_ok s₁) fun s₂ ⟨cf₂, k₂⟩ => ?_
  refine WP.mono (sbbRdx_ok s₂ cf₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  obtain m₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e₃, e₁]
    simp only [mask, tag_key, decide_eq_true_eq]
  · rw [m₃, m₁, word_writeW_self]
  · exact (k₁.trans ((Keeps.regs k₂).mono (by simp))).trans (Keeps.regs k₃)
  · rw [m₃, m₁]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (R2P BP)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (Impl.EcKey.Compressed.X86_64.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.X86_64.Cfg.checkLtP c (c.sl E)))) := by
  simp only [Impl.EcKey.Compressed.X86_64.decompressPeer, Impl.Ecdh.X86_64.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem decompressPeer_ok {c : Cfg} (hc : BaseCfgOk c) {base q : Addr} {s : State}
    (hs : Scr s base size) (hq : s.gpr .r9 = q)
    (hin : (⟨q, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q, c.C.len + 1⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : word s.mem base (c.sl FLAG) = BitVec.allOnes 64) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.decompressPeer c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.rax, .rdx] s s' ∧
      Unch base (slW c [R2P, BP, D, FLAG]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      word s'.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      word s'.mem base (c.sl FLAG) = mask ((s.mem q = 2 ∨ s.mem q = 3) ∧ sv c base s E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  obtain hR := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  rw [decompressPeer_eq, WP.block_append_iff]
  refine WP.mono (setConst_ok hs hR (Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])) hc.p_lt))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])) hc.p_lt)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) hR).trans (O₂.mono (Nat.zero_le _) hB)
  obtain q₂ : s₂.mem q = s.mem q := by
    obtain h := keep_of_disjoint' W₂ hd (by omega_using [hn]) (i := 0) (by omega_using []) (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using h
  rw [WP.block_append_iff]
  refine WP.mono (decompressTag_ok (c := c) (q := q) hs₂
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hq])
    (by
      exact ⟨_, by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin, by
        simpa using Offset.contains_base q (d := 0) (n := 1)
          (by omega_using [] : 0 + 1 ≤ c.C.len + 1) (by decide)⟩) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, tag₃, k₃, O₃⟩ => ?_
  rw [q₂] at mask₃ tag₃
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain U₃ : Unch base (slW c [R2P, BP, D]) s.mem s₃.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (by omega_using [h0]) O₃)
  obtain flag₃ : word s₃.mem base (c.sl FLAG) = BitVec.allOnes 64 := by
    rw [U₃.word (fun w hw => by have := apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, D]) w hw; omega_using [h0, this])
      (by omega_using [h0, hn, hF]), hf]
  rw [WP.block_append_iff]
  refine WP.mono (andFlag_ok' c hs₃ (by omega_using [h0, hF])) fun s₄ ⟨flag₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain U₄ : Unch base (slW c [R2P, BP, D, FLAG]) s.mem s₄.mem :=
    unch_same (U₃.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi)))
      (slot_frame (by simp) (by omega_using [h0]) O₄)
  have keep₄ {i : Nat} (hi : i < 45) (hm : i ∉ [R2P, BP, D, FLAG]) :
      sv c base s₄ i = sv c base s i := sv_unch U₄ h7 hn hi (apart_slW hm)
  refine WP.mono (checkLtP_ok c hs₄ h0 hE hM (by omega_using [h0, hF])) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans (k₃.mono (by simp))).trans
      (k₄.mono (by simp))).trans k₅
  · exact unch_same U₄ (slot_frame (by simp) (by omega_using [h0]) O₅)
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide)]
    exact e₂
  · rw [O₅.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [h0, hn, hD]),
      O₄.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [h0, hn, hD])]
    exact tag₃
  · rw [flag₅, flag₄, flag₃, mask₃, BitVec.allOnes_and,
      show wordsVal s₄.mem base (c.sl E) c.n = sv c base s₄ E from rfl,
      show wordsVal s₄.mem base (c.sl MP) c.n = sv c base s₄ MP from rfl,
      keep₄ (by decide) (by decide), keep₄ (by decide) (by decide), hmp, mask_and]

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! ### `EcKey.Compressed.X86_64.Check`, which only this module used -/

section

/-! # Check the recovered root's square and parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.X86_64 (QY QYM R2P W1 W2 W3)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]
abbrev checkSlots : List Nat := [QY, R2P, W2, QYM, W1, W3]

theorem checkOps_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.checkRootOps c =
    checkN.map (FOp.rename c.sl) := rfl

theorem checkN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps checkN e W3 = (e QY * e R2P) * (e QY * e R2P) - e W2 := by
  simp only [checkN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [QYM, QY, R2P, W1, W2, X, RR, DM, TT, SM, Nat.reduceEqDiff, ↓reduceIte]

theorem checkN_reads : readsOk checkN [QY, R2P, W2] = true := by decide
theorem checkN_slots : ∀ op ∈ checkN, ∀ x ∈ op.out :: op.ins, x ∈ checkSlots := by decide
theorem checkN_out : ∀ op ∈ checkN, op.out ∈ [QYM, W1, W3, TMP] := by decide

theorem raw_r2_mul {c : Cfg} (hc : BaseCfgOk c) (a : Nat) :
    toM c.C.p (2 ^ (64 * c.n)) a *
      toM c.C.p (2 ^ (64 * c.n)) (c.R * c.R % c.C.p) = Fin.ofNat c.C.p a := by
  change toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.mont c.R) = _
  rw [toM_cmont hc]
  unfold toM
  obtain hu := mul_rinv (unitMod_pow_two hc.p_odd (64 * c.n))
  change Fin.ofNat c.C.p c.R * rinv c.C.p (2 ^ (64 * c.n)) = 1 at hu
  grind

structure CheckPolyPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
    Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)

theorem checkPoly_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (Impl.Weierstrass.X86_64.fprogB c.MP'
      (Impl.EcKey.Compressed.X86_64.checkRootOps c)).inline s (CheckPolyPost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ checkSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain I : Inv c.MP' base size c.C.p (· ∈ checkSlots.map c.sl) ([QY, R2P, W2].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QY, R2P, W2], i ∈ checkSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy
      · show sv c base s R2P < _
        rw [hr2]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_arith)
      · exact hr
  rw [checkOps_eq]
  refine WP.mono (fprogB_ok hL (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_) (readsOk_rename c.sl checkN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (checkN_slots _ h₀ _ hi)
  obtain hw : c.sl W3 ∈ validAfter (checkN.map (FOp.rename c.sl)) ([QY, R2P, W2].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [checkN, FOp.rename, FOp.out]))
  obtain vt := IT.val _ hw
  rw [congrFun (runOps_rename c.sl checkN _ fun _ _ y h => sl_inj c hc.n0 h) W3, checkN_run] at vt
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr⟩, ?_, IT.lt _ hw, ?_⟩
  · apply PK.unch.mono
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, checkN_out _ h₀, by rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t W3) =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) at vt
    simpa only [hr2, raw_r2_mul hc] using vt

structure CheckRootPost (c : Cfg) (base : Addr) (P : Prop) [Decidable P] (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s'.mem
  flag : word s'.mem base (c.sl FLAG) = mask
    ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
      sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2)

theorem checkRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) {P : Prop} [Decidable P]
    (hf : word s.mem base (c.sl FLAG) = mask P) :
    WP isa (Impl.EcKey.Compressed.X86_64.checkRoot c).inline s (CheckRootPost c base P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain hW := sl_le c h7 (i := W3) (by decide)
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq
    (Impl.Weierstrass.X86_64.fprogB c.MP' (Impl.EcKey.Compressed.X86_64.checkRootOps c)).inline
    (.block (Impl.EcKey.Compressed.X86_64.checkRootChecks c))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hs hM hy hr hr2) fun s₁ I => ?_)
  obtain flag₁ : word s₁.mem base (c.sl FLAG) = mask P := by
    rw [flag_unch I.unch h7 h0 hn (by decide), hf]
  obtain hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) I.lt, I.val]
    constructor <;> intro h <;> grind
  rw [Impl.EcKey.Compressed.X86_64.checkRootChecks, WP.block_append_iff]
  refine WP.mono (checkZero_ok c I.scr h0 hW (by omega_arith)) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := I.scr.of_keepRegs k₂ (by decide)
  obtain flag₂ : word s₂.mem base (c.sl FLAG) = mask
      (P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) := by
    rw [f₂, flag₁, show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, mask_and]
    simp only [mask, hz]
  obtain y₂ : sv c base s₂ QY = sv c base s QY := by
    rw [sv, sv_flag O₂ h0 h7 hn (by decide) (by decide)]
    exact sv_unch I.unch h7 hn (by decide) (apart_slW (by decide))
  obtain tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) := by
    rw [O₂.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_arith) (by omega_arith)]
    exact I.unch.word (fun w hw => by
      have := apart_slW (c := c) (by decide : D ∉ [QYM, W1, W3, TMP]) w hw
      omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_arith) (by omega_arith)) fun s₃ ⟨mask₃, k₃⟩ => ?_
  rw [y₂, tag₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok s₃ _ mask₃) fun s₄ ⟨mask₄, k₄⟩ => ?_
  obtain hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  refine WP.mono (andFlag_ok' c hs₄ (by omega_arith)) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_⟩
  · exact (((I.keep.trans (k₂.mono (by simp [clob]))).trans
      ((Keeps.regs k₃).mono (by simp [clob]))).trans
      ((Keeps.regs k₄).mono (by simp [clob]))).trans (k₅.mono (by simp [clob]))
  · have U₁ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s₁.mem := I.unch.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi))
    obtain U₂ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s₁.mem s₄.mem := by
      rw [k₄.2.1, k₃.2.1]
      exact slot_frame (by simp) (by omega_arith) O₂
    exact unch_same (unch_same U₁ U₂) (slot_frame (by simp) (by omega_arith) O₅)
  · rw [flag₅, k₄.2.1, k₃.2.1, flag₂, mask₄]
    simp only [not_not]
    exact mask_and _ _

end VG.Proof.EcKey.Compressed.X86_64

end

end

/-! # Decompression meets the merged API contract -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Start.lean`, which only this module imported.
section

/-! # Decode the compressed x coordinate with the existing EC setup -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

structure DecompressPre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .rsi, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .rdx, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .rsi, c.C.len + 1⟩ ⟨s.gpr .rdx, size⟩
  fit : (s.gpr .rdx).toNat + size ≤ 2 ^ 64

structure DecompressStart (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rdx) size
  fixed : Fixed c (s₀.gpr .rdx) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .rsi = s₀.gpr .rdi
  pk : s.gpr .r9 = s₀.gpr .rsi
  x : sv c (s₀.gpr .rdx) s E = keyX c s₀
  flag : word s.mem (s₀.gpr .rdx) (c.sl FLAG) = BitVec.allOnes 64
  outside : Outside (s₀.gpr .rdx) 0 size s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressStart_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressStart c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.X86_64.args)
      (.seq (.block (c.setupWith none)) rest)) s₀ Q := by
  have hsz : size = 8192 := rfl
  have := hc.len8
  have := hc.len_hi
  have := hc.n10
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8, r9, rcx, rsi, rdx, k₁⟩ => ?_)
  obtain rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.2.1, k₁.2.2.2]
  obtain hsp : SetupPre c s₁ := by
    obtain hin : ∀ e, e + 8 ≤ c.C.len →
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + 1 + BitVec.ofNat 64 e) 8 := by
      intro e he
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact ⟨_, hp.pk, Offset.contains_base _ (by omega_using [he]) (by omega_arith)⟩
    obtain hd : Region.Disjoint ⟨s₀.gpr .rsi + 1, c.C.len⟩ ⟨s₀.gpr .rdx, size⟩ :=
      hp.disjoint.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))
    exact ⟨by rw [k₁.2.2.2, r8]; exact hp.ws,
      by rw [rcx, rw₁]; exact hin, by rw [rsi, rw₁]; exact hin,
      by rw [rdx, rw₁]; exact hin, by rw [rsi, r8]; exact hd,
      by rw [rdx, r8]; exact hd, by rw [rcx, r8]; exact hd, by rw [r8]; exact hp.fit⟩
  refine WP.seq (WP.mono (setup_ok hc (hs := none) (.inl rfl) hsp) fun s₂ S => ?_)
  rw [r8] at S
  apply h s₁.gpr s₂
  refine ⟨S.scr, VG.Proof.EcKey.Validate.X86_64.setup_fixed S,
    fun r hr => k₁.1 r (by revert r; decide), S.rsi.trans (k₁.1 _ (by decide)),
    (S.keep.gpr _ (by decide)).trans r9, ?_, S.flag, ?_, ?_, ?_⟩
  · rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.2.1]
  · rw [← k₁.2.1]
    exact S.unch.outside (by simp)
  · rw [S.keep.rd, k₁.2.2.1]
  · rw [S.keep.wr, k₁.2.2.2]

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Rhs.lean`, which only this module imported.
section

/-! # The curve polynomial used by coordinate recovery -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.X86_64 (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.X86_64 (rhsOps)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64

abbrev rhsSlots : List Nat := [QXM, AP, BP, W1, W2, W3]

def rhsTail : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM,
    .add W3 W2 W1, .add W2 W3 BP]

theorem rhsOps_eq (c : Cfg) : rhsOps c =
    .mul (c.sl QXM) (c.sl E) (c.sl R2P) :: rhsTail.map (FOp.rename c.sl) := rfl

theorem rhsTail_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsTail e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsTail, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsTail_reads : readsOk rhsTail [QXM, AP, BP] = true := by decide
theorem rhsTail_slots : ∀ op ∈ rhsTail, ∀ x ∈ op.out :: op.ins, x ∈ rhsSlots := by decide
theorem rhsTail_out : ∀ op ∈ rhsTail, op.out ∈ [W1, W2, W3, TMP] := by decide

structure RhsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.X86_64.fprogB c.MP' (rhsOps c)).inline s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [rhsOps_eq, fprogB_cons_iff]
  refine WP.mono (slMulP_ok h7 hs hM (o := QXM) (a := E) (b := R2P) (by decide) (by decide)
    (by decide) (by decide) (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  obtain a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  obtain b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  obtain hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QXM, AP, BP], i ∈ rhsSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt₁
      · show sv c base s₁ AP < _
        rw [a₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
      · show sv c base s₁ BP < _
        rw [b₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
  refine WP.mono (fprogB_ok hL hpR _ I (fun op hop x hx => ?_)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  obtain hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  obtain v₂ := I₂.val _ hw
  rw [congrFun (runOps_rename c.sl rhsTail _ fun _ _ y h => sl_inj c hc.n0 h) W2, rhsTail_run] at v₂
  obtain U₁ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  obtain U₂ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s₁.mem s₂.mem := PK.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, List.mem_cons_of_mem _ (rhsTail_out op₀ h₀), by
        rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  refine ⟨PK.scr hs₁, I₂.mod, fun r hr => (PK.gpr r hr).trans (k₁.gpr r hr),
    PK.rd.trans k₁.rd, PK.wr.trans k₁.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DecompressFront.lean`, which only this module imported.
section

/-! # Prepare the polynomial and retain the compressed input's checks -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (R2P BP QXM W1 W2 W3)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (s.gpr .rsi) = 2 ∨ s.mem (s.gpr .rsi) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rdx) size
  fixed : Fixed c (s₀.gpr .rdx) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .rsi = s₀.gpr .rdi
  x : sv c (s₀.gpr .rdx) s E = keyX c s₀
  tag : word s.mem (s₀.gpr .rdx) (c.sl D) = (s₀.mem (s₀.gpr .rsi)).setWidth 64
  r2 : sv c (s₀.gpr .rdx) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (s₀.gpr .rdx) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : word s.mem (s₀.gpr .rdx) (c.sl FLAG) = mask (CompressedPrefix c s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Keep the input checks while a field-arithmetic phase writes other slots. -/
theorem DecompressFront.frame {c : Cfg} (hc : BaseCfgOk c) {s₀ s t : State}
    {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s)
    (K : KeepRegs (powClob c.n) s t) {W : List (Nat × Nat)}
    (U : Unch (s₀.gpr .rdx) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ g t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (s₀.gpr .rdx) t i = sv c (s₀.gpr .rdx) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      word t.mem (s₀.gpr .rdx) (c.sl i) = word s.mem (s₀.gpr .rdx) (c.sl i) :=
    U.word (fun w hw => by have := ha i hm w hw; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, h0, this])
  refine ⟨F.scr.of_keepRegs K (rdi_not_powClob _), F.fixed.unch h7 hn hW U, F.original,
    (K.gpr _ (rsi_not_powClob _)).trans F.out,
    (e (by decide) (by simp)).trans F.x, (ew (by decide) (by simp)).trans F.tag,
    (e (by decide) (by simp)).trans F.r2, ?_, ?_, (ew (by decide) (by simp)).trans F.flag,
    K.rd.trans F.rd, K.wr.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs

theorem decompressFront_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressFront c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.X86_64.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.EcKey.Compressed.X86_64.decompressPeer c))
      (.seq (Impl.Weierstrass.X86_64.fprogB c.MP'
        (Impl.EcKey.Compressed.X86_64.rhsOps c)).inline rest)))) s₀ Q := by
  apply decompressStart_ok hc hp
  intro g s S
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := S.scr.nowrap
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr S.pk
    (by rw [S.rd, S.wr]; exact hp.pk) hp.disjoint S.fixed.mp S.flag)
    fun s₁ ⟨hs₁, k₁, U₁, r2₁, bp₁, tag₁, flag₁⟩ => ?_)
  obtain F₁ := S.fixed.unch h7 hn (fixedOk_slW (l := [R2P, BP, D, FLAG]) (by decide)) U₁
  obtain x₁ : sv c (s₀.gpr .rdx) s₁ E = keyX c s₀ :=
    (sv_unch U₁ h7 hn (by decide) (apart_slW (by decide))).trans S.x
  obtain lead : s.mem (s₀.gpr .rsi) = s₀.mem (s₀.gpr .rsi) := by
    obtain e := keep_of_disjoint' S.outside hp.disjoint (by omega_using [hn]) (i := 0) (by omega_using [])
      (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using e
  rw [lead, S.x] at flag₁
  rw [lead] at tag₁
  refine WP.seq (WP.mono (rhs_ok hc hs₁ (modP_of hc F₁.mp) r2₁ F₁.ap bp₁) fun s₂ R => ?_)
  obtain F₂ := F₁.unch h7 hn (fixedOk_slW (l := [QXM, W1, W2, W3, TMP]) (by decide)) R.unch
  have eq₂ {i : Nat} (hi : i < 45) (hw : i ∉ [QXM, W1, W2, W3, TMP]) :
      sv c (s₀.gpr .rdx) s₂ i = sv c (s₀.gpr .rdx) s₁ i :=
    sv_unch R.unch h7 hn hi (apart_slW hw)
  apply h g s₂
  refine ⟨R.scr, F₂, S.original, ?_, (eq₂ (by decide) (by decide)).trans x₁,
    ?_, (eq₂ (by decide) (by decide)).trans r2₁, R.lt, ?_, ?_, ?_, ?_⟩
  · rw [R.gpr _ (rsi_not_clob _), k₁.gpr _ (by decide), S.out]
  · exact (R.unch.word (fun w hw => by
      have := apart_slW (c := c) (by decide : D ∉ [QXM, W1, W2, W3, TMP]) w hw
      have := hc.n0
      omega_arith) (by have := sl_le c h7 (i := D) (by decide); omega_using [h0, hn, this])).trans tag₁
  · simpa only [x₁] using R.val
  · rw [flag_unch R.unch h7 hc.n0 hn (by decide), flag₁]
  · rw [R.rd, k₁.rd, S.rd]
  · rw [R.wr, k₁.wr, S.wr]

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Select.lean`, which only this module imported.
section

/-! # Leave Montgomery form and choose between the two canonical roots -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (QY W0)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (word s.mem base (c.sl D)).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.X86_64.selectRoot c).inline s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hZ := sl_le c h7 (i := ZERO) (by decide)
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (opProg c.MP' (.mul (c.sl QY) (c.sl ACC) (c.sl ONE))).inline
    (.block (opCode c.MP' (.sub (c.sl W0) (c.sl ZERO) (c.sl QY)) ++
      Impl.EcKey.Compressed.X86_64.parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0)))) s _
  refine WP.seq (WP.mono (slMulP_ok h7 hs hM (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by decide) (by rw [hOne]; omega_using [hp3]))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  obtain normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  obtain zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  obtain ha := slots_apart (MP'_n c) (MP'_tmp c) (MP'_mo c)
    (o := W0) (a := ZERO) (b := QY) (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₁ hM₁ hW hZ hY ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
    (by change sv c base s₁ ZERO < c.C.p; rw [zero₁]; omega_using [hp3])
    lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  obtain hs₂ := k₂.scr hs₁
  obtain hM₂ := hM₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  obtain negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega_using [hp3])
  obtain negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  obtain U₁₂ : Unch base (slW c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  obtain tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) :=
    U₁₂.word (fun w hw => by
      have := apart_slW (c := c) (by decide : D ∉ [QY, W0, TMP]) w hw
      omega_using [h0, this]) (by have := hs.nowrap; omega_using [h0, hn, hD])
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega_using [h0, hY]) (by omega_using [h0, hD])) fun s₃ ⟨mask₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2)) c.n hs₃
    (by simpa only [mask, decide_eq_true_eq] using mask₃)
    hY hY hW (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega_using [this])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain hM₄ : ModOkW c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega_using [hn, hMP]), k₃.2.1]
    exact hM₂.val)
  obtain e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, k₃.2.1, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hra : r ≠ .rax := fun h => hr (h ▸ by simp [clob])
      obtain hrd : r ≠ .rdx := fun h => hr (h ▸ by simp [clob])
      obtain hrc : r ≠ .rcx := fun h => hr (h ▸ by simp [clob])
      rw [k₄.gpr _ (by simp [hra, hrd]), k₃.1 _ (by simp [hrd, hrc]), k₂.gpr _ hr, k₁.gpr _ hr]
    · rw [k₄.rd, k₃.2.2.1, k₂.rd, k₁.rd]
    · rw [k₄.wr, k₃.2.2.2, k₂.wr, k₁.wr]
  · apply unch_same U₁₂
    rw [← k₃.2.1]
    exact slot_frame (by simp) (Nat.le_refl _) O₄
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DecompressMiddle.lean`, which only this module imported.
section

/-! # Coordinate recovery and final checks preserve the parsed encoding -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (s.gpr .rsi)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (s.gpr .rsi)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rdx) size
  saved : Spill.Saved s.mem (s₀.gpr .rdx) g Cfg.saved
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .rsi = s₀.gpr .rdi
  x : sv c (s₀.gpr .rdx) s E = keyX c s₀
  y : sv c (s₀.gpr .rdx) s QY = (keyRoot c root s₀).val
  flag : word s.mem (s₀.gpr .rdx) (c.sl FLAG) = mask (CompressedAccept c root s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : BaseCfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s) :
    WP isa (.seq (Impl.EcKey.Compressed.X86_64.rootCandidate c).inline
      (.seq (Impl.EcKey.Compressed.X86_64.selectRoot c).inline
        (Impl.EcKey.Compressed.X86_64.checkRoot c).inline)) s (DecompressChecked c root s₀ g) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  obtain F₁ := F.frame hc C.keep C.unch (candidate_fixed c) (by
    intro i hi
    obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ candidateSlots := by decide
    exact candidate_apart (h i hi).1 (h i hi).2)
  obtain root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  obtain F₂ := F₁.frame hc (S.keep.mono (fun _ hr => List.mem_cons_of_mem _ hr)) S.unch
    (fixedOk_slW (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      obtain h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slW (h i hi))
  obtain y₂ : Fin.ofNat c.C.p (sv c (s₀.gpr .rdx) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (s₀.gpr .rsi)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  obtain yval₂ : sv c (s₀.gpr .rdx) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  obtain F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slW (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (s₀.gpr .rdx) s₃ i = sv c (s₀.gpr .rdx) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slW hw)
  refine ⟨K.scr, F₃.saved, F.original, (K.keep.gpr _ (rsi_not_clob _)).trans F₂.out,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, K.keep.rd.trans F₂.rd, K.keep.wr.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (s₀.gpr .rsi)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  obtain hb : Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (c.C.len + 1) =
      s.mem (s.gpr .rsi) :: Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : BaseCfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (hi : (Impl.EcKey.Compressed.X86_64.decompress c).InlineOk = true)
    (hmx : (Impl.EcKey.Compressed.X86_64.decompress c).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86_64.decompress c).inline s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hro, hrw, hfit, hwfit⟩ := hs
  obtain hp : DecompressPre c s :=
    ⟨by rw [hrd]; simp, by rw [hwr]; simp, hpw, hwfit⟩
  obtain hrun : WP isa (Impl.EcKey.Compressed.X86_64.decompress c).inline s fun s' =>
      (decompressContract c.C root).post s s' ∧ ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r := by
    apply decompressFront_ok hc hp
    intro g t F
    refine WP.seq (WP.mono (decompressMiddle_ok hc hroot F) fun u U => ?_)
    refine WP.mono (decompressFinish_ok hc U.scr U.out
      (by rw [U.wr, hwr, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega_using []]; simp)
      (by simpa only [Nat.add_comm] using how)
      (by omega_using [hfit]) U.saved
      (decide (CompressedAccept c root s)) (by simp only [U.flag, mask, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave, _⟩ => ?_
    refine ⟨?_, fun r hr => (hsave r hr).trans (U.original r hr)⟩
    dsimp only [decompressContract]
    rw [decompress_key]
    rw [U.x, U.y] at hout
    change Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (1 + 2 * c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at hret hout ⊢
      refine ⟨hret, ?_⟩
      change Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using hout
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
  obtain ⟨t, s', he, hpost, hsave⟩ := hrun
  obtain F := (Exec.regions he (Code.noCalls_inline hi)).2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; exact hmx) he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact Exec.gpr (Code.clobbers_rsp_of_inlineOk hi) he
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrw) (by decide)

end VG.Proof.EcKey.Compressed.X86_64
