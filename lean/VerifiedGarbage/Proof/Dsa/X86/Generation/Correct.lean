module

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Search
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Dsa.X86.Generation.Q
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Dsa.X86.Generation.Finish`, which this module and modules that import it used -/

section

/-! # The result: `out`, `used` and `state`, and the status

`out` gets p||q||g for parameters, else zeros; `used` the octets consumed;
`state[0]` the seeds left and `state[3]` the next tape's length
(`VG.Proof.Dsa.Generation.requested`), each with its high half zero; and the
status is the protocol's (`Entropy.Outcome.status`) for the controller's end
(`cRes`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.Dsa.Generation

/-- What `out` holds for the controller's end. -/
def outBytes (g : Geo) : COut → List Byte
  | .found a _ => Spec.Dsa.encodeParams g.pLen g.qLen a
  | _ => List.replicate (2 * g.pLen + g.qLen) 0

/-- `fStatus` for the controller's end. -/
def stOf : COut → Nat
  | .found .. => 1
  | .noSeeds _ => 3
  | .ranOut .. => 2

theorem SRes.status {E : Env} {g : Geo} {m : Mem} {o : COut} (h : SRes E g m o) :
    m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 (stOf o) := by
  rcases o with _ | _ | _
  · exact h.1
  · exact h.1
  · exact h.1

/-- A 64-bit word, from its two 32-bit halves. -/
theorem readW64_halves (m : Mem) (a : Addr) :
    m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, ← VG.Proof.Rc2.Word32.readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega_using [hi]]; congr 1; omega_arith

theorem zero_half {x : Nat} (hx : x < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 x = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega_using [hx])]

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (show (x - a).toNat + 1 ≤ n by omega_using [h₁]) (show (x - b).toNat + 1 ≤ k by omega_using [h₂])

theorem wide_narrow {P : Addr} (h : P.toNat < 2 ^ 32) : (P.setWidth 32).setWidth 64 = P := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [])]

/-! ## `out` -/

/-- p||q||g to `out` for parameters, else zeros. -/
theorem outPart_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {o : COut} (hR : SRes E g s.mem o) :
    WP isa g.outPart s fun t => Spec.Rsa.bytesAt t.mem E.out (2 * g.pLen + g.qLen) = outBytes g o ∧
      Frame [E.outRegion] s.mem t.mem ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have of := v.outFit
  have op := v.outPtr
  obtain oL : E.outLen = 2 * g.pLen + g.qLen := by simp only [Env.outLen, hp, hq]
  obtain outW : (E.out.setWidth 32).setWidth 64 = E.out := wide_narrow op
  obtain outN : (E.out.setWidth 32).toNat = E.out.toNat := by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt op]
  obtain lenN : 2 * g.pLen + g.qLen < 2 ^ 32 := by omega_using [bd]
  unfold Geo.outPart
  simp only [seqs]
  refine WP.seq (cmpF_end B.scr (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega_using [sz]) hR.status
    (by rcases o with _ | _ | _ <;> simp [stOf]) (by decide) fun t₁ g₁ m₁ rd₁ wr₁ sy₁ z₁ => ?_)
  obtain hs₁ : Scr t₁ E.base E.size := Scr.of_eq B.scr (g₁ _ (by decide)) (g₁ _ (by decide)) wr₁
  refine WP.ite _ z₁ (fun h1 => ?_) (fun h1 => ?_)
  · -- p||q||g out.
    obtain ⟨a, u, rfl⟩ : ∃ a u, o = .found a u := by
      rcases o with ⟨a, u⟩ | _ | _
      · exact ⟨a, u, rfl⟩
      · simp [stOf] at h1
      · simp [stOf] at h1
    simp only [List.cons_append, List.nil_append]
    refine WP.seq (ld_ok hs₁ (r := .ebx) (d := fOut) (by simp only [fOut, hdr]; omega_using [sz]) fun t₂ u₂ =>
      scr_ok fun t₃ e₃ g₃ m₃ rd₃ wr₃ sy₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_)
    obtain ebx₄ : t₄.gpr .ebx = E.out.setWidth 32 := by
      rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.gpr, m₁, B.outW]
    obtain esi₄ : t₄.gpr .esi = s.gpr .edi + BitVec.ofNat 32 sPk := by
      rw [u₄.other _ (by decide), e₃, u₂.other _ (by decide), g₁ _ (by decide)]
    obtain m₄ : t₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
    obtain rd₄ : t₄.rd = s.rd := by rw [u₄.rd, rd₃, u₂.rd, rd₁]
    obtain wr₄ : t₄.wr = s.wr := by rw [u₄.wr, wr₃, u₂.wr, wr₁]
    have hs := B.scr
    obtain pW := Scr.wide hs (d := sPk) (by simp only [sPk]; omega_using [sz])
    obtain pN := Scr.toNat_add hs (d := sPk) (by simp only [sPk]; omega_using [sz])
    refine VG.X86.WP.mono_syms (VG.Proof.Bignum.X86.copyBuffers_ok (src := s.gpr .edi + BitVec.ofNat 32 sPk)
      (dst := E.out.setWidth 32) (n := 2 * g.pLen + g.qLen) (by omega_using [bd]) lenN (by rw [pN]; simp only [sPk]; omega_using [sz, bd, nw])
      (by rw [outN]; simp only [Env.outLen, hp, hq] at of; omega_using [of])
      (by rw [VG.Proof.Bignum.X86.byteAddr, pW, rd₄, wr₄]; exact hs.read (by simp only [sPk]; omega_using [sz, bd]))
      (by rw [VG.Proof.Bignum.X86.byteAddr, outW, wr₄]
          exact ⟨_, B.out, by simp only [Env.outRegion, oL]; exact contains_start _ (Nat.le_refl _)⟩)
      (by rw [VG.Proof.Bignum.X86.byteAddr, pW, VG.Proof.Bignum.X86.byteAddr, outW]
          exact (v.outScratch.symm.sub_left (Offset.sub_base _ (by simp only [sPk]; omega_using [sz, bd]))).sub_right
            (by intro x hx; simp only [Env.outRegion, oL]; exact hx))
      esi₄ ebx₄ u₄.gpr) fun t₅ ⟨R₅, _, _, F₅, K₅⟩ sy₅ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [VG.Proof.Bignum.X86.byteAddr, outW, pW, m₄] at R₅
      rw [bytesAt_of_read R₅]; exact hR.2.1
    · simp only [VG.Proof.Bignum.X86.byteAddr, outW, m₄] at F₅
      intro x hx; exact F₅ x fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hx E.outRegion (List.mem_singleton_self _) |> fun h => by simpa [Env.outRegion, oL] using h
    · rw [K₅.1 _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]
    · rw [K₅.1 _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]
    · rw [K₅.2.1, rd₄]
    · rw [K₅.2.2, wr₄]
    · rw [sy₅, u₄.syms, sy₃, u₂.syms, sy₁]
  · -- Zeros out.
    obtain hn : outBytes g o = List.replicate (2 * g.pLen + g.qLen) 0 := by
      rcases o with _ | _ | _
      · simp [stOf] at h1
      · rfl
      · rfl
    rw [hn]
    refine WP.seq (ld_ok hs₁ (r := .esi) (d := fOut) (by simp only [fOut, hdr]; omega_using [sz]) fun t₂ u₂ =>
      wp_movi fun t₃ u₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_)
    refine VG.X86.WP.mono_syms (VG.Proof.Dsa.X86.failureLoop_ok (out := E.out.setWidth 32)
      (len := 2 * g.pLen + g.qLen) (by omega_using [bd]) lenN (by rw [outN]; simp only [Env.outLen, hp, hq] at of; omega_using [of])
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁, B.outW])
      (by rw [u₄.other _ (by decide), u₃.gpr]) u₄.gpr (fun i hi => by
        rw [u₄.wr, u₃.wr, u₂.wr, wr₁, outW]
        exact ⟨_, B.out, by simp only [Env.outRegion, oL]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [bd, hi])⟩))
      fun t₅ ⟨V₅, _, O₅, K₅⟩ sy₅ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [outW] at V₅; exact V₅
    · rw [outW] at O₅
      intro x hx
      obtain hc := hx E.outRegion (List.mem_singleton_self _)
      have := O₅ x (.inr (by
        simp only [Region.Contains, Env.outRegion, oL] at hc
        show 0 + (2 * g.pLen + g.qLen) ≤ (x - E.out).toNat
        omega_using [hc]))
      rw [this, u₄.mem, u₃.mem, u₂.mem, m₁]
    · rw [K₅.1 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide)]
    · rw [K₅.1 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide)]
    · rw [K₅.2.1, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [K₅.2.2, u₄.wr, u₃.wr, u₂.wr, wr₁]
    · rw [sy₅, u₄.syms, u₃.syms, u₂.syms, sy₁]

/-! ## `used` and `state` -/

section
variable {is : List Instr} {Q : State → Prop}

/-- `[ebx + d] := r`, with `ebx` the pointer `P` into the writable region `R`. -/
theorem stB_ok {s : State} {P : Addr} {R : Region} {d : Nat} {r : Reg} (hb : s.gpr .ebx = P.setWidth 32)
    (hP : P.toNat + d + 4 ≤ 2 ^ 32) (hR : R ∈ s.wr) (hc : R.Contains (P + BitVec.ofNat 64 d) 4)
    (k : ∀ t, Mupd s t (s.mem.writeW (P + BitVec.ofNat 64 d) (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (.store (at_ .ebx d) r :: is)) s Q := by
  obtain hP32 : P.toNat < 2 ^ 32 := by omega_using [hP]
  refine wp_storeS (a := P + BitVec.ofNat 64 d) ?_ ⟨R, hR, hc⟩ k
  show addr (s.gpr .ebx) d = _
  rw [hb, addr_eq (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hP32]; omega_using [hP]), wide_narrow hP32]

end

/-- The words of `state` and `used`: `state[0]` := `edx`, `state[3]` := `ecx`,
`used` := the word at `u`, each with its high half zero; `state[1]` and
`state[2]` as they were; and `eax` := `val`. -/
theorem results_ok {E : Env} (v : E.Valid) {s : State} (B : Base E s) {u val k r w : Nat}
    (hu₂ : u + 4 ≤ sState) (hw : s.mem.readW (off E.base u) 32 = BitVec.ofNat 32 w)
    (hk : s.gpr .edx = BitVec.ofNat 32 k) (hr : s.gpr .ecx = BitVec.ofNat 32 r) (hkl : k < 2 ^ 32)
    (hrl : r < 2 ^ 32) (hwl : w < 2 ^ 32) :
    WP isa (Geo.results u val) s fun t =>
      t.mem.readW (E.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 k ∧
      t.mem.readW (E.stP + BitVec.ofNat 64 8) 64 = s.mem.readW (E.stP + BitVec.ofNat 64 8) 64 ∧
      t.mem.readW (E.stP + BitVec.ofNat 64 16) 64 = s.mem.readW (E.stP + BitVec.ofNat 64 16) 64 ∧
      t.mem.readW (E.stP + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 r ∧
      t.mem.readW (E.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 w ∧
      Frame [E.stRegion, E.usedRegion] s.mem t.mem ∧ t.gpr .eax = BitVec.ofNat 32 val ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have sz := v.size_ge
  have sf := v.stFit
  have uf := v.usedFit
  have nw := v.scratchFit
  obtain SU : E.stRegion.Disjoint E.usedRegion := (v.usedFar _ (by simp)).symm
  obtain sepSt : ∀ d n e, d + n ≤ 32 → e + 4 ≤ 32 → (d + n ≤ e ∨ e + 4 ≤ d) →
      Mem.Sep (E.stP + BitVec.ofNat 64 d) n (E.stP + BitVec.ofNat 64 e) 4 :=
    fun d n e h₁ h₂ h => Offset.sep _ h (by omega_using [h₁]) (by omega_using [h₂])
  obtain sepSU : ∀ d n e, d + n ≤ 32 → e + 4 ≤ 8 →
      Mem.Sep (E.stP + BitVec.ofNat 64 d) n (E.usedP + BitVec.ofNat 64 e) 4 := fun d n e h₁ h₂ =>
    sep_of_disjoint ((SU.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂))
  obtain sepU : ∀ d e, d + 4 ≤ 8 → e + 4 ≤ 8 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      Mem.Sep (E.usedP + BitVec.ofNat 64 d) 4 (E.usedP + BitVec.ofNat 64 e) 4 :=
    fun d e h₁ h₂ h => Offset.sep _ h (by omega_using [h₁]) (by omega_using [h₂])
  obtain sepUS : ∀ d e, d + 4 ≤ 8 → e + 4 ≤ 32 →
      Mem.Sep (E.usedP + BitVec.ofNat 64 d) 4 (E.stP + BitVec.ofNat 64 e) 4 := fun d e h₁ h₂ =>
    sep_of_disjoint ((SU.symm.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂))
  obtain cS : ∀ d, d + 4 ≤ 32 → E.stRegion.Contains (E.stP + BitVec.ofNat 64 d) 4 :=
    fun d h => Offset.contains_base _ h (by omega_using [h])
  obtain cU : ∀ d, d + 4 ≤ 8 → E.usedRegion.Contains (E.usedP + BitVec.ofNat 64 d) 4 :=
    fun d h => Offset.contains_base _ h (by omega_using [h])
  unfold Geo.results
  simp only [seqs]
  refine WP.seq (ld_ok B.scr (r := .ebx) (d := fStP) (by simp only [fStP, hdr]; omega_using [sz]) fun t₁ u₁ =>
    WP.block_nil ?_)
  obtain b₁ : t₁.gpr .ebx = E.stP.setWidth 32 := by rw [u₁.gpr, B.stPW]
  refine WP.seq (stB_ok (P := E.stP) (d := 0) b₁ (by omega_using [sf]) (by rw [u₁.wr]; exact B.stW) (cS 0 (by omega_using []))
    fun t₂ M₂ => ?_)
  refine stB_ok (P := E.stP) (d := 24) (by rw [M₂.gpr]; exact b₁) (by omega_using [sf]) (by rw [M₂.wr, u₁.wr]; exact B.stW)
    (cS 24 (by omega_using [])) fun t₃ M₃ => wp_movi fun t₄ u₄ => ?_
  obtain b₄ : t₄.gpr .ebx = E.stP.setWidth 32 := by rw [u₄.other _ (by decide), M₃.gpr, M₂.gpr, b₁]
  refine stB_ok (P := E.stP) (d := 4) b₄ (by omega_using [sf]) (by rw [u₄.wr, M₃.wr, M₂.wr, u₁.wr]; exact B.stW)
    (cS 4 (by omega_using [])) fun t₅ M₅ => ?_
  refine stB_ok (P := E.stP) (d := 28) (by rw [M₅.gpr]; exact b₄) (by omega_using [sf])
    (by rw [M₅.wr, u₄.wr, M₃.wr, M₂.wr, u₁.wr]; exact B.stW) (cS 28 (by omega_using [])) fun t₆ M₆ => ?_
  obtain m₆ : t₆.mem = (((s.mem.writeW (E.stP + BitVec.ofNat 64 0) (BitVec.ofNat 32 k)).writeW
      (E.stP + BitVec.ofNat 64 24) (BitVec.ofNat 32 r)).writeW (E.stP + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW
      (E.stP + BitVec.ofNat 64 28) (0 : BitVec 32) := by
    simp only [M₆.mem, M₅.mem, u₄.mem, M₃.mem, M₂.mem, u₁.mem, M₅.gpr, u₄.gpr, M₂.gpr]
    rw [u₁.other .edx (by decide), u₁.other .ecx (by decide), hk, hr]
  obtain F₆ : Frame [E.stRegion, E.usedRegion] s.mem t₆.mem := by
    rw [m₆]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cS 0 (by omega_using []))).writeW List.mem_cons_self _
      (cS 24 (by omega_using []))).writeW List.mem_cons_self _ (cS 4 (by omega_using []))).writeW List.mem_cons_self _
      (cS 28 (by omega_using []))
  obtain hs₆ : Scr t₆ E.base E.size := Scr.of_eq B.scr (by rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr,
    M₂.gpr, u₁.other _ (by decide)]) (by rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr, M₂.gpr,
    u₁.other _ (by decide)]) (by rw [M₆.wr, M₅.wr, u₄.wr, M₃.wr, M₂.wr, u₁.wr])
  obtain scrApart : ∀ d, d + 4 ≤ E.size → ∀ r' ∈ [E.stRegion, E.usedRegion],
      (⟨off E.base d, 4⟩ : Region).Disjoint r' := fun d h r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ((v.stFar _ List.mem_cons_self).symm).sub_left (Offset.sub_base _ h)
    · exact ((v.usedFar _ List.mem_cons_self).symm).sub_left (Offset.sub_base _ h)
  refine ld_ok hs₆ (r := .ebx) (d := fUsedP) (by simp only [fUsedP, hdr]; omega_using [sz]) fun t₇ u₇ => WP.block_nil ?_
  obtain b₇ : t₇.gpr .ebx = E.usedP.setWidth 32 := by
    rw [u₇.gpr, F₆.readW (r := ⟨off E.base fUsedP, 4⟩) (Region.contains_self _ _)
      (scrApart _ (by simp only [fUsedP, hdr]; omega_using [sz])) (by decide), B.usedPW]
  obtain wr₇ : t₇.wr = s.wr := by rw [u₇.wr, M₆.wr, M₅.wr, u₄.wr, M₃.wr, M₂.wr, u₁.wr]
  refine stB_ok (P := E.usedP) (d := 4) b₇ (by omega_using [uf]) (by rw [wr₇]; exact B.usedW) (cU 4 (by omega_using []))
    fun t₈ M₈ => ?_
  obtain hs₈ : Scr t₈ E.base E.size := Scr.of_eq hs₆ (by rw [M₈.gpr, u₇.other _ (by decide)])
    (by rw [M₈.gpr, u₇.other _ (by decide)]) (by rw [M₈.wr, u₇.wr])
  have eax₄ : t₄.gpr .eax = 0 := u₄.gpr
  obtain m₈ : t₈.mem = t₆.mem.writeW (E.usedP + BitVec.ofNat 64 4) (0 : BitVec 32) := by
    rw [M₈.mem, u₇.mem, u₇.other .eax (by decide), M₆.gpr, M₅.gpr, eax₄]
  obtain F₈ : Frame [E.stRegion, E.usedRegion] s.mem t₈.mem := by
    rw [m₈]
    exact F₆.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (cU 4 (by omega_using []))
  refine ld_ok hs₈ (r := .eax) (d := u) (by simp only [sState] at hu₂; omega_using [hu₂, sz]) fun t₉ u₉ => ?_
  obtain eax₉ : t₉.gpr .eax = BitVec.ofNat 32 w := by
    rw [u₉.gpr, F₈.readW (r := ⟨off E.base u, 4⟩) (Region.contains_self _ _)
      (scrApart _ (by simp only [sState] at hu₂; omega_using [hu₂, sz])) (by decide), hw]
  refine stB_ok (P := E.usedP) (d := 0) (by rw [u₉.other _ (by decide), M₈.gpr]; exact b₇) (by omega_using [uf])
    (by rw [u₉.wr, M₈.wr, wr₇]; exact B.usedW) (cU 0 (by omega_using [])) fun t₁₀ M₁₀ => wp_movi fun t₁₁ u₁₁ =>
      WP.block_nil ?_
  obtain m₁₁' : t₁₁.mem = t₈.mem.writeW (E.usedP + BitVec.ofNat 64 0) (BitVec.ofNat 32 w) := by
    rw [u₁₁.mem, M₁₀.mem, u₉.mem, eax₉]
  obtain m₁₁ : t₁₁.mem = (t₆.mem.writeW (E.usedP + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW
      (E.usedP + BitVec.ofNat 64 0) (BitVec.ofNat 32 w) := by
    rw [m₁₁', m₈]
  obtain F : Frame [E.stRegion, E.usedRegion] s.mem t₁₁.mem := by
    rw [m₁₁']
    exact F₈.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (cU 0 (by omega_using []))
  obtain rU : ∀ (m : Mem) d, d + 8 ≤ 32 → ((m.writeW (E.usedP + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW
      (E.usedP + BitVec.ofNat 64 0) (BitVec.ofNat 32 w)).readW (E.stP + BitVec.ofNat 64 d) 64 =
      m.readW (E.stP + BitVec.ofNat 64 d) 64 := fun m d h => by
    rw [Mem.readW_writeW_sep (sepSU d 8 0 h (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSU d 8 4 h (by omega_using [])) (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, F, u₁₁.gpr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₁, rU _ 0 (by omega_using []), m₆, readW64_halves, VG.Offset.add_add,
      Mem.readW_writeW_sep (sepSt 4 4 28 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self32,
      Mem.readW_writeW_sep (sepSt 0 4 28 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 0 4 4 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 0 4 24 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self32, zero_half hkl]
  · rw [m₁₁, rU _ 8 (by omega_using []), m₆,
      Mem.readW_writeW_sep (sepSt 8 8 28 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 8 8 4 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 8 8 24 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 8 8 0 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide)]
  · rw [m₁₁, rU _ 16 (by omega_using []), m₆,
      Mem.readW_writeW_sep (sepSt 16 8 28 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 16 8 4 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 16 8 24 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 16 8 0 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide)]
  · rw [m₁₁, rU _ 24 (by omega_using []), m₆, readW64_halves, VG.Offset.add_add, Mem.readW_writeW_self32,
      Mem.readW_writeW_sep (sepSt 24 4 28 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sepSt 24 4 4 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self32, zero_half hrl]
  · rw [m₁₁, readW64_halves, VG.Offset.add_add,
      Mem.readW_writeW_sep (sepU 4 0 (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self32,
      Mem.readW_writeW_self32, zero_half hwl]
  · rw [u₁₁.other _ (by decide), M₁₀.gpr, u₉.other _ (by decide), M₈.gpr, u₇.other _ (by decide), M₆.gpr, M₅.gpr,
      u₄.other _ (by decide), M₃.gpr, M₂.gpr, u₁.other _ (by decide)]
  · rw [u₁₁.other _ (by decide), M₁₀.gpr, u₉.other _ (by decide), M₈.gpr, u₇.other _ (by decide), M₆.gpr, M₅.gpr,
      u₄.other _ (by decide), M₃.gpr, M₂.gpr, u₁.other _ (by decide)]
  · rw [u₁₁.rd, M₁₀.rd, u₉.rd, M₈.rd, u₇.rd, M₆.rd, M₅.rd, u₄.rd, M₃.rd, M₂.rd, u₁.rd]
  · rw [u₁₁.wr, M₁₀.wr, u₉.wr, M₈.wr, wr₇]
  · rw [u₁₁.syms, M₁₀.syms, u₉.syms, M₈.syms, u₇.syms, M₆.syms, M₅.syms, u₄.syms, M₃.syms, M₂.syms, u₁.syms]

/-! ## The whole result -/

/-- A frame apart from `scratch`, `rand` and the table keeps `Base`. -/
theorem Base.frame {E : Env} (v : E.Valid) {s t : State} (B : Base E s) {rs : List Region}
    (F : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, E.scratchRegion.Disjoint r ∧ E.witRegion.Disjoint r ∧ E.tableRegion.Disjoint r)
    (edi : t.gpr .edi = s.gpr .edi) (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sy : t.syms = s.syms) : Base E t := by
  have sz := v.size_ge
  have nw := v.scratchFit
  obtain word : ∀ d, d + 4 ≤ E.size → t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 := fun d h =>
    F.readW (r := ⟨off E.base d, 4⟩) (Region.contains_self _ _) (fun r hr => (hd r hr).1.sub_left
      (Offset.sub_base _ h)) (by decide)
  obtain witEq : Spec.Rsa.bytesAt t.mem E.wit E.witLen = Spec.Rsa.bytesAt s.mem E.wit E.witLen :=
    VG.Proof.RsaKeyGen.frame_bytesAt F (fun r hr => (hd r hr).2.1) (by have := v.witFit; omega_using [this])
  refine ⟨Scr.of_eq B.scr edi sp wr, sp.trans B.sp, rd ▸ B.tapes, rd ▸ B.table, wr ▸ B.out, wr ▸ B.usedW,
    wr ▸ B.stW, sy ▸ B.syms, ?_, witEq.trans B.wit, (word fOut (by simp only [fOut, hdr]; omega_using [sz])).trans B.outW,
    (word fUsedP (by simp only [fUsedP, hdr]; omega_using [sz])).trans B.usedPW,
    (word fStP (by simp only [fStP, hdr]; omega_using [sz])).trans B.stPW, (word fWit (by simp only [fWit, hdr]; omega_using [sz])).trans B.witW,
    (word fWitLen (by simp only [fWitLen, hdr]; omega_using [sz])).trans B.witLenW⟩
  intro c hc i hi
  obtain h := B.held c hc i hi
  simp only [VG.Impl.RsaKeyGen.TrialTable32.consts, List.mem_singleton] at hc
  subst hc
  rw [sy, ← h]
  simp only [B.syms]
  have := v.tableFit
  obtain len : i < 1024 := by simpa [VG.Impl.RsaKeyGen.TrialTable32.packed] using hi
  exact F.readW (r := E.tableRegion) (Offset.contains_base E.table (by omega_using [len]) (by omega_using [len]))
    (fun r hr => (hd r hr).2.2) (by decide)

/-- The controller's end is in `scratch`, which a frame apart from it keeps. -/
theorem SRes.frame {E : Env} {g : Geo} (G : GeoOk g) (v : E.Valid) {m m' : Mem} {rs : List Region}
    (F : Frame rs m m') (hd : ∀ r ∈ rs, E.scratchRegion.Disjoint r) {o : COut} (h : SRes E g m o) :
    SRes E g m' o := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  obtain word : ∀ d, d + 4 ≤ E.size → m'.readW (off E.base d) 32 = m.readW (off E.base d) 32 := fun d h =>
    F.readW (r := ⟨off E.base d, 4⟩) (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
      (Offset.sub_base _ h)) (by decide)
  rcases o with ⟨a, u⟩ | c | ⟨j, c⟩
  · refine ⟨by rw [word _ (by simp only [fStatus, hdr]; omega_using [sz])]; exact h.1, ?_,
      by rw [word _ (by simp only [fUsed, hdr]; omega_using [sz])]; exact h.2.2.1, h.2.2.2⟩
    rw [VG.Proof.RsaKeyGen.frame_bytesAt F (fun r hr => (hd r hr).sub_left (Offset.sub_base _
      (show sPk + (2 * g.pLen + g.qLen) ≤ E.size by have := v.room; simp only [sPk]; omega_using [sz, bd]))) (by omega_using [bd])]
    exact h.2.1
  · exact ⟨by rw [word _ (by simp only [fStatus, hdr]; omega_using [sz])]; exact h.1,
      by rw [word _ (by simp only [fC, hdr]; omega_using [sz])]; exact h.2.1, h.2.2⟩
  · exact ⟨by rw [word _ (by simp only [fStatus, hdr]; omega_using [sz])]; exact h.1,
      by rw [word _ (by simp only [fC, hdr]; omega_using [sz])]; exact h.2.1,
      by rw [word _ (by simp only [fSeedLeft, hdr]; omega_using [sz])]; exact h.2.2.1, h.2.2.2⟩

/-- After the result. -/
structure FPost (E : Env) (g : Geo) (o : COut) (s t : State) : Prop where
  out : Spec.Rsa.bytesAt t.mem E.out (2 * g.pLen + g.qLen) = outBytes g o
  st0 : t.mem.readW (E.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes E o).remaining
  st1 : t.mem.readW (E.stP + BitVec.ofNat 64 8) 64 = s.mem.readW (E.stP + BitVec.ofNat 64 8) 64
  st2 : t.mem.readW (E.stP + BitVec.ofNat 64 16) 64 = s.mem.readW (E.stP + BitVec.ofNat 64 16) 64
  st3 : t.mem.readW (E.stP + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (requested E.pLen (cRes E o))
  used : t.mem.readW (E.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes E o).used
  eax : t.gpr .eax = BitVec.ofNat 32 (cRes E o).status
  frame : Frame [E.outRegion, E.stRegion, E.usedRegion] s.mem t.mem
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem finish_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {o : COut} (hR : SRes E g s.mem o) : WP isa g.finish s (FPost E g o s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have wl := v.witLen32
  obtain oL : E.outLen = 2 * g.pLen + g.qLen := by simp only [Env.outLen, hp, hq]
  obtain outFar : ∀ r ∈ [E.outRegion], E.scratchRegion.Disjoint r ∧ E.witRegion.Disjoint r ∧
      E.tableRegion.Disjoint r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨v.outScratch.symm, v.witFar.2.1, v.tableFar.2.1⟩
  unfold Geo.finish
  simp only [seqs]
  refine WP.seq (WP.mono (outPart_ok G v hp hq B hR) fun t₁ ⟨O₁, F₁, edi₁, esp₁, rd₁, wr₁, sy₁⟩ => ?_)
  obtain B₁ := B.frame v F₁ outFar edi₁ esp₁ rd₁ wr₁ sy₁
  obtain R₁ := hR.frame G v F₁ fun r hr => (outFar r hr).1
  obtain stF : ∀ r ∈ [E.stRegion, E.usedRegion], E.outRegion.Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (v.stFar _ (by simp)).symm
    · exact (v.usedFar _ (by simp)).symm
  -- After the words: `out` as it was, and the frame.
  obtain fin : ∀ {t₂ t : State} (m₂ : t₂.mem = t₁.mem) (e₂ : t₂.gpr .edi = t₁.gpr .edi)
      (p₂ : t₂.gpr .esp = t₁.gpr .esp) (r₂ : t₂.rd = t₁.rd) (w₂ : t₂.wr = t₁.wr) (y₂ : t₂.syms = t₁.syms)
      (F : Frame [E.stRegion, E.usedRegion] t₂.mem t.mem) (e : t.gpr .edi = t₂.gpr .edi)
      (p : t.gpr .esp = t₂.gpr .esp) (r : t.rd = t₂.rd) (w : t.wr = t₂.wr) (y : t.syms = t₂.syms)
      (s0 : t.mem.readW (E.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes E o).remaining)
      (s1 : t.mem.readW (E.stP + BitVec.ofNat 64 8) 64 = t₂.mem.readW (E.stP + BitVec.ofNat 64 8) 64)
      (s2 : t.mem.readW (E.stP + BitVec.ofNat 64 16) 64 = t₂.mem.readW (E.stP + BitVec.ofNat 64 16) 64)
      (s3 : t.mem.readW (E.stP + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (requested E.pLen (cRes E o)))
      (u : t.mem.readW (E.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (cRes E o).used)
      (a : t.gpr .eax = BitVec.ofNat 32 (cRes E o).status), FPost E g o s t := by
    intro t₂ t m₂ e₂ p₂ r₂ w₂ y₂ F e p r w y s0 s1 s2 s3 u a
    obtain stOut : ∀ d, d + 8 ≤ 32 → t₁.mem.readW (E.stP + BitVec.ofNat 64 d) 64 =
        s.mem.readW (E.stP + BitVec.ofNat 64 d) 64 := fun d h =>
      F₁.readW (r := ⟨E.stP + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ((v.stFar _ (by simp)).sub_left (Offset.sub_base _ h))) (by decide)
    refine ⟨?_, s0, by rw [s1, m₂, stOut 8 (by omega_using [])], by rw [s2, m₂, stOut 16 (by omega_using [])], s3, u, a, ?_,
      e.trans (e₂.trans edi₁), p.trans (p₂.trans esp₁), r.trans (r₂.trans rd₁), w.trans (w₂.trans wr₁),
      y.trans (y₂.trans sy₁)⟩
    · rw [VG.Proof.RsaKeyGen.frame_bytesAt F (fun r hr => by have := stF r hr; simpa [Env.outRegion, oL] using this)
        (by omega_using [bd]), m₂]
      exact O₁
    · refine Frame.trans (Frame.mono F₁ fun r hr => by simp at hr ⊢; exact .inl hr) ?_
      rw [← m₂]
      exact Frame.mono F fun r hr => by simp at hr ⊢; exact .inr hr
  obtain stLt : ∀ o : COut, stOf o < 2 ^ 32 := fun o => by rcases o with _ | _ | _ <;> simp [stOf]
  obtain budget : g.budget < 2 ^ 32 := by simp only [Geo.budget]; omega_using [bd]
  refine WP.seq (cmpF_end B₁.scr (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega_using [sz]) R₁.status (stLt o)
    (by decide) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  obtain B₂ := B₁.regs m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  obtain e₂ : t₂.gpr .edi = t₁.gpr .edi := g₂ _ (by decide)
  obtain p₂ : t₂.gpr .esp = t₁.gpr .esp := g₂ _ (by decide)
  -- `edx`, `ecx` and then the words.
  obtain words : ∀ {t₃ : State} {u val k r w : Nat},
      t₃.mem = t₁.mem → t₃.gpr .edi = t₁.gpr .edi → t₃.gpr .esp = t₁.gpr .esp → t₃.rd = t₁.rd →
      t₃.wr = t₁.wr → t₃.syms = t₁.syms → u + 4 ≤ sState →
      t₃.mem.readW (off E.base u) 32 = BitVec.ofNat 32 w → t₃.gpr .edx = BitVec.ofNat 32 k →
      t₃.gpr .ecx = BitVec.ofNat 32 r → k < 2 ^ 32 → r < 2 ^ 32 → w < 2 ^ 32 →
      k = (cRes E o).remaining → r = requested E.pLen (cRes E o) → w = (cRes E o).used →
      val = (cRes E o).status → WP isa (Geo.results u val) t₃ (FPost E g o s) := by
    intro t₃ u val k r w m₃ e₃ p₃ r₃ w₃ y₃ hu hw hk hr hkl hrl hwl ek er ew ev
    obtain B₃ := B₁.regs m₃ e₃ p₃ r₃ w₃ y₃
    refine WP.mono (results_ok v B₃ hu hw hk hr hkl hrl hwl) fun t ⟨s0, s1, s2, s3, us, F, ea, ed, ep, r', w', y'⟩ =>
      fin m₃ e₃ p₃ r₃ w₃ y₃ F ed ep r' w' y' (by rw [s0, ek]) s1 s2 (by rw [s3, er]) (by rw [us, ew])
        (by rw [ea, ev])
  rcases o with ⟨a, u⟩ | c | ⟨j, c⟩
  · -- Parameters.
    obtain ⟨_, _, fu, hu⟩ := R₁
    refine WP.ite _ z₂ (fun _ => ?_) (fun h => by simp [stOf] at h)
    unfold Geo.accepted
    refine WP.seq (wp_movi fun t₃ u₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_)
    exact words (k := 0) (r := 0) (w := u) (by rw [u₄.mem, u₃.mem, m₂])
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), e₂]) (by rw [u₄.other _ (by decide),
        u₃.other _ (by decide), p₂]) (by rw [u₄.rd, u₃.rd, rd₂]) (by rw [u₄.wr, u₃.wr, wr₂])
      (by rw [u₄.syms, u₃.syms, sy₂]) (by simp only [fUsed, sState, hdr]; omega_using [])
      (by rw [u₄.mem, u₃.mem, m₂]; exact fu) (by rw [u₄.other _ (by decide), u₃.gpr]; rfl) (by rw [u₄.gpr]; rfl)
      (by decide) (by decide) (by omega_using [wl, hu]) rfl rfl rfl rfl
  · -- No seeds left: exhausted.
    obtain ⟨st, cu, hc⟩ := R₁
    refine WP.ite _ z₂ (fun h => by simp [stOf] at h) (fun _ => ?_)
    refine WP.seq (cmpF_end B₂.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega_using [sz]) (by rw [m₂]; exact st)
      (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_)
    refine WP.ite _ z₃ (fun h => by simp at h) (fun _ => ?_)
    unfold Geo.exhausted
    refine WP.seq (wp_movi fun t₄ u₄ => wp_movi fun t₅ u₅ => WP.block_nil ?_)
    exact words (k := 0) (r := 0) (w := c) (by rw [u₅.mem, u₄.mem, m₃, m₂])
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), e₂])
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), p₂])
      (by rw [u₅.rd, u₄.rd, rd₃, rd₂]) (by rw [u₅.wr, u₄.wr, wr₃, wr₂]) (by rw [u₅.syms, u₄.syms, sy₃, sy₂])
      (by simp only [fC, sState, hdr]; omega_using []) (by rw [u₅.mem, u₄.mem, m₃, m₂]; exact cu)
      (by rw [u₅.other _ (by decide), u₄.gpr]; rfl) (by rw [u₅.gpr]; rfl) (by decide) (by decide) (by omega_using [wl, hc])
      rfl rfl rfl rfl
  · -- `rand` ran out.
    obtain ⟨st, cu, lj, hc, hj⟩ := R₁
    obtain jl : j < 2 ^ 32 := by simp only [Spec.Dsa.parameterSeeds] at hj; omega_using [hj]
    refine WP.ite _ z₂ (fun h => by simp [stOf] at h) (fun _ => ?_)
    refine WP.seq (cmpF_end B₂.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega_using [sz]) (by rw [m₂]; exact st)
      (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_)
    obtain B₃ := B₂.regs m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃
    refine WP.ite _ z₃ (fun _ => ?_) (fun h => by simp at h)
    obtain mem₃ : t₃.mem = t₁.mem := by rw [m₃, m₂]
    obtain edi₃ : t₃.gpr .edi = t₁.gpr .edi := by rw [g₃ _ (by decide), e₂]
    obtain esp₃ : t₃.gpr .esp = t₁.gpr .esp := by rw [g₃ _ (by decide), p₂]
    unfold Geo.ranOut
    simp only [seqs]
    refine WP.seq (availCmp_ok v B₃ (c := c) (by rw [mem₃]; exact cu) hc (w := g.budget) budget
      fun t₄ g₄ m₄ rd₄ wr₄ sy₄ a₄ cf₄ => WP.block_nil ?_)
    obtain mem₄ : t₄.mem = t₁.mem := by rw [m₄, mem₃]
    obtain edi₄ : t₄.gpr .edi = t₁.gpr .edi := by rw [g₄ _ (by decide) (by decide), edi₃]
    obtain esp₄ : t₄.gpr .esp = t₁.gpr .esp := by rw [g₄ _ (by decide) (by decide), esp₃]
    obtain rd₄' : t₄.rd = t₁.rd := by rw [rd₄, rd₃, rd₂]
    obtain wr₄' : t₄.wr = t₁.wr := by rw [wr₄, wr₃, wr₂]
    obtain sy₄' : t₄.syms = t₁.syms := by rw [sy₄, sy₃, sy₂]
    obtain budE : g.budget = Spec.Dsa.parameterEntropy E.pLen := by simp only [Geo.budget, Spec.Dsa.parameterEntropy, hp]
    refine WP.ite _ cf₄ (fun hlt => ?_) (fun hge => ?_)
    · -- A request: twice the octets left, at least `256 p_len`, at most the budget.
      obtain lt : E.witLen - c < Spec.Dsa.parameterEntropy E.pLen := by rw [← budE]; exact of_decide_eq_true hlt
      obtain eR : cRes E (.ranOut j c) = ⟨.entropy j (E.witLen - c), c, []⟩ := by
        simp only [cRes, ranOutResult, show ¬ Spec.Dsa.parameterEntropy E.pLen ≤ E.witLen - c by omega_using [lt], ↓reduceIte]
      obtain lb : 256 * g.pLen < 2 ^ 32 := by omega_using [bd]
      obtain lt' : E.witLen - c < 32769 * g.pLen := by
        have := lt; simp only [Spec.Dsa.parameterEntropy] at this; omega_using [hp, this]
      refine WP.seq (wp_cmpi fun t₅ f₅ c₅ _ => WP.block_nil ?_)
      obtain h₆ : WP isa (.ite .b (.block [.mov .eax (.imm (BitVec.ofNat 32 (256 * g.pLen)))]) (.block [])) t₅
          fun t => t.gpr .eax = BitVec.ofNat 32 (max (E.witLen - c) (256 * g.pLen)) ∧ t.mem = t₄.mem ∧
            (∀ r, r ≠ .eax → t.gpr r = t₄.gpr r) ∧ t.rd = t₄.rd ∧ t.wr = t₄.wr ∧ t.syms = t₄.syms :=
        WP.ite _ (show isa.eval .b t₅ = some (decide (E.witLen - c < 256 * g.pLen)) by
            show t₅.cf = _
            rw [c₅, a₄, toNat_ofNat_lt (by omega_using [wl]), toNat_ofNat_lt lb]) (fun h => wp_movi fun t₆ u₆ =>
              WP.block_nil ⟨by rw [u₆.gpr, Nat.max_eq_right (by have := of_decide_eq_true h; omega_using [this])], by
                rw [u₆.mem, f₅.mem], fun r hr => by rw [u₆.other _ hr, f₅.gpr], by rw [u₆.rd, f₅.rd],
                by rw [u₆.wr, f₅.wr], by rw [u₆.syms, f₅.syms]⟩)
            (fun h => WP.block_nil ⟨by rw [f₅.gpr, a₄, Nat.max_eq_left (by have := of_decide_eq_false h; omega_using [this])],
              f₅.mem, fun r _ => by rw [f₅.gpr], f₅.rd, f₅.wr, f₅.syms⟩)
      refine WP.seq (WP.mono h₆ fun t₆ h₆' => ?_)
      obtain ⟨a₆, m₆, g₆, rd₆, wr₆, sy₆⟩ := h₆'
      obtain mx : max (E.witLen - c) (256 * g.pLen) < 2 ^ 31 := by omega_using [bd, lt']
      refine WP.seq (wp_add fun t₇ u₇ _ => wp_cmpi fun t₈ f₈ c₈ _ => WP.block_nil ?_)
      obtain a₇ : t₇.gpr .eax = BitVec.ofNat 32 (2 * max (E.witLen - c) (256 * g.pLen)) := by
        rw [u₇.gpr, a₆, ← BitVec.ofNat_add]; congr 1; omega_using []
      obtain h₉ : WP isa (.ite .b (.block []) (.block [.mov .eax (.imm (BitVec.ofNat 32 g.budget))])) t₈
          fun t => t.gpr .eax = BitVec.ofNat 32 (min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget) ∧
            t.mem = t₄.mem ∧ (∀ r, r ≠ .eax → t.gpr r = t₄.gpr r) ∧ t.rd = t₄.rd ∧ t.wr = t₄.wr ∧
            t.syms = t₄.syms :=
        WP.ite _ (show isa.eval .b t₈ = some (decide (2 * max (E.witLen - c) (256 * g.pLen) < g.budget)) by
            show t₈.cf = _
            rw [c₈, a₇, toNat_ofNat_lt (by omega_using [bd, lt']), toNat_ofNat_lt budget])
          (fun h => WP.block_nil ⟨by rw [f₈.gpr, a₇, Nat.min_eq_left (by have := of_decide_eq_true h; omega_using [this])],
            by rw [f₈.mem, u₇.mem, m₆], fun r hr => by rw [f₈.gpr, u₇.other _ hr, g₆ _ hr],
            by rw [f₈.rd, u₇.rd, rd₆], by rw [f₈.wr, u₇.wr, wr₆], by rw [f₈.syms, u₇.syms, sy₆]⟩)
          (fun h => wp_movi fun t₉ u₉ => WP.block_nil ⟨by
              rw [u₉.gpr, Nat.min_eq_right (by have := of_decide_eq_false h; omega_using [this])],
            by rw [u₉.mem, f₈.mem, u₇.mem, m₆], fun r hr => by rw [u₉.other _ hr, f₈.gpr, u₇.other _ hr, g₆ _ hr],
            by rw [u₉.rd, f₈.rd, u₇.rd, rd₆], by rw [u₉.wr, f₈.wr, u₇.wr, wr₆],
            by rw [u₉.syms, f₈.syms, u₇.syms, sy₆]⟩)
      refine WP.seq (WP.mono h₉ fun t₉ h₉' => ?_)
      obtain ⟨a₉, m₉, g₉, rd₉, wr₉, sy₉⟩ := h₉'
      obtain rq : requested E.pLen (cRes E (.ranOut j c)) = min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget := by
        rw [eR]
        simp only [requested, VG.Proof.Entropy.requested, parameterRequest, VG.Proof.Entropy.request,
          Spec.Dsa.parameterEntropy, Geo.budget, hp]
      obtain rql : min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget < 2 ^ 32 := by omega_using [budget]
      refine WP.seq (wp_mov fun t₁₀ u₁₀ => ld_ok (Scr.of_eq B₃.scr (by rw [u₁₀.other _ (by decide), g₉ _ (by decide),
          g₄ _ (by decide) (by decide)]) (by rw [u₁₀.other _ (by decide), g₉ _ (by decide),
          g₄ _ (by decide) (by decide)]) (by rw [u₁₀.wr, wr₉, wr₄])) (r := .edx) (d := fSeedLeft)
        (by simp only [fSeedLeft, hdr]; omega_using [sz]) fun t₁₁ u₁₁ => WP.block_nil ?_)
      exact words (k := j) (r := min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget) (w := c)
        (by rw [u₁₁.mem, u₁₀.mem, m₉, mem₄])
        (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide), edi₄])
        (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide), esp₄])
        (by rw [u₁₁.rd, u₁₀.rd, rd₉, rd₄']) (by rw [u₁₁.wr, u₁₀.wr, wr₉, wr₄']) (by rw [u₁₁.syms, u₁₀.syms, sy₉, sy₄'])
        (by simp only [fC, sState, hdr]; omega_using []) (by rw [u₁₁.mem, u₁₀.mem, m₉, mem₄]; exact cu)
        (by rw [u₁₁.gpr, u₁₀.mem, m₉, mem₄]; exact lj) (by rw [u₁₁.other _ (by decide), u₁₀.gpr, a₉]) jl rql (by omega_using [wl, hc])
        (by rw [eR]; rfl) rq.symm (by rw [eR]) (by rw [eR]; rfl)
    · -- Exhausted: the octets left reach the budget.
      obtain ge : Spec.Dsa.parameterEntropy E.pLen ≤ E.witLen - c := by
        rw [← budE]; have := of_decide_eq_false hge; omega_using [this]
      obtain eR : cRes E (.ranOut j c) = ⟨.exhausted, c, []⟩ := by simp only [cRes, ranOutResult, ge, ↓reduceIte]
      unfold Geo.exhausted
      refine WP.seq (wp_movi fun t₅ u₅ => wp_movi fun t₆ u₆ => WP.block_nil ?_)
      exact words (k := 0) (r := 0) (w := c) (by rw [u₆.mem, u₅.mem, mem₄])
        (by rw [u₆.other _ (by decide), u₅.other _ (by decide), edi₄])
        (by rw [u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
        (by rw [u₆.rd, u₅.rd, rd₄']) (by rw [u₆.wr, u₅.wr, wr₄']) (by rw [u₆.syms, u₅.syms, sy₄'])
        (by simp only [fC, sState, hdr]; omega_using []) (by rw [u₆.mem, u₅.mem, mem₄]; exact cu)
        (by rw [u₆.other _ (by decide), u₅.gpr]; rfl) (by rw [u₆.gpr]; rfl) (by decide) (by decide) (by omega_using [wl, hc])
        (by rw [eR]; rfl) (by rw [eR]; rfl) (by rw [eR]) (by rw [eR]; rfl)

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.Entry`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.Generation.ABI`, which this module and modules that import it used -/

section

/-! # The generation contract's precondition at the call -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- The contract, as the registration gives it. -/
abbrev genContract : Contract isa := Spec.Dsa.parameterSearchContract
  (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 216

def reservedRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 216#64, 216⟩

/-- The modulus's width, `state[1]`. -/
abbrev pLenOf (s : State) : Nat := (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat

/-- What the precondition says, in the shape `sig_pre` leaves it. -/
structure CallFacts (s : State) : Prop where
  low : 216 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 4 + 32 ≤ 2 ^ 32
  rdTable : s.rd.drop (s.rd.length - 1) = Abi.constRegions (fun name => (s.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts
  tableHeld : Abi.constsHeld s.mem (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts
  tableFar : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64) VG.Impl.RsaKeyGen.TrialTable32.consts,
    t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
    t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s)
  tableAligned : ∀ t ∈ Abi.constRegions (fun name => (s.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts, t.base.toNat % 64 = 0
  rdPrefix : s.rd.take (s.rd.length - 1) = [(⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region)]
  wr : s.wr = [(⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region), ⟨(arg s 2).setWidth 64, 8⟩,
    ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩, ⟨(arg s 7).setWidth 64, 32⟩, ⟨argAddr s 0, 32⟩]
  outUsed : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, 8⟩
  outRand : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  outScr : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  outSt : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  outArgs : (⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  usedRand : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  usedScr : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  usedSt : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  usedArgs : (⟨(arg s 2).setWidth 64, 8⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  randScr : (⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region).Disjoint
    ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  randSt : (⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  randArgs : (⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  scrSt : (⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  scrArgs : (⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  stArgs : (⟨(arg s 7).setWidth 64, 32⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  retUsed : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, 8⟩
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  retScr : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  retSt : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 32⟩
  stackOut : (reservedRegion s).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  stackUsed : (reservedRegion s).Disjoint ⟨(arg s 2).setWidth 64, 8⟩
  stackRand : (reservedRegion s).Disjoint ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  stackScr : (reservedRegion s).Disjoint ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩
  stackSt : (reservedRegion s).Disjoint ⟨(arg s 7).setWidth 64, 32⟩
  stackArgs : (reservedRegion s).Disjoint ⟨argAddr s 0, 32⟩
  outFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  usedFit : (arg s 2).toNat + 8 ≤ 2 ^ 32
  randFit : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  scrFit : (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32
  stFit : (arg s 7).toNat + 32 ≤ 2 ^ 32
  pValid : Spec.Dsa.generationPLenValid (pLenOf s) = true
  outLen : (arg s 1).toNat = 2 * pLenOf s + Spec.Dsa.generationQLen (pLenOf s)
  room : Spec.Dsa.generationScratchWords (pLenOf s) ≤ (arg s 6).toNat
  seeds : (s.mem.readW (BitVec.setWidth 64 (arg s 7)) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (BitVec.setWidth 64 (arg s 7) + 16) 64 =
    BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s))
  randLen : (arg s 4).toNat ≤ Spec.Dsa.parameterEntropy (pLenOf s)

theorem call_facts {s : State} (h : genContract.pre s) : CallFacts s := by
  sig_pre [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  all_goals dsimp only [reservedRegion, VG.Impl.RsaKeyGen.TrialTable32.consts]
  all_goals with_reducible assumption

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.ABIEnv`, which only this module used -/

section

/-! # The precondition gives a valid environment -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

/-- The environment of a call, from its arguments: the seeds and the `h`
candidates are those of each seed's own environment (`Env.atSeed`,
`Env.window`). -/
def callEnv (s : State) : Env where
  pLen := pLenOf s
  qLen := Spec.Dsa.generationQLen (pLenOf s)
  base := (arg s 5).setWidth 64
  size := (arg s 6).toNat * 8
  out := (arg s 0).setWidth 64
  usedP := (arg s 2).setWidth 64
  stP := (arg s 7).setWidth 64
  k0 := (s.mem.readW ((arg s 7).setWidth 64) 64).toNat
  seedsOff := 0
  seedsLen := 0
  hsOff := 0
  hsLen := 0
  wit := (arg s 3).setWidth 64
  witLen := (arg s 4).toNat
  sp := s.gpr .esp - BitVec.ofNat 32 16
  table := (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64
  witT := Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat

theorem disjoint_nat {a b : Addr} {n k : Nat}
    (_an : a.toNat + n ≤ 2 ^ 64) (_bk : b.toNat + k ≤ 2 ^ 64) (np : 0 < n) (kp : 0 < k)
    (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  by_contra bad
  have overlap : a.toNat < b.toNat + k ∧ b.toNat < a.toNat + n := by omega_using [bad]
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      omega_using [bad, order]
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]; change 0 + 1 ≤ k; omega_using [kp]
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]; change 0 + 1 ≤ n; omega_using [np]
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      omega_using [bad, order]

theorem CallFacts.tableRegion {s : State} (F : CallFacts s) :
    let t : Region := ⟨(s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64, 8192⟩
    t.base.toNat + 8192 ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧ t.Disjoint (reservedRegion s) :=
  F.tableFar _ (by rw [ProbablePrime.table_regions]; exact List.mem_cons_self)

theorem CallFacts.rd {s : State} (F : CallFacts s) :
    s.rd = [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, (callEnv s).tableRegion] := by
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, F.rdPrefix, F.rdTable, ProbablePrime.table_regions]
  rfl

theorem CallFacts.pLens {s : State} (F : CallFacts s) : pLenOf s = 128 ∨ pLenOf s = 256 ∨ pLenOf s = 384 := by
  have := F.pValid
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  omega_using [this]

theorem CallFacts.lengths {s : State} (F : CallFacts s) :
    Spec.Dsa.generationLengthsValid (pLenOf s) (Spec.Dsa.generationQLen (pLenOf s)) := by
  rcases F.pLens with h | h | h <;> simp [Spec.Dsa.generationLengthsValid, Spec.Dsa.generationQLen, h]

theorem CallFacts.reserved {s : State} (F : CallFacts s) : reservedRegion s = below (s.gpr .esp) 216 := by
  unfold reservedRegion below
  rw [Taint.sub_setWidth F.low]

theorem CallFacts.stackSub {s : State} (F : CallFacts s) : (callEnv s).stackRegion.Sub (reservedRegion s) := by
  rw [F.reserved]
  exact below_inner (by decide) F.low

theorem CallFacts.spNat {s : State} (F : CallFacts s) : (callEnv s).sp.toNat = (s.gpr .esp).toNat - 16 :=
  sub_toNat (by have := F.low; omega_using [this])

theorem CallFacts.reservedNat {s : State} (F : CallFacts s) :
    ((s.gpr .esp).setWidth 64 - 216#64).toNat = (s.gpr .esp).toNat - 216 := by
  change (reservedRegion s).base.toNat = _
  rw [F.reserved]
  change ((s.gpr .esp - BitVec.ofNat 32 216).setWidth 64).toNat = _
  rw [toNat_wide, sub_toNat F.low]

/-- `scratch` lies below the reserved stack or above the return address. -/
theorem CallFacts.scratchNat {s : State} (F : CallFacts s) :
    (arg s 5).toNat + (arg s 6).toNat * 8 ≤ (s.gpr .esp).toNat - 216 ∨
      (s.gpr .esp).toNat + 4 ≤ (arg s 5).toNat := by
  have room := F.room
  unfold Spec.Dsa.generationScratchWords at room
  have fit := F.scrFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) (by omega_using [room]) (by decide)
    F.stackScr.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) (by omega_using [room]) (by decide)
    F.retScr.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [room, b₁, b₂]

/-- `out` lies below the reserved stack or above the return address. -/
theorem CallFacts.outNat {s : State} (F : CallFacts s) :
    (arg s 0).toNat + (arg s 1).toNat ≤ (s.gpr .esp).toNat - 216 ∨
      (s.gpr .esp).toNat + 4 ≤ (arg s 0).toNat := by
  have pos : 0 < (arg s 1).toNat := by
    rw [F.outLen]; rcases F.pLens with h | h | h <;> omega_using [h]
  have fit := F.outFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) pos (by decide)
    F.stackOut.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) pos (by decide)
    F.retOut.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [pos, b₁, b₂]

/-- `state` lies below the reserved stack or above the return address. -/
theorem CallFacts.stNat {s : State} (F : CallFacts s) :
    (arg s 7).toNat + 32 ≤ (s.gpr .esp).toNat - 216 ∨ (s.gpr .esp).toNat + 4 ≤ (arg s 7).toNat := by
  have fit := F.stFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) (by decide) (by decide)
    F.stackSt.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) (by decide) (by decide)
    F.retSt.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [b₁, b₂]

/-- `used` lies below the reserved stack or above the return address. -/
theorem CallFacts.usedNat {s : State} (F : CallFacts s) :
    (arg s 2).toNat + 8 ≤ (s.gpr .esp).toNat - 216 ∨ (s.gpr .esp).toNat + 4 ≤ (arg s 2).toNat := by
  have fit := F.usedFit
  have esp := (s.gpr .esp).isLt
  have low := F.low
  have b₁ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [F.reservedNat]; omega_using []) (by decide) (by decide)
    F.stackUsed.symm
  have b₂ := disjoint_nat (by rw [toNat_wide]; omega_using []) (by rw [toNat_wide]; omega_using []) (by decide) (by decide)
    F.retUsed.symm
  rw [toNat_wide, F.reservedNat] at b₁
  rw [toNat_wide, toNat_wide] at b₂
  omega_using [b₁, b₂]

theorem CallFacts.outLenEq {s : State} (F : CallFacts s) : (callEnv s).outLen = (arg s 1).toNat := by
  simp only [Env.outLen, callEnv, F.outLen]

theorem CallFacts.outRegion {s : State} (F : CallFacts s) :
    (callEnv s).outRegion = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ := by
  simp only [Env.outRegion, F.outLenEq]; rfl

/-- A region of the arguments' memory, apart from the stack the calls use. -/
theorem CallFacts.far {s : State} (F : CallFacts s) {r : Region} (h : (reservedRegion s).Disjoint r) :
    r.Disjoint (callEnv s).stackRegion := h.symm.sub_right F.stackSub

theorem CallFacts.valid {s : State} (F : CallFacts s) : (callEnv s).Valid := by
  have room := F.room
  unfold Spec.Dsa.generationScratchWords at room
  have T := F.tableRegion
  have scratchNat := F.scratchNat
  have spNat := F.spNat
  have low := F.low
  have ws : (callEnv s).scratchRegion = ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 8⟩ := rfl
  have wW : (callEnv s).witRegion = ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩ := rfl
  have uR : (callEnv s).usedRegion = ⟨(arg s 2).setWidth 64, 8⟩ := rfl
  have sR : (callEnv s).stRegion = ⟨(arg s 7).setWidth 64, 32⟩ := rfl
  have tW : ∀ r ∈ s.wr, (callEnv s).tableRegion.Disjoint r := T.2.1
  refine ⟨F.lengths, by change 512 * pLenOf s + 8192 ≤ (arg s 6).toNat * 8; omega_using [room],
    by change ((arg s 5).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.scrFit,
    by rw [F.outLenEq]; change ((arg s 0).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.outFit,
    by change ((arg s 3).setWidth 64).toNat + _ ≤ _; rw [toNat_wide]; exact F.randFit,
    by simp [callEnv], by simp [callEnv], by rw [spNat]; omega_using [low], ?_, by rw [ws, F.outRegion]; exact F.outScr,
    ⟨by rw [wW, ws]; exact F.randScr, by rw [wW, F.outRegion]; exact F.outRand.symm,
      by rw [wW]; exact F.far F.stackRand⟩,
    by rw [F.outRegion]; exact F.far F.stackOut,
    by rw [ws]; exact F.far F.stackScr, T.1, (toNat_wide _).symm ▸ (arg s 0).isLt,
    (toNat_wide _).symm ▸ (arg s 3).isLt, (arg s 4).isLt, ⟨T.2.1 _ ?_, ?_, T.2.2.2.sub_right F.stackSub⟩, ?_,
    by change ((arg s 2).setWidth 64).toNat + 8 ≤ _; rw [toNat_wide]; exact F.usedFit,
    by change ((arg s 7).setWidth 64).toNat + 32 ≤ _; rw [toNat_wide]; exact F.stFit, ?_, ?_, F.seeds⟩
  · change (callEnv s).sp.toNat ≤ ((arg s 5).setWidth 64).toNat ∨
      ((arg s 5).setWidth 64).toNat + (arg s 6).toNat * 8 + 200 ≤ (callEnv s).sp.toNat
    rw [spNat, toNat_wide]
    omega_using [room, scratchNat]
  · rw [F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rw [F.outRegion]; exact T.2.1 _ (by rw [F.wr]; exact List.mem_cons_self)
  · exact F.tableAligned _ (by rw [ProbablePrime.table_regions]; exact List.mem_cons_self)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [uR, ws]; exact F.usedScr
    · rw [uR, F.outRegion]; exact F.outUsed.symm
    · rw [uR]; exact F.far F.stackUsed
    · rw [uR, sR]; exact F.usedSt
    · rw [uR, wW]; exact F.usedRand
    · exact (tW _ (by rw [F.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [sR, ws]; exact F.scrSt.symm
    · rw [sR, F.outRegion]; exact F.outSt.symm
    · rw [sR]; exact F.far F.stackSt
    · rw [sR, wW]; exact F.randSt.symm
    · exact (tW _ (by rw [F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))).symm

end VG.Proof.Dsa.X86.Generation

end

end


/-! # The entry: the arguments into the state words -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86.Compact (entered savedRegisters)

/-- What the entry keeps of the state it starts from. -/
structure EInv (s t : State) : Prop where
  esp : t.gpr .esp = (callEnv s).sp
  rd : t.rd = s.rd
  wr : t.wr = below (s.gpr .esp) 16 :: s.wr
  syms : t.syms = s.syms
  fr : Frame [(callEnv s).scratchRegion, below (s.gpr .esp) 16] s.mem t.mem
  fe : Frame [(callEnv s).scratchRegion] (entered s).mem t.mem

theorem entered_inv {s : State} (F : CallFacts s) : EInv s (entered s) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega_using [this]
  refine ⟨by rw [entered, pushed_esp]; rfl, pushed_rd _ _, pushed_wr _ _, pushRegs_syms _ _, ?_, Frame.refl _ _⟩
  exact Frame.mono (pushed_frame (rs := savedRegisters) (s := s) (by decide) fit)
    fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem argOffset {s : State} (F : CallFacts s) {i : Nat} (hi : i < 8) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have bound := F.argsFit
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hi, bound]

theorem addrArg (s : State) (i : Nat) : addr (callEnv s).sp (20 + 4 * i) = argAddr s i := by
  change ((s.gpr .esp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) = _
  rw [show 20 + 4 * i = 16 + (4 + 4 * i) by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem argAccess {s t : State} (F : CallFacts s) (I : EInv s t) {i : Nat} (hi : i < 8) :
    InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
  have bound := F.argsFit
  refine ⟨⟨argAddr s 0, 32⟩, List.mem_append_right _ ?_, ?_⟩
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  · rw [argOffset F hi]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem argValue {s t : State} (F : CallFacts s) (I : EInv s t) {i : Nat} (hi : i < 8) :
    t.mem.readW (argAddr s i) 32 = arg s i := by
  have bound := F.argsFit
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := F.low; omega_using [this]
  have separate : (⟨argAddr s 0, 32⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 32⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by omega_using [bound])]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (⟨argAddr s 0, 32⟩ : Region).Contains (argAddr s i) 4 := by
    rw [argOffset F hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine I.fr.readW (r := ⟨argAddr s 0, 32⟩) (w := 32) contains ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact F.scrArgs.symm
  · exact separate

theorem EInv.store {s t t' : State} (F : CallFacts s) (I : EInv s t) {o : Nat} (ho : o + 4 ≤ 73728) {v : BitVec 32}
    (hm : t'.mem = t.mem.writeW (off (callEnv s).base o) v) (esp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd)
    (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : EInv s t' := by
  have v := F.valid
  have := v.size_ge
  have := v.scratchFit
  refine ⟨esp.trans I.esp, rd.trans I.rd, wr.trans I.wr, sy.trans I.syms, ?_, ?_⟩
  · rw [hm]
    exact Frame.writeW I.fr List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_using [ho]))
  · rw [hm]
    exact Frame.writeW I.fe List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_using [ho]))

/-- `copyArg`: an argument into a state word. -/
theorem copyArg_ok {s t : State} (F : CallFacts s) (I : EInv s t) (hs : Scr t (callEnv s).base (callEnv s).size)
    {i o : Nat} (hi : i < 8) (ho : o + 4 ≤ 73728) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', EInv s t' → Scr t' (callEnv s).base (callEnv s).size →
      t'.mem = t.mem.writeW (off (callEnv s).base o) (arg s i) → WP isa (.block is) t' Q) :
    WP isa (.block (copyArg i o ++ is)) t Q := by
  have := F.valid.size_ge
  simp only [copyArg, List.cons_append, List.nil_append]
  refine wp_ldm (B := (callEnv s).sp) I.esp (by rw [addrArg]; exact argAccess F I hi) fun t₁ u₁ => ?_
  have hs₁ := Scr.of_eq hs (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr
  refine st_ok hs₁ (d := o) (by omega_using [ho, this]) fun t₂ M₂ => k t₂ ?_ ?_ ?_
  · refine I.store F ho (v := arg s i) ?_ (by rw [M₂.gpr, u₁.other _ (by decide)]) (by rw [M₂.rd, u₁.rd])
      (by rw [M₂.wr, u₁.wr]) (by rw [M₂.syms, u₁.syms])
    rw [M₂.mem, u₁.mem, u₁.gpr, addrArg, argValue F I hi]
  · exact Scr.of_eq hs₁ (by rw [M₂.gpr]) (by rw [M₂.gpr]) M₂.wr
  · rw [M₂.mem, u₁.mem, u₁.gpr, addrArg, argValue F I hi]

theorem EInv.regs {s t t' : State} (I : EInv s t) (hm : t'.mem = t.mem) (esp : t'.gpr .esp = t.gpr .esp)
    (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : EInv s t' :=
  ⟨esp.trans I.esp, rd.trans I.rd, wr.trans I.wr, sy.trans I.syms, by rw [hm]; exact I.fr, by rw [hm]; exact I.fe⟩

theorem readW_off_other (m : Mem) (b : Addr) {o o' : Nat} (v : BitVec 32) (h : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (h₁ : o + 4 ≤ 2 ^ 64) (h₂ : o' + 4 ≤ 2 ^ 64) :
    (m.writeW (off b o) v).readW (off b o') 32 = m.readW (off b o') 32 :=
  Mem.readW_writeW_sep (Offset.sep b (d := o') (n := 4) (e := o) (k := 4) (by omega_using [h]) h₂ h₁) (by decide)

/-- A state word's low half. -/
theorem readW_lowNat (m : Mem) (a : Addr) : m.readW a 32 = BitVec.ofNat 32 (m.readW a 64).toNat := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo]
  simp only [BitVec.extractLsb', Nat.shiftRight_zero]

/-- The address of `state`'s word `d`. -/
theorem stAddr {s : State} (F : CallFacts s) {d : Nat} (hd : d + 4 ≤ 32) :
    addr (arg s 7) d = (arg s 7).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := F.stFit; omega_using [hd, this])

/-- The low halves of `state`'s words, before anything wrote them. -/
theorem stWord {s t : State} (F : CallFacts s) (I : EInv s t) {d : Nat} (hd : d + 8 ≤ 32) :
    InRegions (t.rd ++ t.wr) (addr (arg s 7) d) 4 ∧
      t.mem.readW (addr (arg s 7) d) 32 = BitVec.ofNat 32 (s.mem.readW ((arg s 7).setWidth 64 + BitVec.ofNat 64 d) 64).toNat := by
  have fit := F.stFit
  rw [stAddr F (by omega_using [hd])]
  refine ⟨⟨⟨(arg s 7).setWidth 64, 32⟩, List.mem_append_right _ ?_, Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩, ?_⟩
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  · have sub : (below (s.gpr .esp) 16).Sub (reservedRegion s) := by
      rw [F.reserved]; exact below_sub (by decide) F.low
    rw [I.fr.readW (r := ⟨(arg s 7).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact F.scrSt.symm.sub_left (Offset.sub_base _ (by omega_using [hd]))
      · exact (F.stackSt.symm.sub_right sub).sub_left (Offset.sub_base _ (by omega_using [hd]))) (by decide), readW_lowNat]

/-- After the entry. -/
structure EPost (s t : State) : Prop where
  inv : EInv s t
  base : Base (callEnv s) t
  cur : t.mem.readW (off (callEnv s).base fC) 32 = BitVec.ofNat 32 0
  status : t.mem.readW (off (callEnv s).base fStatus) 32 = BitVec.ofNat 32 0

theorem narrow (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem entry_ok {s : State} (F : CallFacts s) : WP isa (.block entry) (entered s) (EPost s) := by
  have v := F.valid
  have sz := v.size_ge
  have I₀ := entered_inv F
  simp only [entry, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldm (B := (callEnv s).sp) I₀.esp (by rw [addrArg]; exact argAccess F I₀ (by decide)) fun t₀ u₀ => ?_
  have I₁ := I₀.regs u₀.mem (u₀.other _ (by decide)) u₀.rd u₀.wr u₀.syms
  have hs₀ : Scr t₀ (callEnv s).base (callEnv s).size := by
    refine ⟨?_, ?_, v.scratchFit, ?_⟩
    · rw [u₀.gpr, addrArg, argValue F I₀ (by decide)]; rfl
    · rw [I₁.wr, F.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · have := v.stackScratch; have := v.low
      refine ⟨by rw [I₁.esp]; omega_using [this], ?_⟩
      rw [I₁.esp]; omega_arith
  refine copyArg_ok F I₁ hs₀ (i := 0) (o := fOut) (by decide) (by decide) fun t₁ I₂ hs₁ m₁ => ?_
  refine copyArg_ok F I₂ hs₁ (i := 2) (o := fUsedP) (by decide) (by decide) fun t₂ I₃ hs₂ m₂ => ?_
  refine copyArg_ok F I₃ hs₂ (i := 3) (o := fWit) (by decide) (by decide) fun t₃ I₄ hs₃ m₃ => ?_
  refine copyArg_ok F I₄ hs₃ (i := 4) (o := fWitLen) (by decide) (by decide) fun t₄ I₅ hs₄ m₄ => ?_
  refine copyArg_ok F I₅ hs₄ (i := 7) (o := fStP) (by decide) (by decide) fun t₅ I₆ hs₅ m₅ => ?_
  refine stImm_ok hs₅ (o := fC) (v := 0) (by simp only [fC, hdr]; omega_using [sz]) fun t₉ g₉ m₉ rd₉ wr₉ sy₉ => ?_
  have hs₉ := Scr.of_eq hs₅ (g₉ _ (by decide)) (g₉ _ (by decide)) wr₉
  have I₁₀ := I₆.store F (o := fC) (by decide) m₉ (g₉ _ (by decide)) rd₉ wr₉ sy₉
  refine stImm_end hs₉ (o := fStatus) (v := 0) (by simp only [fStatus, hdr]; omega_using [sz])
    fun t₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ sy₁₀ => ?_
  have hs₁₀ := Scr.of_eq hs₉ (g₁₀ _ (by decide)) (g₁₀ _ (by decide)) wr₁₀
  have I := I₁₀.store F (o := fStatus) (by decide) m₁₀ (g₁₀ _ (by decide)) rd₁₀ wr₁₀ sy₁₀
  have M : t₁₀.mem = (((((((entered s).mem.writeW (off (callEnv s).base fOut) (arg s 0)).writeW
      (off (callEnv s).base fUsedP) (arg s 2)).writeW (off (callEnv s).base fWit) (arg s 3)).writeW
      (off (callEnv s).base fWitLen) (arg s 4)).writeW (off (callEnv s).base fStP) (arg s 7)).writeW
      (off (callEnv s).base fC) (BitVec.ofNat 32 0)).writeW (off (callEnv s).base fStatus) (BitVec.ofNat 32 0) := by
    rw [m₁₀, m₉, m₅, m₄, m₃, m₂, m₁, u₀.mem]
  have rd : (callEnv s).witRegion ∈ t₁₀.rd ∧ (callEnv s).tableRegion ∈ t₁₀.rd := by
    rw [I.rd, F.rd]; exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
  have far : ∀ R ∈ [(callEnv s).witRegion, (callEnv s).tableRegion],
      ∀ r ∈ [(callEnv s).scratchRegion, below (s.gpr .esp) 16], R.Disjoint r := by
    have sub : (below (s.gpr .esp) 16).Sub (reservedRegion s) := by
      rw [F.reserved]; exact below_sub (by decide) F.low
    intro R hR r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR hr
    rcases hr with rfl | rfl
    · rcases hR with rfl | rfl
      · exact v.witFar.1
      · exact v.tableFar.1
    · have T := F.tableRegion
      rcases hR with rfl | rfl
      · exact F.stackRand.symm.sub_right sub
      · exact T.2.2.2.sub_right sub
  have wit : Spec.Rsa.bytesAt t₁₀.mem (callEnv s).wit (callEnv s).witLen = (callEnv s).witT :=
    VG.Proof.RsaKeyGen.frame_bytesAt I.fr (far (callEnv s).witRegion (by simp))
      (Nat.le_of_lt (Nat.lt_trans (arg s 4).isLt (by decide)))
  have sy : (t₁₀.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64 = (callEnv s).table := by
    rw [I.syms]; rfl
  refine ⟨I, ⟨hs₁₀, I.esp, rd.1, rd.2, ?_, ?_, ?_, sy, ?_, wit, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [I.wr, F.wr, F.outRegion]; simp
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rw [I.wr, F.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  · intro c hc i hi
    simp only [VG.Impl.RsaKeyGen.TrialTable32.consts, List.mem_singleton] at hc
    subst hc
    have len : i < 1024 := by simpa [VG.Impl.RsaKeyGen.TrialTable32.packed] using hi
    have fit := v.tableFit
    rw [I.syms, ← F.tableHeld _ (List.mem_singleton_self _) i hi]
    exact Frame.readW I.fr (r := (callEnv s).tableRegion)
      (Offset.contains_base _ (by change 8 * i + 64 / 8 ≤ 8192; omega_using [len]) (by omega_using [len]))
      (far _ (by simp)) (by decide)
  all_goals
    rw [M]
    simp (disch := decide) only [readW_off_other, Mem.readW_writeW_self32]
  all_goals first
    | exact (narrow _).symm
    | simp only [callEnv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    | rfl

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.Generation.Frame`, which only this module used -/

section

/-! # The callee-saved registers' frame around the generator

`Compact.frame_ok`'s frame, around any body that keeps the saved registers'
slots and the return address. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Compact (savedRegisters entered popped_four_value)

theorem frameWith_ok {inner : Prog isa} (hns : NoSp (.seq inner (.block Compact.restoreRegs))) {s : State}
    {Q : Mem → BitVec 32 → Prop} (stackFit : 16 ≤ (s.gpr .esp).toNat) (stackTop : (s.gpr .esp).toNat + 4 ≤ 2 ^ 32)
    (core : WP isa inner (entered s) fun t =>
      (∀ x, (⟨((entered s).gpr .esp).setWidth 64, 20⟩ : Region).Contains x 1 → t.mem x = (entered s).mem x) ∧
      Q t.mem (t.gpr .eax) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t) :
    WP isa (.frame (.push [.ebx, .ebp, .esi, .edi]) (.seq inner (.block Compact.restoreRegs)) (.pop .ebx 4)) s
      fun t => abiPreserved s t ∧ Q t.mem (t.gpr .eax) := by
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit hns ?_
  refine WP.seq (WP.mono core fun t ⟨O, Qt, K⟩ => ?_)
  have sp : t.gpr .esp = (entered s).gpr .esp := K.1 .esp (by decide)
  have eNat : ((entered s).gpr .esp).toNat = (s.gpr .esp).toNat - 16 := by
    rw [entered, pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    have := (s.gpr .esp).isLt
    omega
  have keepAt : ∀ (k : Nat), k + 4 ≤ 20 → t.mem.readW (addr ((entered s).gpr .esp) k) 32 =
      (entered s).mem.readW (addr ((entered s).gpr .esp) k) 32 := fun k hk => by
    have address : addr ((entered s).gpr .esp) k = ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 k :=
      addr_eq (by omega_using [eNat, hk])
    rw [address]
    exact Mem.readW_congr fun j hj => O _ (by
      rw [show ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 k + BitVec.ofNat 64 j =
          ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 (k + j) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
      exact Offset.contains_base _ (by omega_using [hk, hj]) (by omega_using [hk, hj]))
  have read (i : Nat) (hi : i < 4) :
      readSrc t (.mem (at_ .esp (4 * i))) = some (s.gpr (savedRegisters[3 - i]'(by
        change 3 - i < 4; omega_using []))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
      change (below (s.gpr .esp) 16).Contains _ 4
      have region : below (s.gpr .esp) 16 = ⟨((entered s).gpr .esp).setWidth 64, 16⟩ := by
        unfold entered savedRegisters below
        rw [pushed_esp]
        rfl
      rw [region]
      have address : addr ((entered s).gpr .esp) (4 * i) =
          ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i) := addr_eq (by omega_using [eNat, hi])
      rw [address]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    have value : t.mem.readW (addr (t.gpr .esp) (4 * i)) 32 =
        (entered s).mem.readW (addr ((entered s).gpr .esp) (4 * i)) 32 := by
      rw [sp]; exact keepAt _ (by omega_using [hi])
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, value]
    exact congrArg some (pushed_word (rs := savedRegisters) (by decide) stackFit hi)
  refine WP.mono (VG.Proof.Mont.X86.Compact.restore_ok (read 0 (by decide)) (read 1 (by decide))
    (read 2 (by decide))) ?_
  rintro t' ⟨edi, esi, ebp, M, K'⟩
  have sp' : t'.gpr .esp = (entered s).gpr .esp := (K'.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show savedRegisters.length = 4 from rfl, popped_four_value, sp', M]
      have word := pushed_word (s := s) (rs := savedRegisters) (by decide) stackFit (i := 3) (by decide)
      have e12 : (((entered s).gpr .esp) + 12).setWidth 64 = addr ((entered s).gpr .esp) 12 := rfl
      rw [e12, keepAt 12 (by decide)]
      exact word
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', entered, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, M]
    have ret : (s.gpr .esp).setWidth 64 = addr ((entered s).gpr .esp) 16 := by
      unfold addr entered savedRegisters
      rw [pushed_esp]
      congr 1
      exact (BitVec.sub_add_cancel _ _).symm
    rw [ret, keepAt 16 (by decide), ← ret]
    have saved := pushed_frame (rs := savedRegisters) (s := s) (by decide) stackFit
    have separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
      unfold below
      rw [Taint.sub_setWidth stackFit]
      exact Offset.base_disjoint_below _ (by decide)
    exact saved.readW (Region.contains_self _ _) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)
  · rw [popped_mem, M, popped_gpr _ _ _ (by decide) (by decide), K'.1 .eax (by decide)]
    exact Qt

end VG.Proof.Dsa.X86.Generation

end

end


/-! # Parameter generation meets its contract on i686 -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86.Compact (entered savedRegisters)
open VG.Proof.Dsa.Generation
open VG.Impl.Mont.X86 (at_)

/-- The whole search's result. -/
abbrev sW (E : Env) : Spec.Dsa.ParameterSearchResult := Spec.Dsa.parameterSearch E.pLen E.k0 E.witT

/-- What `out` holds, as the contract states it. -/
def outSpec (g : Geo) (r : Spec.Dsa.ParameterSearchResult) : List Byte :=
  match r.outcome with
  | .accepted a => Spec.Dsa.encodeParams g.pLen g.qLen a
  | _ => List.replicate (2 * g.pLen + g.qLen) 0

theorem outBytes_eq (E : Env) (g : Geo) (o : COut) : outBytes g o = outSpec g (cRes E o) := by
  cases o with
  | found => rfl
  | noSeeds => rfl
  | ranOut j c =>
    simp only [outBytes, outSpec, cRes, ranOutResult]
    by_cases hb : Spec.Dsa.parameterEntropy E.pLen ≤ E.witLen - c
    · simp only [hb, ↓reduceIte]
    · simp only [hb, ↓reduceIte]

/-- After one geometry's search and result. -/
structure GPost (E : Env) (g : Geo) (t u : State) : Prop where
  fr : Frame [E.scratchRegion, E.stackRegion, E.outRegion, E.stRegion, E.usedRegion] t.mem u.mem
  out : Spec.Rsa.bytesAt u.mem E.out (2 * g.pLen + g.qLen) = outSpec g (sW E)
  st0 : u.mem.readW (E.stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW E).remaining
  st1 : u.mem.readW (E.stP + BitVec.ofNat 64 8) 64 = t.mem.readW (E.stP + BitVec.ofNat 64 8) 64
  st2 : u.mem.readW (E.stP + BitVec.ofNat 64 16) 64 = t.mem.readW (E.stP + BitVec.ofNat 64 16) 64
  st3 : u.mem.readW (E.stP + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (requested E.pLen (sW E))
  used : u.mem.readW (E.usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW E).used
  eax : u.gpr .eax = BitVec.ofNat 32 (sW E).status
  esp : u.gpr .esp = t.gpr .esp
  rd : u.rd = t.rd
  wr : u.wr = t.wr

theorem generate_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {t : State} (B : Base E t)
    (hL : t.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.k0)
    (hC : t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 0)
    (hst : t.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0) :
    WP isa g.generate t (GPost E g t) := by
  obtain ap := sRanges_apart G v hp
  have sz := v.size_ge
  have sf := v.stFit
  unfold Geo.generate
  refine WP.seq (WP.mono (search_ok G v hp hq B hL hC hst) fun m ⟨K, R, e⟩ =>
    WP.mono (finish_ok G v hp hq K.base R) fun u P => ?_)
  obtain stK : ∀ d, d + 8 ≤ 32 → m.mem.readW (E.stP + BitVec.ofNat 64 d) 64 =
      t.mem.readW (E.stP + BitVec.ofNat 64 d) 64 := fun d hd =>
    Frame.readW K.chg (r := ⟨E.stP + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Env.far_all ((v.stFar _ List.mem_cons_self).sub_left (Offset.sub_base _ hd))
        ((v.stFar _ (by simp)).sub_left (Offset.sub_base _ hd)) fun o ho => (ap o ho).1) (by decide)
  refine ⟨?_, by rw [P.out, outBytes_eq E, e], by rw [P.st0, e], by rw [P.st1, stK 8 (by omega_using [])],
    by rw [P.st2, stK 16 (by omega_using [])], by rw [P.st3, e], by rw [P.used, e], by rw [P.eax, e],
    P.esp.trans (K.base.sp.trans B.sp.symm), P.rd.trans K.rd, P.wr.trans K.wr⟩
  refine Frame.trans (Frame.sub K.chg fun r hr => ?_) (Frame.mono P.frame fun r hr => ?_)
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · exact ⟨_, List.mem_cons_self, Env.range_sub (ap o ho).1⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp

/-- The modulus's width, read in the dispatch. -/
theorem pLen_word {s t : State} (F : CallFacts s) (I : EInv s t) :
    InRegions (t.rd ++ t.wr) (addr (arg s 7) 8) 4 ∧ t.mem.readW (addr (arg s 7) 8) 32 = BitVec.ofNat 32 (pLenOf s) :=
  stWord F I (d := 8) (by decide)

/-- After the dispatch's pointer to `state`. -/
structure DPtr (s t t₁ : State) : Prop where
  inv : EInv s t₁
  ebx : t₁.gpr .ebx = arg s 7
  mem : t₁.mem = t.mem
  edi : t₁.gpr .edi = t.gpr .edi
  esp : t₁.gpr .esp = t.gpr .esp
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  syms : t₁.syms = t.syms

theorem dPtr_ok {s t : State} (F : CallFacts s) (P : EPost s t) :
    WP isa (.block [.mov .ebx (.mem (VG.Impl.Mont.X86.Compact.arg 7))]) t (DPtr s t) :=
  wp_ldm (B := (callEnv s).sp) P.inv.esp (by rw [addrArg]; exact argAccess F P.inv (by decide)) fun t₁ u₁ =>
    WP.block_nil ⟨P.inv.regs u₁.mem (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.syms,
      by rw [u₁.gpr, addrArg, argValue F P.inv (by decide)], u₁.mem, u₁.other _ (by decide),
      u₁.other _ (by decide), u₁.rd, u₁.wr, u₁.syms⟩

/-- After the dispatch's reads of `state`: the seeds left in `fSeedLeft`, and
the modulus's width compared with 128. -/
structure DRead (s t t₅ : State) : Prop where
  base : Base (callEnv s) t₅
  left : t₅.mem.readW (off (callEnv s).base fSeedLeft) 32 = BitVec.ofNat 32 (callEnv s).k0
  cur : t₅.mem.readW (off (callEnv s).base fC) 32 = BitVec.ofNat 32 0
  status : t₅.mem.readW (off (callEnv s).base fStatus) 32 = BitVec.ofNat 32 0
  eax : t₅.gpr .eax = BitVec.ofNat 32 (pLenOf s)
  zf : isa.eval .e t₅ = some (decide (pLenOf s = 128))
  chg : (callEnv s).Chg [(fSeedLeft, 4)] t.mem t₅.mem
  esp : t₅.gpr .esp = t.gpr .esp
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr

theorem dRead_ok {s t t₁ : State} (F : CallFacts s) (P : EPost s t) (D : DPtr s t t₁) :
    WP isa (.block [.mov .eax (.mem (at_ .ebx 0)), .store (VG.Impl.Mont.X86.sc fSeedLeft) .eax,
      .mov .eax (.mem (at_ .ebx 8)), .alu .cmp .eax (.imm 128)]) t₁ (DRead s t) := by
  have v := F.valid
  have pl := F.pLens
  have sz := v.size_ge
  obtain W₀ := stWord F D.inv (d := 0) (by decide)
  obtain hs₁ := Scr.of_eq P.base.scr D.edi D.esp D.wr
  refine wp_ldm (B := arg s 7) D.ebx W₀.1 fun t₂ u₂ => st_ok (Scr.of_eq hs₁ (u₂.other _ (by decide))
    (u₂.other _ (by decide)) u₂.wr) (d := fSeedLeft) (by simp only [fSeedLeft, hdr]; omega_using [sz]) fun t₃ M₃ => ?_
  obtain e0 : (arg s 7).setWidth 64 + BitVec.ofNat 64 0 = (arg s 7).setWidth 64 := by simp
  obtain low : t₂.gpr .eax = BitVec.ofNat 32 (callEnv s).k0 := by rw [u₂.gpr, W₀.2, e0]; rfl
  obtain m₃ : t₃.mem = t.mem.writeW (off (callEnv s).base fSeedLeft) (BitVec.ofNat 32 (callEnv s).k0) := by
    rw [M₃.mem, u₂.mem, D.mem, low]
  obtain I₃ := D.inv.store F (o := fSeedLeft) (by decide) (v := t₂.gpr .eax) (by rw [M₃.mem, u₂.mem])
    (by rw [M₃.gpr, u₂.other _ (by decide)]) (by rw [M₃.rd, u₂.rd]) (by rw [M₃.wr, u₂.wr]) (by rw [M₃.syms, u₂.syms])
  obtain ebx₃ : t₃.gpr .ebx = arg s 7 := by rw [M₃.gpr, u₂.other _ (by decide), D.ebx]
  obtain W := pLen_word F I₃
  refine wp_ldm (B := arg s 7) ebx₃ W.1 fun t₄ u₄ => wp_cmpi fun t₅ f₅ _ z₅ => WP.block_nil ?_
  obtain eax : t₅.gpr .eax = BitVec.ofNat 32 (pLenOf s) := by rw [f₅.gpr, u₄.gpr, W.2]
  obtain mem₅ : t₅.mem = t₃.mem := by rw [f₅.mem, u₄.mem]
  obtain C : (callEnv s).Chg [(fSeedLeft, 4)] t.mem t₅.mem := by
    rw [mem₅, m₃]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) _
  obtain edi₅ : t₅.gpr .edi = t.gpr .edi := by
    rw [f₅.gpr, u₄.other _ (by decide), M₃.gpr, u₂.other _ (by decide), D.edi]
  obtain esp₅ : t₅.gpr .esp = t.gpr .esp := by
    rw [f₅.gpr, u₄.other _ (by decide), M₃.gpr, u₂.other _ (by decide), D.esp]
  obtain rd₅ : t₅.rd = t.rd := by rw [f₅.rd, u₄.rd, M₃.rd, u₂.rd, D.rd]
  obtain wr₅ : t₅.wr = t.wr := by rw [f₅.wr, u₄.wr, M₃.wr, u₂.wr, D.wr]
  obtain sy₅ : t₅.syms = t.syms := by rw [f₅.syms, u₄.syms, M₃.syms, u₂.syms, D.syms]
  obtain wd : ∀ d, d + 4 ≤ sState → (d + 4 ≤ fSeedLeft ∨ fSeedLeft + 4 ≤ d) →
      t₅.mem.readW (off (callEnv s).base d) 32 = t.mem.readW (off (callEnv s).base d) 32 := fun d h₁ h₂ => by
    rw [mem₅, m₃]; exact word_store_other v _ (by simp only [sState] at h₁; omega_using [sz, h₁])
      (by simp only [fSeedLeft, hdr]; omega_using [sz]) h₂ _
  obtain p32 : pLenOf s < 2 ^ 32 := by rcases pl with h | h | h <;> rw [h] <;> decide
  obtain cur : t₅.mem.readW (off (callEnv s).base fC) 32 = BitVec.ofNat 32 0 := by
    rw [wd _ (by simp only [fC, sState, hdr]; omega_using []) (.inr (by simp only [fC, fSeedLeft, hdr]; omega_using []))]
    exact P.cur
  obtain st : t₅.mem.readW (off (callEnv s).base fStatus) 32 = BitVec.ofNat 32 0 := by
    rw [wd _ (by simp only [fStatus, sState, hdr]; omega_using []) (.inr (by simp only [fStatus, fSeedLeft, hdr]; omega_using []))]
    exact P.status
  obtain B₅ := P.base.keep v C (fun o ho => by
    simp only [List.mem_singleton] at ho; subst ho; simp only [fSeedLeft, fOut, fUsedP, fWitLen, hdr]; omega_using [sz])
    edi₅ esp₅ rd₅ wr₅ sy₅
  refine ⟨B₅, by rw [mem₅, m₃, Mem.readW_writeW_self32], cur, st, eax, ?_, C, esp₅, rd₅, wr₅⟩
  show t₅.zf = _
  rw [z₅, show t₄.gpr .eax = BitVec.ofNat 32 (pLenOf s) by rw [← eax, f₅.gpr]]
  exact congrArg some (sub_beq (b := 128) p32 (by decide))

/-- The three geometries, by `state[1]`. -/
theorem dispatch_ok {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) {s t : State} (F : CallFacts s) (P : EPost s t) :
    WP isa (dispatch g1 g2 g3) t fun u =>
      ∃ g, (callEnv s).pLen = g.pLen ∧ (callEnv s).qLen = g.qLen ∧ GPost (callEnv s) g t u := by
  have v := F.valid
  have pl := F.pLens
  have sz := v.size_ge
  unfold dispatch
  simp only [seqs]
  refine WP.seq (WP.mono (dPtr_ok F P) fun t₁ D => ?_)
  refine WP.seq (WP.mono (dRead_ok F P D) fun t₅ R => ?_)
  have C := R.chg
  have eax := R.eax
  obtain stC : ∀ d, d + 8 ≤ 32 → t₅.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 =
      t.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 := fun d hd =>
    Frame.readW C (r := ⟨(callEnv s).stP + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Env.far_all ((v.stFar _ List.mem_cons_self).sub_left (Offset.sub_base _ hd))
        ((v.stFar _ (by simp)).sub_left (Offset.sub_base _ hd)) fun o ho => by
          simp only [List.mem_singleton] at ho; subst ho; simp only [fSeedLeft, hdr]; omega_using [sz]) (by decide)
  have run {t' : State} {g : Geo} (G : GeoOk g) (hp : (callEnv s).pLen = g.pLen) (hm : t'.mem = t₅.mem)
      (edi : t'.gpr .edi = t₅.gpr .edi) (esp : t'.gpr .esp = t₅.gpr .esp) (rd : t'.rd = t₅.rd)
      (wr : t'.wr = t₅.wr) (sy : t'.syms = t₅.syms) :
      WP isa g.generate t' fun u =>
        ∃ g, (callEnv s).pLen = g.pLen ∧ (callEnv s).qLen = g.qLen ∧ GPost (callEnv s) g t u := by
    obtain hq : (callEnv s).qLen = g.qLen := by
      have := G.lengths
      change pLenOf s = _ at hp
      change (if pLenOf s = 128 then 20 else 32) = _
      split <;> omega
    refine WP.mono (generate_ok G v hp hq (R.base.regs hm edi esp rd wr sy) (by rw [hm]; exact R.left)
      (by rw [hm]; exact R.cur) (by rw [hm]; exact R.status)) fun u Q => ?_
    refine ⟨g, hp, hq, ⟨Frame.trans (?_ : Frame _ t.mem t'.mem) Q.fr, Q.out, Q.st0, ?_, ?_, Q.st3, Q.used, Q.eax,
      Q.esp.trans (esp.trans R.esp), Q.rd.trans (rd.trans R.rd), Q.wr.trans (wr.trans R.wr)⟩⟩
    · rw [hm]
      exact Frame.sub C fun r hr => by
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
        rcases hr with ⟨o, ho, rfl⟩ | rfl
        · exact ⟨_, List.mem_cons_self, Env.range_sub (o := o) (by subst ho; simp only [fSeedLeft, hdr]; omega_using [sz])⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · rw [Q.st1, hm]; exact stC 8 (by omega_using [])
    · rw [Q.st2, hm]; exact stC 16 (by omega_using [])
  obtain p32 : pLenOf s < 2 ^ 32 := by rcases pl with h | h | h <;> rw [h] <;> decide
  refine WP.ite _ R.zf (fun h => run G1 (by rw [h1]; exact of_decide_eq_true h) rfl rfl rfl rfl rfl rfl)
    (fun h => ?_)
  obtain n128 : pLenOf s ≠ 128 := of_decide_eq_false h
  refine WP.seq (wp_cmpi fun t₆ f₆ _ z₆ => WP.block_nil ?_)
  obtain z256 : isa.eval .e t₆ = some (decide (pLenOf s = 256)) := by
    show t₆.zf = _
    rw [z₆, eax]
    exact congrArg some (sub_beq (b := 256) p32 (by decide))
  refine WP.ite _ z256 (fun h => run G2 (by rw [h2]; exact of_decide_eq_true h) f₆.mem (by rw [f₆.gpr])
    (by rw [f₆.gpr]) f₆.rd f₆.wr f₆.syms) (fun h => ?_)
  obtain n256 : pLenOf s ≠ 256 := of_decide_eq_false h
  exact run G3 (by rw [h3]; change pLenOf s = 384; omega_using [pl, n128, n256]) f₆.mem (by rw [f₆.gpr]) (by rw [f₆.gpr]) f₆.rd f₆.wr
    f₆.syms

theorem contains_nat {a x : Addr} {n : Nat} (fit : a.toNat + n ≤ 2 ^ 64) (h : (⟨a, n⟩ : Region).Contains x 1) :
    a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n := by
  change (x - a).toNat + 1 ≤ n at h
  rw [BitVec.toNat_sub] at h
  have := x.isLt
  have := a.isLt
  by_cases o : a.toNat ≤ x.toNat
  · rw [show 2 ^ 64 - a.toNat + x.toNat = (x.toNat - a.toNat) + 2 ^ 64 by omega_using [fit, h], Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_using [])] at h
    omega_using [h, o]
  · rw [Nat.mod_eq_of_lt (by omega_using [o])] at h
    omega_using [fit, h]

/-- What the contract's postcondition asks of the result, `out`, `used` and `state`. -/
def genQ (s : State) (m : Mem) (e : BitVec 32) : Prop :=
  let res := Spec.Dsa.parameterSearch (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat
    (s.mem.readW (BitVec.setWidth 64 (arg s 7)) 64).toNat
    (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (arg s 3)) (arg s 4).toNat)
  e.toNat = res.status ∧
    Spec.Rsa.bytesAt m (BitVec.setWidth 64 (arg s 0)) (arg s 1).toNat =
      (match res.outcome with
        | .accepted a => Spec.Dsa.encodeParams (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat
            (Spec.Dsa.generationQLen (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat) a
        | _ => List.replicate (arg s 1).toNat 0) ∧
    Spec.Rsa.wordsAt m (BitVec.setWidth 64 (arg s 2)) 1 = [BitVec.ofNat 64 res.used] ∧
    ∃ requested, Spec.Rsa.wordsAt m (BitVec.setWidth 64 (arg s 7)) 4 =
      [BitVec.ofNat 64 res.remaining,
        BitVec.ofNat 64 (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat,
        BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat),
        BitVec.ofNat 64 requested] ∧
      res.Requests (Spec.Dsa.parameterEntropy (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat) requested

theorem genQ_of {s : State} (F : CallFacts s) {g : Geo} (hp : (callEnv s).pLen = g.pLen)
    (hq : (callEnv s).qLen = g.qLen) {m : Mem} {e : BitVec 32}
    (out : Spec.Rsa.bytesAt m (callEnv s).out (2 * g.pLen + g.qLen) = outSpec g (sW (callEnv s)))
    (st0 : m.readW ((callEnv s).stP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW (callEnv s)).remaining)
    (st1 : m.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64 = s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64)
    (st2 : m.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64 =
      s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64)
    (st3 : m.readW ((callEnv s).stP + BitVec.ofNat 64 24) 64 =
      BitVec.ofNat 64 (requested (callEnv s).pLen (sW (callEnv s))))
    (used : m.readW ((callEnv s).usedP + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 (sW (callEnv s)).used)
    (eax : e = BitVec.ofNat 32 (sW (callEnv s)).status) : genQ s m e := by
  have pl := F.pLens
  obtain hpos : 0 < pLenOf s := by omega_using [pl]
  obtain lenOut : (arg s 1).toNat = 2 * g.pLen + g.qLen := by rw [F.outLen, ← hp, ← hq]; rfl
  refine ⟨?_, ?_, ?_, requested (pLenOf s) (sW (callEnv s)), ?_, requested_requests hpos _ _⟩
  · rw [eax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · rfl
    · show (sW (callEnv s)).status < 2 ^ 32
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
  · change Spec.Rsa.bytesAt m (callEnv s).out _ = _
    rw [lenOut, out, outSpec]
    have p2 : pLenOf s = g.pLen := hp
    have q3 : Spec.Dsa.generationQLen (pLenOf s) = g.qLen := hq
    show _ = match (sW (callEnv s)).outcome with
      | .accepted a => Spec.Dsa.encodeParams (pLenOf s) (Spec.Dsa.generationQLen (pLenOf s)) a
      | _ => List.replicate (2 * g.pLen + g.qLen) 0
    rw [q3, p2]
    rfl
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    exact congrArg (· :: []) used
  · have w8 : s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64 =
        BitVec.ofNat 64 (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
    have w16 : s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64 =
        BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (s.mem.readW (BitVec.setWidth 64 (arg s 7) + 8) 64).toNat) :=
      F.budget
    refine (show Spec.Rsa.wordsAt m (callEnv s).stP 4 = [m.readW ((callEnv s).stP + BitVec.ofNat 64 0) 64,
      m.readW ((callEnv s).stP + BitVec.ofNat 64 8) 64, m.readW ((callEnv s).stP + BitVec.ofNat 64 16) 64,
      m.readW ((callEnv s).stP + BitVec.ofNat 64 24) 64] from rfl).trans ?_
    exact List.cons_eq_cons.mpr ⟨st0, List.cons_eq_cons.mpr ⟨st1.trans w8,
      List.cons_eq_cons.mpr ⟨st2.trans w16, List.cons_eq_cons.mpr ⟨st3, rfl⟩⟩⟩⟩

/-- `state`'s words, apart from the entry's writes. -/
theorem stKeep {s t : State} (F : CallFacts s) (I : EInv s t) {d : Nat} (hd : d + 8 ≤ 32) :
    t.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 = s.mem.readW ((callEnv s).stP + BitVec.ofNat 64 d) 64 := by
  have fit := F.stFit
  obtain sub : (below (s.gpr .esp) 16).Sub (reservedRegion s) := by
    rw [F.reserved]; exact below_sub (by decide) F.low
  exact I.fr.readW (r := ⟨(arg s 7).setWidth 64 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact F.scrSt.symm.sub_left (Offset.sub_base _ hd)
    · exact (F.stackSt.symm.sub_right sub).sub_left (Offset.sub_base _ hd)) (by decide)

/-- The entry and the dispatch, inside the saved registers' frame. -/
theorem body_ok {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) {s : State} (F : CallFacts s) :
    WP isa (.seq (.block entry) (dispatch g1 g2 g3)) (entered s) fun t =>
      (∀ x, (⟨((entered s).gpr .esp).setWidth 64, 20⟩ : Region).Contains x 1 → t.mem x = (entered s).mem x) ∧
      genQ s t.mem (t.gpr .eax) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t := by
  have v := F.valid
  obtain I₀ := entered_inv F
  refine WP.seq (WP.mono (entry_ok F) fun t P => WP.mono (dispatch_ok G1 G2 G3 h1 h2 h3 F P)
    fun u ⟨g, hp, hq, Q⟩ => ⟨?_, genQ_of F hp hq Q.out Q.st0 (by rw [Q.st1, stKeep F P.inv (by decide)])
      (by rw [Q.st2, stKeep F P.inv (by decide)]) Q.st3 Q.used Q.eax, ?_, ?_, ?_⟩)
  · have fr : Frame [(callEnv s).scratchRegion, (callEnv s).stackRegion, (callEnv s).outRegion,
        (callEnv s).stRegion, (callEnv s).usedRegion] (entered s).mem u.mem :=
      Frame.trans (Frame.mono P.inv.fe fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self) Q.fr
    intro x hx
    rw [I₀.esp] at hx
    have spNat := F.spNat
    have low := F.low
    obtain esp := (s.gpr .esp).isLt
    have argsFit := F.argsFit
    obtain xr := contains_nat (by rw [toNat_wide]; omega_using []) hx
    rw [toNat_wide, spNat] at xr
    refine fr x fun r hr c => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have fit := F.scrFit
      have := contains_nat (a := (arg s 5).setWidth 64) (n := (arg s 6).toNat * 8)
        (by rw [toNat_wide]; omega_using []) c
      change ((arg s 5).setWidth 64).toNat ≤ _ ∧ _ < ((arg s 5).setWidth 64).toNat + (arg s 6).toNat * 8 at this
      rw [toNat_wide] at this
      have := F.scratchNat
      omega_arith
    · have sb : ((callEnv s).sp - BitVec.ofNat 32 200).toNat = (callEnv s).sp.toNat - 200 :=
        sub_toNat (by omega_using [spNat, low])
      have := contains_nat (a := ((callEnv s).sp - BitVec.ofNat 32 200).setWidth 64) (n := 200)
        (by rw [toNat_wide]; omega_using []) c
      rw [toNat_wide, sb, spNat] at this
      omega_using [low, xr, this]
    · rw [F.outRegion] at c
      have fit := F.outFit
      have := contains_nat (by rw [toNat_wide]; omega_using []) c
      rw [toNat_wide] at this
      have := F.outNat
      omega_arith
    · have fit := F.stFit
      have := contains_nat (a := (arg s 7).setWidth 64) (n := 32) (by rw [toNat_wide]; omega_using []) c
      rw [toNat_wide] at this
      have := F.stNat
      omega_arith
    · have fit := F.usedFit
      have := contains_nat (a := (arg s 2).setWidth 64) (n := 8) (by rw [toNat_wide]; omega_using []) c
      rw [toNat_wide] at this
      have := F.usedNat
      omega_arith
  · intro r hr
    cases r <;> simp at hr
    rw [Q.esp, P.inv.esp, I₀.esp]
  · rw [Q.rd, P.inv.rd, I₀.rd]
  · rw [Q.wr, P.inv.wr, I₀.wr]

theorem correct {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384)
    (hns : NoSp (.seq (.seq (.block entry) (dispatch g1 g2 g3)) (.block VG.Impl.Mont.X86.Compact.restoreRegs)))
    (s : State) (h : genContract.pre s) :
    ∃ trace t, Exec isa (code g1 g2 g3) s trace t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain F := call_facts h
  obtain ⟨trace, t, run, preserved, Q⟩ := frameWith_ok (Q := genQ s) hns (by have := F.low; omega_using [this])
    (by have := F.argsFit; omega_using [this]) (body_ok G1 G2 G3 h1 h2 h3 F)
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  exact Q

end VG.Proof.Dsa.X86.Generation
