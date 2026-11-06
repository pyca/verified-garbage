module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Search
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Dsa.X86.Generation.Copy
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base

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
  · simp [show i - 32 < 32 by omega]; congr 1; omega

theorem zero_half {x : Nat} (hx : x < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 x = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)]

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (show (x - a).toNat + 1 ≤ n by omega) (show (x - b).toNat + 1 ≤ k by omega)

theorem wide_narrow {P : Addr} (h : P.toNat < 2 ^ 32) : (P.setWidth 32).setWidth 64 = P := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

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
  have oL : E.outLen = 2 * g.pLen + g.qLen := by simp only [Env.outLen, hp, hq]
  have outW : (E.out.setWidth 32).setWidth 64 = E.out := wide_narrow op
  have outN : (E.out.setWidth 32).toNat = E.out.toNat := by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt op]
  have lenN : 2 * g.pLen + g.qLen < 2 ^ 32 := by omega
  unfold Geo.outPart
  simp only [seqs]
  refine WP.seq (cmpF_end B.scr (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega) hR.status
    (by rcases o with _ | _ | _ <;> simp [stOf]) (by decide) fun t₁ g₁ m₁ rd₁ wr₁ sy₁ z₁ => ?_)
  have hs₁ : Scr t₁ E.base E.size := Scr.of_eq B.scr (g₁ _ (by decide)) (g₁ _ (by decide)) wr₁
  refine WP.ite _ z₁ (fun h1 => ?_) (fun h1 => ?_)
  · -- p||q||g out.
    obtain ⟨a, u, rfl⟩ : ∃ a u, o = .found a u := by
      rcases o with ⟨a, u⟩ | _ | _
      · exact ⟨a, u, rfl⟩
      · simp [stOf] at h1
      · simp [stOf] at h1
    simp only [List.cons_append, List.nil_append]
    refine WP.seq (ld_ok hs₁ (r := .ebx) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      scr_ok fun t₃ e₃ g₃ m₃ rd₃ wr₃ sy₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_)
    have ebx₄ : t₄.gpr .ebx = E.out.setWidth 32 := by
      rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.gpr, m₁, B.outW]
    have esi₄ : t₄.gpr .esi = s.gpr .edi + BitVec.ofNat 32 sPk := by
      rw [u₄.other _ (by decide), e₃, u₂.other _ (by decide), g₁ _ (by decide)]
    have m₄ : t₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
    have rd₄ : t₄.rd = s.rd := by rw [u₄.rd, rd₃, u₂.rd, rd₁]
    have wr₄ : t₄.wr = s.wr := by rw [u₄.wr, wr₃, u₂.wr, wr₁]
    have hs := B.scr
    have pW := Scr.wide hs (d := sPk) (by simp only [sPk]; omega)
    have pN := Scr.toNat_add hs (d := sPk) (by simp only [sPk]; omega)
    refine VG.X86.WP.mono_syms (VG.Proof.Bignum.X86.copyBuffers_ok (src := s.gpr .edi + BitVec.ofNat 32 sPk)
      (dst := E.out.setWidth 32) (n := 2 * g.pLen + g.qLen) (by omega) lenN (by rw [pN]; simp only [sPk]; omega)
      (by rw [outN]; simp only [Env.outLen, hp, hq] at of; omega)
      (by rw [VG.Proof.Bignum.X86.byteAddr, pW, rd₄, wr₄]; exact hs.read (by simp only [sPk]; omega))
      (by rw [VG.Proof.Bignum.X86.byteAddr, outW, wr₄]
          exact ⟨_, B.out, by simp only [Env.outRegion, oL]; exact contains_start _ (Nat.le_refl _)⟩)
      (by rw [VG.Proof.Bignum.X86.byteAddr, pW, VG.Proof.Bignum.X86.byteAddr, outW]
          exact (v.outScratch.symm.sub_left (Offset.sub_base _ (by simp only [sPk]; omega))).sub_right
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
    have hn : outBytes g o = List.replicate (2 * g.pLen + g.qLen) 0 := by
      rcases o with _ | _ | _
      · simp [stOf] at h1
      · rfl
      · rfl
    rw [hn]
    refine WP.seq (ld_ok hs₁ (r := .esi) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      wp_movi fun t₃ u₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_)
    refine VG.X86.WP.mono_syms (VG.Proof.Dsa.X86.failureLoop_ok (out := E.out.setWidth 32)
      (len := 2 * g.pLen + g.qLen) (by omega) lenN (by rw [outN]; simp only [Env.outLen, hp, hq] at of; omega)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁, B.outW])
      (by rw [u₄.other _ (by decide), u₃.gpr]) u₄.gpr (fun i hi => by
        rw [u₄.wr, u₃.wr, u₂.wr, wr₁, outW]
        exact ⟨_, B.out, by simp only [Env.outRegion, oL]; exact Offset.contains_base _ (by omega) (by omega)⟩))
      fun t₅ ⟨V₅, _, O₅, K₅⟩ sy₅ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [outW] at V₅; exact V₅
    · rw [outW] at O₅
      intro x hx
      have hc := hx E.outRegion (List.mem_singleton_self _)
      have := O₅ x (.inr (by
        simp only [Region.Contains, Env.outRegion, oL] at hc
        show 0 + (2 * g.pLen + g.qLen) ≤ (x - E.out).toNat
        omega))
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
  have hP32 : P.toNat < 2 ^ 32 := by omega
  refine wp_storeS (a := P + BitVec.ofNat 64 d) ?_ ⟨R, hR, hc⟩ k
  show addr (s.gpr .ebx) d = _
  rw [hb, addr_eq (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hP32]; omega), wide_narrow hP32]

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
  have SU : E.stRegion.Disjoint E.usedRegion := (v.usedFar _ (by simp)).symm
  have sepSt : ∀ d n e, d + n ≤ 32 → e + 4 ≤ 32 → (d + n ≤ e ∨ e + 4 ≤ d) →
      Mem.Sep (E.stP + BitVec.ofNat 64 d) n (E.stP + BitVec.ofNat 64 e) 4 :=
    fun d n e h₁ h₂ h => Offset.sep _ h (by omega) (by omega)
  have sepSU : ∀ d n e, d + n ≤ 32 → e + 4 ≤ 8 →
      Mem.Sep (E.stP + BitVec.ofNat 64 d) n (E.usedP + BitVec.ofNat 64 e) 4 := fun d n e h₁ h₂ =>
    sep_of_disjoint ((SU.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂))
  have sepU : ∀ d e, d + 4 ≤ 8 → e + 4 ≤ 8 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      Mem.Sep (E.usedP + BitVec.ofNat 64 d) 4 (E.usedP + BitVec.ofNat 64 e) 4 :=
    fun d e h₁ h₂ h => Offset.sep _ h (by omega) (by omega)
  have sepUS : ∀ d e, d + 4 ≤ 8 → e + 4 ≤ 32 →
      Mem.Sep (E.usedP + BitVec.ofNat 64 d) 4 (E.stP + BitVec.ofNat 64 e) 4 := fun d e h₁ h₂ =>
    sep_of_disjoint ((SU.symm.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂))
  have cS : ∀ d, d + 4 ≤ 32 → E.stRegion.Contains (E.stP + BitVec.ofNat 64 d) 4 :=
    fun d h => Offset.contains_base _ h (by omega)
  have cU : ∀ d, d + 4 ≤ 8 → E.usedRegion.Contains (E.usedP + BitVec.ofNat 64 d) 4 :=
    fun d h => Offset.contains_base _ h (by omega)
  unfold Geo.results
  simp only [seqs]
  refine WP.seq (ld_ok B.scr (r := .ebx) (d := fStP) (by simp only [fStP, hdr]; omega) fun t₁ u₁ =>
    WP.block_nil ?_)
  have b₁ : t₁.gpr .ebx = E.stP.setWidth 32 := by rw [u₁.gpr, B.stPW]
  refine WP.seq (stB_ok (P := E.stP) (d := 0) b₁ (by omega) (by rw [u₁.wr]; exact B.stW) (cS 0 (by omega))
    fun t₂ M₂ => ?_)
  refine stB_ok (P := E.stP) (d := 24) (by rw [M₂.gpr]; exact b₁) (by omega) (by rw [M₂.wr, u₁.wr]; exact B.stW)
    (cS 24 (by omega)) fun t₃ M₃ => wp_movi fun t₄ u₄ => ?_
  have b₄ : t₄.gpr .ebx = E.stP.setWidth 32 := by rw [u₄.other _ (by decide), M₃.gpr, M₂.gpr, b₁]
  refine stB_ok (P := E.stP) (d := 4) b₄ (by omega) (by rw [u₄.wr, M₃.wr, M₂.wr, u₁.wr]; exact B.stW)
    (cS 4 (by omega)) fun t₅ M₅ => ?_
  refine stB_ok (P := E.stP) (d := 28) (by rw [M₅.gpr]; exact b₄) (by omega)
    (by rw [M₅.wr, u₄.wr, M₃.wr, M₂.wr, u₁.wr]; exact B.stW) (cS 28 (by omega)) fun t₆ M₆ => ?_
  have m₆ : t₆.mem = (((s.mem.writeW (E.stP + BitVec.ofNat 64 0) (BitVec.ofNat 32 k)).writeW
      (E.stP + BitVec.ofNat 64 24) (BitVec.ofNat 32 r)).writeW (E.stP + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW
      (E.stP + BitVec.ofNat 64 28) (0 : BitVec 32) := by
    simp only [M₆.mem, M₅.mem, u₄.mem, M₃.mem, M₂.mem, u₁.mem, M₅.gpr, u₄.gpr, M₂.gpr]
    rw [u₁.other .edx (by decide), u₁.other .ecx (by decide), hk, hr]
  have F₆ : Frame [E.stRegion, E.usedRegion] s.mem t₆.mem := by
    rw [m₆]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (cS 0 (by omega))).writeW List.mem_cons_self _
      (cS 24 (by omega))).writeW List.mem_cons_self _ (cS 4 (by omega))).writeW List.mem_cons_self _
      (cS 28 (by omega))
  have hs₆ : Scr t₆ E.base E.size := Scr.of_eq B.scr (by rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr,
    M₂.gpr, u₁.other _ (by decide)]) (by rw [M₆.gpr, M₅.gpr, u₄.other _ (by decide), M₃.gpr, M₂.gpr,
    u₁.other _ (by decide)]) (by rw [M₆.wr, M₅.wr, u₄.wr, M₃.wr, M₂.wr, u₁.wr])
  have scrApart : ∀ d, d + 4 ≤ E.size → ∀ r' ∈ [E.stRegion, E.usedRegion],
      (⟨off E.base d, 4⟩ : Region).Disjoint r' := fun d h r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ((v.stFar _ List.mem_cons_self).symm).sub_left (Offset.sub_base _ h)
    · exact ((v.usedFar _ List.mem_cons_self).symm).sub_left (Offset.sub_base _ h)
  refine ld_ok hs₆ (r := .ebx) (d := fUsedP) (by simp only [fUsedP, hdr]; omega) fun t₇ u₇ => WP.block_nil ?_
  have b₇ : t₇.gpr .ebx = E.usedP.setWidth 32 := by
    rw [u₇.gpr, F₆.readW (r := ⟨off E.base fUsedP, 4⟩) (Region.contains_self _ _)
      (scrApart _ (by simp only [fUsedP, hdr]; omega)) (by decide), B.usedPW]
  have wr₇ : t₇.wr = s.wr := by rw [u₇.wr, M₆.wr, M₅.wr, u₄.wr, M₃.wr, M₂.wr, u₁.wr]
  refine stB_ok (P := E.usedP) (d := 4) b₇ (by omega) (by rw [wr₇]; exact B.usedW) (cU 4 (by omega))
    fun t₈ M₈ => ?_
  have hs₈ : Scr t₈ E.base E.size := Scr.of_eq hs₆ (by rw [M₈.gpr, u₇.other _ (by decide)])
    (by rw [M₈.gpr, u₇.other _ (by decide)]) (by rw [M₈.wr, u₇.wr])
  have eax₄ : t₄.gpr .eax = 0 := u₄.gpr
  have m₈ : t₈.mem = t₆.mem.writeW (E.usedP + BitVec.ofNat 64 4) (0 : BitVec 32) := by
    rw [M₈.mem, u₇.mem, u₇.other .eax (by decide), M₆.gpr, M₅.gpr, eax₄]
  have F₈ : Frame [E.stRegion, E.usedRegion] s.mem t₈.mem := by
    rw [m₈]
    exact F₆.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (cU 4 (by omega))
  refine ld_ok hs₈ (r := .eax) (d := u) (by simp only [sState] at hu₂; omega) fun t₉ u₉ => ?_
  have eax₉ : t₉.gpr .eax = BitVec.ofNat 32 w := by
    rw [u₉.gpr, F₈.readW (r := ⟨off E.base u, 4⟩) (Region.contains_self _ _)
      (scrApart _ (by simp only [sState] at hu₂; omega)) (by decide), hw]
  refine stB_ok (P := E.usedP) (d := 0) (by rw [u₉.other _ (by decide), M₈.gpr]; exact b₇) (by omega)
    (by rw [u₉.wr, M₈.wr, wr₇]; exact B.usedW) (cU 0 (by omega)) fun t₁₀ M₁₀ => wp_movi fun t₁₁ u₁₁ =>
      WP.block_nil ?_
  have m₁₁' : t₁₁.mem = t₈.mem.writeW (E.usedP + BitVec.ofNat 64 0) (BitVec.ofNat 32 w) := by
    rw [u₁₁.mem, M₁₀.mem, u₉.mem, eax₉]
  have m₁₁ : t₁₁.mem = (t₆.mem.writeW (E.usedP + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW
      (E.usedP + BitVec.ofNat 64 0) (BitVec.ofNat 32 w) := by
    rw [m₁₁', m₈]
  have F : Frame [E.stRegion, E.usedRegion] s.mem t₁₁.mem := by
    rw [m₁₁']
    exact F₈.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (cU 0 (by omega))
  have rU : ∀ (m : Mem) d, d + 8 ≤ 32 → ((m.writeW (E.usedP + BitVec.ofNat 64 4) (0 : BitVec 32)).writeW
      (E.usedP + BitVec.ofNat 64 0) (BitVec.ofNat 32 w)).readW (E.stP + BitVec.ofNat 64 d) 64 =
      m.readW (E.stP + BitVec.ofNat 64 d) 64 := fun m d h => by
    rw [Mem.readW_writeW_sep (sepSU d 8 0 h (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSU d 8 4 h (by omega)) (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, F, u₁₁.gpr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₁, rU _ 0 (by omega), m₆, readW64_halves, VG.Offset.add_add,
      Mem.readW_writeW_sep (sepSt 4 4 28 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32,
      Mem.readW_writeW_sep (sepSt 0 4 28 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 0 4 4 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 0 4 24 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32, zero_half hkl]
  · rw [m₁₁, rU _ 8 (by omega), m₆,
      Mem.readW_writeW_sep (sepSt 8 8 28 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 8 8 4 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 8 8 24 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 8 8 0 (by omega) (by omega) (by omega)) (by decide)]
  · rw [m₁₁, rU _ 16 (by omega), m₆,
      Mem.readW_writeW_sep (sepSt 16 8 28 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 16 8 4 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 16 8 24 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 16 8 0 (by omega) (by omega) (by omega)) (by decide)]
  · rw [m₁₁, rU _ 24 (by omega), m₆, readW64_halves, VG.Offset.add_add, Mem.readW_writeW_self32,
      Mem.readW_writeW_sep (sepSt 24 4 28 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sepSt 24 4 4 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32, zero_half hrl]
  · rw [m₁₁, readW64_halves, VG.Offset.add_add,
      Mem.readW_writeW_sep (sepU 4 0 (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self32,
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
  have word : ∀ d, d + 4 ≤ E.size → t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 := fun d h =>
    F.readW (r := ⟨off E.base d, 4⟩) (Region.contains_self _ _) (fun r hr => (hd r hr).1.sub_left
      (Offset.sub_base _ h)) (by decide)
  have witEq : Spec.Rsa.bytesAt t.mem E.wit E.witLen = Spec.Rsa.bytesAt s.mem E.wit E.witLen :=
    VG.Proof.RsaKeyGen.frame_bytesAt F (fun r hr => (hd r hr).2.1) (by have := v.witFit; omega)
  refine ⟨Scr.of_eq B.scr edi sp wr, sp.trans B.sp, rd ▸ B.tapes, rd ▸ B.table, wr ▸ B.out, wr ▸ B.usedW,
    wr ▸ B.stW, sy ▸ B.syms, ?_, witEq.trans B.wit, (word fOut (by simp only [fOut, hdr]; omega)).trans B.outW,
    (word fUsedP (by simp only [fUsedP, hdr]; omega)).trans B.usedPW,
    (word fStP (by simp only [fStP, hdr]; omega)).trans B.stPW, (word fWit (by simp only [fWit, hdr]; omega)).trans B.witW,
    (word fWitLen (by simp only [fWitLen, hdr]; omega)).trans B.witLenW⟩
  intro c hc i hi
  have h := B.held c hc i hi
  simp only [VG.Impl.RsaKeyGen.TrialTable32.consts, List.mem_singleton] at hc
  subst hc
  rw [sy, ← h]
  simp only [B.syms]
  have := v.tableFit
  have len : i < 1024 := by simpa [VG.Impl.RsaKeyGen.TrialTable32.packed] using hi
  exact F.readW (r := E.tableRegion) (Offset.contains_base E.table (by omega) (by omega))
    (fun r hr => (hd r hr).2.2) (by decide)

/-- The controller's end is in `scratch`, which a frame apart from it keeps. -/
theorem SRes.frame {E : Env} {g : Geo} (G : GeoOk g) (v : E.Valid) {m m' : Mem} {rs : List Region}
    (F : Frame rs m m') (hd : ∀ r ∈ rs, E.scratchRegion.Disjoint r) {o : COut} (h : SRes E g m o) :
    SRes E g m' o := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have word : ∀ d, d + 4 ≤ E.size → m'.readW (off E.base d) 32 = m.readW (off E.base d) 32 := fun d h =>
    F.readW (r := ⟨off E.base d, 4⟩) (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
      (Offset.sub_base _ h)) (by decide)
  rcases o with ⟨a, u⟩ | c | ⟨j, c⟩
  · refine ⟨by rw [word _ (by simp only [fStatus, hdr]; omega)]; exact h.1, ?_,
      by rw [word _ (by simp only [fUsed, hdr]; omega)]; exact h.2.2.1, h.2.2.2⟩
    rw [VG.Proof.RsaKeyGen.frame_bytesAt F (fun r hr => (hd r hr).sub_left (Offset.sub_base _
      (show sPk + (2 * g.pLen + g.qLen) ≤ E.size by have := v.room; simp only [sPk]; omega))) (by omega)]
    exact h.2.1
  · exact ⟨by rw [word _ (by simp only [fStatus, hdr]; omega)]; exact h.1,
      by rw [word _ (by simp only [fC, hdr]; omega)]; exact h.2.1, h.2.2⟩
  · exact ⟨by rw [word _ (by simp only [fStatus, hdr]; omega)]; exact h.1,
      by rw [word _ (by simp only [fC, hdr]; omega)]; exact h.2.1,
      by rw [word _ (by simp only [fSeedLeft, hdr]; omega)]; exact h.2.2.1, h.2.2.2⟩

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
  have oL : E.outLen = 2 * g.pLen + g.qLen := by simp only [Env.outLen, hp, hq]
  have outFar : ∀ r ∈ [E.outRegion], E.scratchRegion.Disjoint r ∧ E.witRegion.Disjoint r ∧
      E.tableRegion.Disjoint r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨v.outScratch.symm, v.witFar.2.1, v.tableFar.2.1⟩
  unfold Geo.finish
  simp only [seqs]
  refine WP.seq (WP.mono (outPart_ok G v hp hq B hR) fun t₁ ⟨O₁, F₁, edi₁, esp₁, rd₁, wr₁, sy₁⟩ => ?_)
  have B₁ := B.frame v F₁ outFar edi₁ esp₁ rd₁ wr₁ sy₁
  have R₁ := hR.frame G v F₁ fun r hr => (outFar r hr).1
  have stF : ∀ r ∈ [E.stRegion, E.usedRegion], E.outRegion.Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (v.stFar _ (by simp)).symm
    · exact (v.usedFar _ (by simp)).symm
  -- After the words: `out` as it was, and the frame.
  have fin : ∀ {t₂ t : State} (m₂ : t₂.mem = t₁.mem) (e₂ : t₂.gpr .edi = t₁.gpr .edi)
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
    have stOut : ∀ d, d + 8 ≤ 32 → t₁.mem.readW (E.stP + BitVec.ofNat 64 d) 64 =
        s.mem.readW (E.stP + BitVec.ofNat 64 d) 64 := fun d h =>
      F₁.readW (r := ⟨E.stP + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ((v.stFar _ (by simp)).sub_left (Offset.sub_base _ h))) (by decide)
    refine ⟨?_, s0, by rw [s1, m₂, stOut 8 (by omega)], by rw [s2, m₂, stOut 16 (by omega)], s3, u, a, ?_,
      e.trans (e₂.trans edi₁), p.trans (p₂.trans esp₁), r.trans (r₂.trans rd₁), w.trans (w₂.trans wr₁),
      y.trans (y₂.trans sy₁)⟩
    · rw [VG.Proof.RsaKeyGen.frame_bytesAt F (fun r hr => by have := stF r hr; simpa [Env.outRegion, oL] using this)
        (by omega), m₂]
      exact O₁
    · refine Frame.trans (Frame.mono F₁ fun r hr => by simp at hr ⊢; exact .inl hr) ?_
      rw [← m₂]
      exact Frame.mono F fun r hr => by simp at hr ⊢; exact .inr hr
  have stLt : ∀ o : COut, stOf o < 2 ^ 32 := fun o => by rcases o with _ | _ | _ <;> simp [stOf]
  have budget : g.budget < 2 ^ 32 := by simp only [Geo.budget]; omega
  refine WP.seq (cmpF_end B₁.scr (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega) R₁.status (stLt o)
    (by decide) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ z₂ => ?_)
  have B₂ := B₁.regs m₂ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ sy₂
  have e₂ : t₂.gpr .edi = t₁.gpr .edi := g₂ _ (by decide)
  have p₂ : t₂.gpr .esp = t₁.gpr .esp := g₂ _ (by decide)
  -- `edx`, `ecx` and then the words.
  have words : ∀ {t₃ : State} {u val k r w : Nat},
      t₃.mem = t₁.mem → t₃.gpr .edi = t₁.gpr .edi → t₃.gpr .esp = t₁.gpr .esp → t₃.rd = t₁.rd →
      t₃.wr = t₁.wr → t₃.syms = t₁.syms → u + 4 ≤ sState →
      t₃.mem.readW (off E.base u) 32 = BitVec.ofNat 32 w → t₃.gpr .edx = BitVec.ofNat 32 k →
      t₃.gpr .ecx = BitVec.ofNat 32 r → k < 2 ^ 32 → r < 2 ^ 32 → w < 2 ^ 32 →
      k = (cRes E o).remaining → r = requested E.pLen (cRes E o) → w = (cRes E o).used →
      val = (cRes E o).status → WP isa (Geo.results u val) t₃ (FPost E g o s) := by
    intro t₃ u val k r w m₃ e₃ p₃ r₃ w₃ y₃ hu hw hk hr hkl hrl hwl ek er ew ev
    have B₃ := B₁.regs m₃ e₃ p₃ r₃ w₃ y₃
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
      (by rw [u₄.syms, u₃.syms, sy₂]) (by simp only [fUsed, sState, hdr]; omega)
      (by rw [u₄.mem, u₃.mem, m₂]; exact fu) (by rw [u₄.other _ (by decide), u₃.gpr]; rfl) (by rw [u₄.gpr]; rfl)
      (by decide) (by decide) (by omega) rfl rfl rfl rfl
  · -- No seeds left: exhausted.
    obtain ⟨st, cu, hc⟩ := R₁
    refine WP.ite _ z₂ (fun h => by simp [stOf] at h) (fun _ => ?_)
    refine WP.seq (cmpF_end B₂.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega) (by rw [m₂]; exact st)
      (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_)
    refine WP.ite _ z₃ (fun h => by simp at h) (fun _ => ?_)
    unfold Geo.exhausted
    refine WP.seq (wp_movi fun t₄ u₄ => wp_movi fun t₅ u₅ => WP.block_nil ?_)
    exact words (k := 0) (r := 0) (w := c) (by rw [u₅.mem, u₄.mem, m₃, m₂])
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), e₂])
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), p₂])
      (by rw [u₅.rd, u₄.rd, rd₃, rd₂]) (by rw [u₅.wr, u₄.wr, wr₃, wr₂]) (by rw [u₅.syms, u₄.syms, sy₃, sy₂])
      (by simp only [fC, sState, hdr]; omega) (by rw [u₅.mem, u₄.mem, m₃, m₂]; exact cu)
      (by rw [u₅.other _ (by decide), u₄.gpr]; rfl) (by rw [u₅.gpr]; rfl) (by decide) (by decide) (by omega)
      rfl rfl rfl rfl
  · -- `rand` ran out.
    obtain ⟨st, cu, lj, hc, hj⟩ := R₁
    have jl : j < 2 ^ 32 := by simp only [Spec.Dsa.parameterSeeds] at hj; omega
    refine WP.ite _ z₂ (fun h => by simp [stOf] at h) (fun _ => ?_)
    refine WP.seq (cmpF_end B₂.scr (o := fStatus) (v := 2) (by simp only [fStatus, hdr]; omega) (by rw [m₂]; exact st)
      (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_)
    have B₃ := B₂.regs m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃
    refine WP.ite _ z₃ (fun _ => ?_) (fun h => by simp at h)
    have mem₃ : t₃.mem = t₁.mem := by rw [m₃, m₂]
    have edi₃ : t₃.gpr .edi = t₁.gpr .edi := by rw [g₃ _ (by decide), e₂]
    have esp₃ : t₃.gpr .esp = t₁.gpr .esp := by rw [g₃ _ (by decide), p₂]
    unfold Geo.ranOut
    simp only [seqs]
    refine WP.seq (availCmp_ok v B₃ (c := c) (by rw [mem₃]; exact cu) hc (w := g.budget) budget
      fun t₄ g₄ m₄ rd₄ wr₄ sy₄ a₄ cf₄ => WP.block_nil ?_)
    have mem₄ : t₄.mem = t₁.mem := by rw [m₄, mem₃]
    have edi₄ : t₄.gpr .edi = t₁.gpr .edi := by rw [g₄ _ (by decide) (by decide), edi₃]
    have esp₄ : t₄.gpr .esp = t₁.gpr .esp := by rw [g₄ _ (by decide) (by decide), esp₃]
    have rd₄' : t₄.rd = t₁.rd := by rw [rd₄, rd₃, rd₂]
    have wr₄' : t₄.wr = t₁.wr := by rw [wr₄, wr₃, wr₂]
    have sy₄' : t₄.syms = t₁.syms := by rw [sy₄, sy₃, sy₂]
    have budE : g.budget = Spec.Dsa.parameterEntropy E.pLen := by simp only [Geo.budget, Spec.Dsa.parameterEntropy, hp]
    refine WP.ite _ cf₄ (fun hlt => ?_) (fun hge => ?_)
    · -- A request: twice the octets left, at least `256 p_len`, at most the budget.
      have lt : E.witLen - c < Spec.Dsa.parameterEntropy E.pLen := by rw [← budE]; exact of_decide_eq_true hlt
      have eR : cRes E (.ranOut j c) = ⟨.entropy j (E.witLen - c), c, []⟩ := by
        simp only [cRes, ranOutResult, show ¬ Spec.Dsa.parameterEntropy E.pLen ≤ E.witLen - c by omega, ↓reduceIte]
      have lb : 256 * g.pLen < 2 ^ 32 := by omega
      have lt' : E.witLen - c < 32769 * g.pLen := by
        have := lt; simp only [Spec.Dsa.parameterEntropy] at this; omega
      refine WP.seq (wp_cmpi fun t₅ f₅ c₅ _ => WP.block_nil ?_)
      have h₆ : WP isa (.ite .b (.block [.mov .eax (.imm (BitVec.ofNat 32 (256 * g.pLen)))]) (.block [])) t₅
          fun t => t.gpr .eax = BitVec.ofNat 32 (max (E.witLen - c) (256 * g.pLen)) ∧ t.mem = t₄.mem ∧
            (∀ r, r ≠ .eax → t.gpr r = t₄.gpr r) ∧ t.rd = t₄.rd ∧ t.wr = t₄.wr ∧ t.syms = t₄.syms :=
        WP.ite _ (show isa.eval .b t₅ = some (decide (E.witLen - c < 256 * g.pLen)) by
            show t₅.cf = _
            rw [c₅, a₄, toNat_ofNat_lt (by omega), toNat_ofNat_lt lb]) (fun h => wp_movi fun t₆ u₆ =>
              WP.block_nil ⟨by rw [u₆.gpr, Nat.max_eq_right (by have := of_decide_eq_true h; omega)], by
                rw [u₆.mem, f₅.mem], fun r hr => by rw [u₆.other _ hr, f₅.gpr], by rw [u₆.rd, f₅.rd],
                by rw [u₆.wr, f₅.wr], by rw [u₆.syms, f₅.syms]⟩)
            (fun h => WP.block_nil ⟨by rw [f₅.gpr, a₄, Nat.max_eq_left (by have := of_decide_eq_false h; omega)],
              f₅.mem, fun r _ => by rw [f₅.gpr], f₅.rd, f₅.wr, f₅.syms⟩)
      refine WP.seq (WP.mono h₆ fun t₆ h₆' => ?_)
      obtain ⟨a₆, m₆, g₆, rd₆, wr₆, sy₆⟩ := h₆'
      have mx : max (E.witLen - c) (256 * g.pLen) < 2 ^ 31 := by omega
      refine WP.seq (wp_add fun t₇ u₇ _ => wp_cmpi fun t₈ f₈ c₈ _ => WP.block_nil ?_)
      have a₇ : t₇.gpr .eax = BitVec.ofNat 32 (2 * max (E.witLen - c) (256 * g.pLen)) := by
        rw [u₇.gpr, a₆, ← BitVec.ofNat_add]; congr 1; omega
      have h₉ : WP isa (.ite .b (.block []) (.block [.mov .eax (.imm (BitVec.ofNat 32 g.budget))])) t₈
          fun t => t.gpr .eax = BitVec.ofNat 32 (min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget) ∧
            t.mem = t₄.mem ∧ (∀ r, r ≠ .eax → t.gpr r = t₄.gpr r) ∧ t.rd = t₄.rd ∧ t.wr = t₄.wr ∧
            t.syms = t₄.syms :=
        WP.ite _ (show isa.eval .b t₈ = some (decide (2 * max (E.witLen - c) (256 * g.pLen) < g.budget)) by
            show t₈.cf = _
            rw [c₈, a₇, toNat_ofNat_lt (by omega), toNat_ofNat_lt budget])
          (fun h => WP.block_nil ⟨by rw [f₈.gpr, a₇, Nat.min_eq_left (by have := of_decide_eq_true h; omega)],
            by rw [f₈.mem, u₇.mem, m₆], fun r hr => by rw [f₈.gpr, u₇.other _ hr, g₆ _ hr],
            by rw [f₈.rd, u₇.rd, rd₆], by rw [f₈.wr, u₇.wr, wr₆], by rw [f₈.syms, u₇.syms, sy₆]⟩)
          (fun h => wp_movi fun t₉ u₉ => WP.block_nil ⟨by
              rw [u₉.gpr, Nat.min_eq_right (by have := of_decide_eq_false h; omega)],
            by rw [u₉.mem, f₈.mem, u₇.mem, m₆], fun r hr => by rw [u₉.other _ hr, f₈.gpr, u₇.other _ hr, g₆ _ hr],
            by rw [u₉.rd, f₈.rd, u₇.rd, rd₆], by rw [u₉.wr, f₈.wr, u₇.wr, wr₆],
            by rw [u₉.syms, f₈.syms, u₇.syms, sy₆]⟩)
      refine WP.seq (WP.mono h₉ fun t₉ h₉' => ?_)
      obtain ⟨a₉, m₉, g₉, rd₉, wr₉, sy₉⟩ := h₉'
      have rq : requested E.pLen (cRes E (.ranOut j c)) = min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget := by
        rw [eR]
        simp only [requested, VG.Proof.Entropy.requested, parameterRequest, VG.Proof.Entropy.request,
          Spec.Dsa.parameterEntropy, Geo.budget, hp]
      have rql : min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget < 2 ^ 32 := by omega
      refine WP.seq (wp_mov fun t₁₀ u₁₀ => ld_ok (Scr.of_eq B₃.scr (by rw [u₁₀.other _ (by decide), g₉ _ (by decide),
          g₄ _ (by decide) (by decide)]) (by rw [u₁₀.other _ (by decide), g₉ _ (by decide),
          g₄ _ (by decide) (by decide)]) (by rw [u₁₀.wr, wr₉, wr₄])) (r := .edx) (d := fSeedLeft)
        (by simp only [fSeedLeft, hdr]; omega) fun t₁₁ u₁₁ => WP.block_nil ?_)
      exact words (k := j) (r := min (2 * max (E.witLen - c) (256 * g.pLen)) g.budget) (w := c)
        (by rw [u₁₁.mem, u₁₀.mem, m₉, mem₄])
        (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide), edi₄])
        (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide), esp₄])
        (by rw [u₁₁.rd, u₁₀.rd, rd₉, rd₄']) (by rw [u₁₁.wr, u₁₀.wr, wr₉, wr₄']) (by rw [u₁₁.syms, u₁₀.syms, sy₉, sy₄'])
        (by simp only [fC, sState, hdr]; omega) (by rw [u₁₁.mem, u₁₀.mem, m₉, mem₄]; exact cu)
        (by rw [u₁₁.gpr, u₁₀.mem, m₉, mem₄]; exact lj) (by rw [u₁₁.other _ (by decide), u₁₀.gpr, a₉]) jl rql (by omega)
        (by rw [eR]; rfl) rq.symm (by rw [eR]) (by rw [eR]; rfl)
    · -- Exhausted: the octets left reach the budget.
      have ge : Spec.Dsa.parameterEntropy E.pLen ≤ E.witLen - c := by
        rw [← budE]; have := of_decide_eq_false hge; omega
      have eR : cRes E (.ranOut j c) = ⟨.exhausted, c, []⟩ := by simp only [cRes, ranOutResult, ge, ↓reduceIte]
      unfold Geo.exhausted
      refine WP.seq (wp_movi fun t₅ u₅ => wp_movi fun t₆ u₆ => WP.block_nil ?_)
      exact words (k := 0) (r := 0) (w := c) (by rw [u₆.mem, u₅.mem, mem₄])
        (by rw [u₆.other _ (by decide), u₅.other _ (by decide), edi₄])
        (by rw [u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
        (by rw [u₆.rd, u₅.rd, rd₄']) (by rw [u₆.wr, u₅.wr, wr₄']) (by rw [u₆.syms, u₅.syms, sy₄'])
        (by simp only [fC, sState, hdr]; omega) (by rw [u₆.mem, u₅.mem, mem₄]; exact cu)
        (by rw [u₆.other _ (by decide), u₅.gpr]; rfl) (by rw [u₆.gpr]; rfl) (by decide) (by decide) (by omega)
        (by rw [eR]; rfl) (by rw [eR]; rfl) (by rw [eR]) (by rw [eR]; rfl)

end VG.Proof.Dsa.X86.Generation
