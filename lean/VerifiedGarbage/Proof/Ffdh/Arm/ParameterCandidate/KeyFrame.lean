module

public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ffdh.Arm.ParameterCandidate.KeyReady`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.KeyView`, which this module and modules that import it used -/

section

/-! View the same Montgomery arrays through RSA's native key-operation
helpers. The 96-byte base adjustment aligns their 160-byte header with
the Montgomery header's 256 bytes. Two extra native words stay explicit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont

theorem keyView_stride (w : Nat) : VG.Proof.Rsa.Arm.Keys.S (2 * w + 2) = 8 * (w + 2) := by
  simp only [VG.Proof.Rsa.Arm.Keys.S]
  omega_using []

theorem keyView_array (w j : Nat) :
    96 + VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j = Proof.Rsa.Mont.arrAt w j := by
  change 96 + (160 + j * VG.Proof.Rsa.Arm.Keys.S (2 * w + 2)) = 256 + j * (8 * (w + 2))
  rw [keyView_stride]
  omega_using []

theorem keyView_number (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32) :
    VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j =
      Proof.Rsa.Mont.numAt m (State.addr base) w j +
        2 ^ (64 * w) * val32 m (State.addr base) (Proof.Rsa.Mont.arrAt w j + 8 * w) 2 := by
  unfold VG.Proof.Rsa.Arm.Keys.num
  rw [VG.Arm.addr_add fits, VG.Proof.Rsa.Arm.CrtValues.val32_off, keyView_array, val32_append,
    VG.Proof.Bignum.Arm.numAt_native,
    show 32 * (2 * w) = 64 * w by omega_using [], show 4 * (2 * w) = 8 * w by omega_using []]

theorem keyView_low (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32) :
    val32 m (State.addr (base + 96#32)) (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j) (2 * w) =
      Proof.Rsa.Mont.numAt m (State.addr base) w j := by
  rw [VG.Arm.addr_add fits, VG.Proof.Rsa.Arm.CrtValues.val32_off, keyView_array,
    VG.Proof.Bignum.Arm.numAt_native]

theorem numAt_lt (m : Mem) (base : Addr) (w j : Nat) :
    Proof.Rsa.Mont.numAt m base w j < 2 ^ (64 * w) := by
  have bound := (m.read (base + BitVec.ofNat 64 (Proof.Rsa.Mont.arrAt w j)) (8 * w)).isLt
  change _ < 2 ^ (8 * (8 * w)) at bound
  simpa only [Proof.Rsa.Mont.numAt, show 8 * (8 * w) = 64 * w by omega_using []] using bound

theorem keyView_number_mod (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32) :
    VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j % 2 ^ (64 * w) =
      Proof.Rsa.Mont.numAt m (State.addr base) w j := by
  rw [keyView_number m base w j fits, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (numAt_lt m (State.addr base) w j)]

theorem keyView_number_low (m : Mem) (base : BitVec 32) (w j : Nat)
    (fits : base.toNat + 96 < 2 ^ 32)
    (small : VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j < 2 ^ (64 * w)) :
    Proof.Rsa.Mont.numAt m (State.addr base) w j =
      VG.Proof.Rsa.Arm.Keys.num m (base + 96#32) (2 * w + 2) j := by
  have split := keyView_number m base w j fits
  have top : val32 m (State.addr base) (Proof.Rsa.Mont.arrAt w j + 8 * w) 2 = 0 := by
    by_contra nonzero
    have scale := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤
      val32 m (State.addr base) (Proof.Rsa.Mont.arrAt w j + 8 * w) 2 by omega_using [nonzero])
    rw [Nat.mul_one] at scale
    omega_using [small, split, scale]
  rw [top, Nat.mul_zero, Nat.add_zero] at split
  exact split.symm

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.KeyContext`, which only this module used -/

section

/-! Bind RSA's native key-array registers to FFDH's existing Montgomery
allocation. Register setup changes neither memory nor argument slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

private theorem nativeKeyWords (w : Nat) :
    (BitVec.ofNat 32 w <<< 1) + 2 = BitVec.ofNat 32 (2 * w + 2) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 w * BitVec.ofNat 32 2 + BitVec.ofNat 32 2 = _
  rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  congr 1
  omega_using []

private theorem nativeKeyStride (w : Nat) :
    (BitVec.ofNat 32 (2 * w + 2) + 2) <<< 2 = BitVec.ofNat 32 (8 * (w + 2)) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change (BitVec.ofNat 32 (2 * w + 2) + BitVec.ofNat 32 2) * BitVec.ofNat 32 4 = _
  rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat]
  congr 1
  omega_using []

theorem keyContext_ok (s : State) (base : BitVec 32) (w : Nat)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (saved : s.mem.readW (State.addr s.sp) 32 = base)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (base + 48#32)) 4)
    (width : s.mem.readW (State.addr (base + 48#32)) 32 = BitVec.ofNat 32 w) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext) s fun t =>
      (t.gpr .r0 = base ∧ t.gpr .r8 = base + 96#32 ∧
        t.gpr .r9 = BitVec.ofNat 32 (2 * w + 2) ∧ t.gpr .r7 = BitVec.ofNat 32 (8 * (w + 2)) ∧
        t.mem = s.mem) ∧ Rest [.r0, .r7, .r8, .r9] s t := by
  refine withRest_all [.r0, .r7, .r8, .r9] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext VG.Impl.Rsa.Arm.Keys.stride
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, readBase, saved, readWidth, width,
    nativeKeyWords w, nativeKeyStride w, show (96 : BitVec 32) = 96#32 from rfl]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Select the same arrays through RSA's proved native key-operation view. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/KeyViewExec.lean`, which only this module imported.
section

/-! RSA's native key helpers use a header view beginning 96 bytes into the
same scratch allocation. Narrowing permissions makes their existing proofs
callable without granting access to a single byte outside that allocation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def keyViewRegion (base : BitVec 32) (capacity : Nat) : Region :=
  ⟨State.addr (base + 96#32), 8 * capacity - 96⟩

theorem keyView_covers {s : State} {base : BitVec 32} {capacity : Nat}
    (h : Workspace s base (8 * capacity)) (large : 96 < 8 * capacity) :
    Covers [keyViewRegion base capacity] s.wr := by
  apply Covers.of_sub
  intro r member
  rw [List.mem_singleton] at member
  subst r
  refine ⟨⟨State.addr base, 8 * capacity⟩, h.writable, 96, ?_, by simp only [keyViewRegion]; omega_using [large]⟩
  exact VG.Arm.addr_add (by have := h.nowrap; omega_using [large, this])

theorem keyView_dimensions {k capacity : Nat} (minLength : 64 ≤ k) (maxLength : k ≤ 1024)
    (space : Spec.Rsa.scratchWords k ≤ capacity) :
    0 < 2 * ((k + 7) / 8) + 2 ∧ 2 * ((k + 7) / 8) + 2 ≤ 1024 ∧
      160 + 30 * (4 * (2 * ((k + 7) / 8) + 4)) ≤ 8 * capacity - 96 := by
  simp only [Spec.Rsa.scratchWords] at space
  omega_using [minLength, maxLength, space]

theorem keyView_inline {c : Prog isa} {s : State} {base : BitVec 32} {capacity : Nat}
    {P Q : State → Prop} (workspace : Workspace s base (8 * capacity)) (large : 96 < 8 * capacity)
    (proof : WP isa c (s.withRegions s.rd [keyViewRegion base capacity]) P)
    (noCalls : c.noCalls = true)
    (done : ∀ t, t.rd = s.rd → t.wr = s.wr →
      Frame [keyViewRegion base capacity] s.mem t.mem →
      P (t.withRegions s.rd [keyViewRegion base capacity]) → Q t) : WP isa c s Q := by
  have writes := keyView_covers workspace large
  exact regionModel.wp_narrow proof ((Covers.refl s.rd).append writes) writes
    (Code.noFrames_of_noCalls noCalls) (.inl noCalls) (fun _ t _ rd wr frame post => done t rd wr frame post)

theorem rest_of_keyView {s t : State} {rs : List Reg} {base : BitVec 32} {capacity : Nat}
    (h : Rest rs (s.withRegions s.rd [keyViewRegion base capacity])
      (t.withRegions s.rd [keyViewRegion base capacity]))
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Rest rs s t := ⟨h.gpr, rd, wr, h.sp⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def KeyReady (base : BitVec 32) (capacity w : Nat) (s : State) : Prop :=
  VG.Proof.Rsa.Arm.Keys.Ws (s.withRegions s.rd [keyViewRegion base capacity])
    (base + 96#32) (8 * capacity - 96) (2 * w + 2) 30

theorem KeyReady.rest {s t : State} {base : BitVec 32} {capacity w : Nat} {rs : List Reg}
    (h : KeyReady base capacity w s) (rest : Rest rs s t)
    (r7 : .r7 ∉ rs) (r8 : .r8 ∉ rs) (r9 : .r9 ∉ rs) : KeyReady base capacity w t :=
  h.of (rest.gpr _ r7) (rest.gpr _ r8) (rest.gpr _ r9) rfl

theorem keyContext_ready (s : State) {base : BitVec 32} {capacity k : Nat}
    (workspace : Workspace s base (8 * capacity))
    (data : MontData base capacity (VG.Spec.Rsa.modulusWords k) s.mem)
    (minLength : 64 ≤ k) (maxLength : k ≤ 1024) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext) s fun t =>
      KeyReady base capacity (VG.Spec.Rsa.modulusWords k) t ∧ t.gpr .r0 = base ∧ t.mem = s.mem ∧
        Rest [.r0, .r7, .r8, .r9] s t := by
  have dims := keyView_dimensions minLength maxLength space
  have capLarge : 96 < 8 * capacity := by
    have := minLength
    simp only [Spec.Rsa.scratchWords] at space
    omega_using [space]
  have shiftFits : base.toNat + 96 < 2 ^ 32 := by have := workspace.nowrap; omega_using [dims, this]
  have shifted : (base + 96#32).toNat = base.toNat + 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 96 < 2 ^ 32),
      Nat.mod_eq_of_lt shiftFits]
  have native := nativeHeader_of_layout s.mem base workspace.nowrap (Nat.le_refl _) data.layout
  rw [data.width] at native
  have readWidth : InRegions (s.rd ++ s.wr) (State.addr (base + 48#32)) 4 := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; omega_using [shiftFits])]
    exact workspace.read (by omega_using [dims])
  have width : s.mem.readW (State.addr (base + 48#32)) 32 = BitVec.ofNat 32 (VG.Spec.Rsa.modulusWords k) := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; omega_using [shiftFits])]
    exact native.count
  refine WP.mono (keyContext_ok s base (VG.Spec.Rsa.modulusWords k) readBase saved readWidth width) ?_
  rintro t ⟨⟨ptr, r8, r9, r7, mem⟩, rest⟩
  refine ⟨?_, ptr, mem, rest⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, r8, r9⟩
  · rw [shifted]
    have := workspace.nowrap
    omega_using [dims, this]
  · exact List.mem_cons_self
  · exact dims.2.2
  · exact dims.1
  · exact dims.2.1
  · change t.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Rsa.Arm.Keys.S (2 * VG.Spec.Rsa.modulusWords k + 2))
    rw [keyView_stride]
    exact r7

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Translate RSA key-array frames back to the shared Montgomery arrays. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt)

def keyArrayRegions (base : BitVec 32) (w : Nat) (js : List Nat) : List Region :=
  js.map fun j => ⟨off (State.addr base) (arrAt w j), 8 * (w + 2)⟩

theorem KeyReady.arrayFit {s : State} {base : BitVec 32} {capacity w j : Nat}
    (h : KeyReady base capacity w s) (bound : j < 30) :
    arrAt w j + 8 * (w + 2) ≤ 8 * capacity := by
  have native := h.arr_fit bound
  rw [keyView_stride] at native
  rw [← keyView_array w j]
  have stridePositive : 16 ≤ 8 * (w + 2) := by omega_using []
  omega_using [native]

theorem KeyReady.arraysFit {s : State} {base : BitVec 32} {capacity w j : Nat}
    (h : KeyReady base capacity w s) (bound : j < 30) : arrAt w (j + 1) ≤ 8 * capacity := by
  have fit := h.arrayFit bound
  have next : arrAt w (j + 1) = arrAt w j + 8 * (w + 2) := by
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  rw [next]
  exact fit

theorem KeyReady.baseShiftFits {s : State} {base : BitVec 32} {capacity w : Nat}
    (h : KeyReady base capacity w s) (workspace : Workspace s base (8 * capacity)) :
    base.toNat + 96 < 2 ^ 32 := by
  have fit := h.arrayFit (j := 0) (by decide)
  have nowrap := workspace.nowrap
  simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
  omega_using [nowrap, fit]

theorem key_keep_number {s : State} {base : BitVec 32} {capacity w j : Nat}
    {js : List Nat} {m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bound : j < 30) (unchanged : ∀ a ∈ js, a ≠ j)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    numAt m' (State.addr base) w j = numAt s.mem (State.addr base) w j := by
  have value := keep.num unchanged (by simp) (ready.fit64 bound)
  have fits := ready.baseShiftFits workspace
  rw [← keyView_number_mod m' base w j fits, ← keyView_number_mod s.mem base w j fits, value]

theorem key_keep_frame {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat} {m m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (h : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] m m') :
    Frame (keyArrayRegions base w js) m m' := by
  have zeroFit := h.arrayFit (j := 0) (by decide)
  have shiftFits : base.toNat + 96 < 2 ^ 32 := by
    have := workspace.nowrap
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at zeroFit
    omega_using [this, zeroFit]
  change Outs (State.addr (base + 96#32)) (VG.Proof.Rsa.KeyWorkspace.ranges (2 * w + 2) js []) m m' at keep
  have native := VG.Proof.Bignum.outs_frame keep (by
    intro r hr
    simp only [VG.Proof.Rsa.KeyWorkspace.ranges, List.map_nil, List.append_nil, List.mem_map] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    exact h.fit64 (bounds j hj))
  have address (j : Nat) : off (State.addr (base + 96#32)) (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j) =
      off (State.addr base) (arrAt w j) := by
    unfold off
    rw [VG.Arm.addr_add shiftFits, BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
  simp only [VG.Proof.Rsa.KeyWorkspace.ranges, List.map_nil, List.append_nil, List.map_map] at native
  have equal : (js.map fun j => (⟨off (State.addr (base + 96#32))
      (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j), VG.Proof.Rsa.Arm.Keys.S (2 * w + 2)⟩ : Region)) =
      keyArrayRegions base w js := by
    unfold keyArrayRegions
    apply List.map_congr_left
    intro j _
    rw [address, keyView_stride]
  change Frame (js.map fun j => ⟨off (State.addr (base + 96#32))
    (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j), VG.Proof.Rsa.Arm.Keys.S (2 * w + 2)⟩) m m' at native
  rw [equal] at native
  exact native

theorem keyArrayRegions.header {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat}
    (workspace : Workspace s base (8 * capacity)) (h : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30) :
    ∀ r ∈ keyArrayRegions base w js, (⟨State.addr base, 128⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have fit := h.arrayFit (bounds j hj)
  have nowrap := workspace.nowrap
  apply Region.Disjoint.symm
  apply Offset.disjoint_base
  · simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega_using []
  · omega_using [fit, nowrap]

theorem key_keep_workspace {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat} {m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    Frame [⟨State.addr base, 8 * capacity⟩] s.mem m' := by
  refine (key_keep_frame workspace ready bounds keep).sub ?_
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact ⟨_, by simp, Offset.sub_base _ (ready.arrayFit (bounds j hj))⟩

theorem key_keep_header {s : State} {base : BitVec 32} {capacity w d : Nat}
    {js : List Nat} {m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30) (fit : d + 8 ≤ 256)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    m'.readW (off (State.addr base) d) 64 = s.mem.readW (off (State.addr base) d) 64 := by
  refine (key_keep_frame workspace ready bounds keep).readW (r := ⟨State.addr base, 256⟩)
    (Offset.contains_base _ fit (by omega_using [fit])) ?_ (by decide)
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have arrayFit := ready.arrayFit (bounds j hj)
  have nowrap := workspace.nowrap
  apply Region.Disjoint.symm
  apply Offset.disjoint_base
  · simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega_using []
  · omega_using [arrayFit, nowrap]

theorem keyArrayRegions.modulus {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat}
    (workspace : Workspace s base (8 * capacity)) (h : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30) (nonzero : ∀ j ∈ js, j ≠ 0) :
    ∀ r ∈ keyArrayRegions base w js,
      (⟨off (State.addr base) (arrAt w 0), 8 * w⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have fit := h.arrayFit (bounds j hj)
  have fit0 := h.arrayFit (j := 0) (by decide)
  have nowrap := workspace.nowrap
  refine Offset.disjoint _ (.inl ?_) (by omega_using [fit0, nowrap]) (by omega_using [fit, nowrap])
  have positive : 1 ≤ j := by have := nonzero j hj; omega_using [this]
  have scale := Nat.mul_le_mul_right (8 * (w + 2)) positive
  simp only [Nat.one_mul] at scale
  simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero]
  omega_using [scale]

theorem MontData.after_key_keep {s : State} {base : BitVec 32} {capacity w : Nat}
    {js : List Nat} {m' : Mem}
    (data : MontData base capacity w s.mem) (workspace : Workspace s base (8 * capacity))
    (ready : KeyReady base capacity w s) (bounds : ∀ j ∈ js, j < 30)
    (nonzero : ∀ j ∈ js, j ≠ 0)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    MontData base capacity w m' ∧ numAt m' (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 :=
  data.after_frame (key_keep_frame workspace ready bounds keep)
    (keyArrayRegions.header workspace ready bounds) (keyArrayRegions.modulus workspace ready bounds nonzero)

end VG.Proof.Ffdh.Arm.ParameterCandidate
