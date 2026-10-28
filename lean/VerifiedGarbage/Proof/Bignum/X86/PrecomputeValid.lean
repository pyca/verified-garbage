module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInputs
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.In
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Mul
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Copy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Set

/-! # The precomputation of a valid modulus at a run-time width

`valid` (`Impl/Bignum/X86/PrecomputeFn.lean`) writes `M` and `R² mod M` to
`pre` and returns 1 (`precomputeValid_ok`), changing memory only in the
working space past its header, `pre`, the 96 bytes below `esp` that the
calls use and the argument it overwrites (`PrecomputePost`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt
open VG.Proof.Bignum.X86.PrecomputeRt
open VG.Proof.Dsa.X86 (stackAddress stackValue)

/-- The result, and the regions of memory a run changes. -/
def PrecomputePost (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (mem : Mem)
    (t : State) : Prop :=
  (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt mem (byteAddr (args 2)) len) with
  | some ws => t.gpr .eax = 1 ∧ Spec.Rsa.wordsAt t.mem (byteAddr (args 0)) (2 * Spec.Rsa.modulusWords len) = ws
  | none => t.gpr .eax = 0 ∧ Spec.Rsa.wordsAt t.mem (byteAddr (args 0)) (2 * Spec.Rsa.modulusWords len) =
      List.replicate (2 * Spec.Rsa.modulusWords len) 0) ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), 16 * Spec.Rsa.modulusWords len⟩, below sp 96,
    ⟨addr sp 8, 4⟩] mem t.mem

/-- The arguments once `pre_len` is `n_len`. -/
def pcArgs (len : Nat) (args : Nat → BitVec 32) (i : Nat) : BitVec 32 :=
  if i = 1 then BitVec.ofNat 32 len else args i

/-- The bytes of a region apart from the regions a frame changes. -/
theorem pcBytesAt_frame {rs : List Region} {m m' : Mem} (F : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have hl := List.mem_range.mp hi
  exact F _ fun r hr => hd r hr _ (Offset.contains_base p (by omega) (by omega))

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem pcStackAddress_eq (h : PrecomputeInputs base bytes len args s) {i : Nat} (hi : i < 6) :
    stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_eq (by have := h.top; omega)

theorem pcSetWidth_ok (h : PrecomputeInputs base bytes len args s) :
    WP isa (.block PrecomputeFn.setWidth) s fun u =>
      PcIn base bytes len (pcArgs len args) u ∧ Frame [⟨addr (s.gpr .esp) 8, 4⟩] s.mem u.mem ∧
      Keeps [.eax] s u := by
  have top := h.top
  unfold PrecomputeFn.setWidth
  refine wp_movS (h.stack 3 (by decide)).readSrc fun u₁ e₁ _ => ?_
  have sp₁ : u₁.gpr .esp = s.gpr .esp := e₁.other _ (by decide)
  have ea : u₁.ea (argAt 0 1) = stackAddress s 1 := by
    simp only [stackAddress, ← sp₁]; rfl
  refine wp_storeS ea (by rw [e₁.wr]; exact h.argWrite) fun u m => WP.block_nil ?_
  have K : Keeps [.eax] s u := e₁.keeps.trans (m.keeps _)
  have esp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have eax : u₁.gpr .eax = BitVec.ofNat 32 len := by rw [e₁.gpr, h.nLen]
  have mu : u.mem = s.mem.writeW (stackAddress s 1) (BitVec.ofNat 32 len) := by rw [m.mem, e₁.mem, eax]
  have sa : ∀ i, stackAddress u i = stackAddress s i := fun i => by simp only [stackAddress, esp]
  have W : 16 * Spec.Rsa.modulusWords len = 2 * wb len := by simp only [wb]; omega
  refine ⟨⟨h.scratch.of_keeps K (by decide) (by decide), h.lower, h.upper, h.space, fun i hi => ?_,
    by simp [pcArgs], by simp only [pcArgs]; exact h.nLen, by simp only [pcArgs]; exact h.hbase,
    by simp only [pcArgs]; exact h.hbytes, by simp only [pcArgs, ← W]; exact h.outFit,
    by simp only [pcArgs]; exact h.nFit, by simp only [pcArgs, ← W]; rw [K.2.2]; exact h.outWrite,
    by simp only [pcArgs]; rw [K.2.1, K.2.2]; exact h.nRead, by simp only [pcArgs, ← W]; exact h.outApart.symm,
    by simp only [pcArgs]; exact h.nApart, by simp only [pcArgs, ← W, argAddr, esp]; exact h.outArgs⟩, ?_, K⟩
  · refine ⟨(h.stack i hi).stack.keep K (by decide), ?_⟩
    unfold stackValue
    rw [sa, mu]
    by_cases hi1 : i = 1
    · subst hi1
      rw [Mem.readW_writeW_self32]; simp [pcArgs]
    · rw [Mem.readW_writeW_sep, show pcArgs len args i = args i by simp [pcArgs, hi1]]
      · exact (h.stack i hi).value
      · rw [pcStackAddress_eq h hi, pcStackAddress_eq h (by decide)]
        exact Offset.sep _ (by omega) (by omega) (by omega)
      · decide
  · rw [mu]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    exact Region.contains_self _ _

end

/-- What `start` leaves for the squares. -/
structure PcStarted (s : State) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (M : Nat) (t : State) :
    Prop where
  pi : PcIn base bytes len args t
  keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  frame : Frame [⟨off base 16, bytes - 16⟩] s.mem t.mem
  mod : val32 t.mem base numOff (nw len) = M
  inv : (M * w32 t.mem base invOff + 1) % 2 ^ 32 = 0
  lt : val32 t.mem base (numAt len 4) (nw len) < M
  val : val32 t.mem base (numAt len 4) (nw len) % M = 2 ^ Spec.Rsa.modulusWords len * 2 ^ (32 * nw len) % M

theorem pcStart_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa PrecomputeFn.start s
      (PcStarted s base bytes len args (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len))) := by
  have dims := h.dimensions
  have facts := valid_facts valid h.lower
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have hfit : ∀ j ≤ 7, numAt len j + wb len ≤ bytes := fun j hj => (h.fits hj).1
  have f5 : numAt len 5 + (3 * wb len + 56) ≤ bytes := (h.fits (j := 0) (by decide)).2
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have n0 : numOff = numAt len 0 := by simp [numAt]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have wbg := wb_ge h.lower
  set M := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) with hMdef
  have frS : ∀ {m m' : Mem} {d n : Nat}, Outside base d n m m' → 16 ≤ d → d + n ≤ bytes →
      Frame [⟨off base 16, bytes - 16⟩] m m' :=
    fun O h1 h2 => (outside_frame O (by omega)).sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., sub_off h1 (by omega)⟩
  unfold PrecomputeFn.start
  -- The modulus, and its inverse.
  refine WP.seq (WP.mono (load_ok h (j := 0) (by decide)) fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  have P₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by have := hfit 0 (by decide); omega))
  refine WP.seq (WP.mono (inverse_ok P₁ (by rw [n0, V₁]; exact facts.1)) fun u₂ ⟨I₂, O₂, K₂⟩ => ?_)
  rw [n0, V₁] at I₂
  have P₂ := P₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by simp only [invOff]; omega))
  have M₂ : val32 u₂.mem base numOff (nw len) = M := by
    rw [O₂.val32 (.inr (by simp [invOff, numOff])) (by omega), n0, V₁]
  -- The seed and the doublings.
  refine WP.seq (WP.mono (seed_ok P₂) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have P₃ := P₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by have := hfit 4 (by decide); omega))
  have M₃ : val32 u₃.mem base numOff (nw len) = M := by
    rw [O₃.val32 (.inl (by rw [e4]; simp only [numOff]; omega)) (by omega), M₂]
  have I₃ : w32 u₃.mem base invOff = w32 u₂.mem base invOff :=
    O₃.w32 (.inl (by rw [e4]; simp only [invOff]; omega)) (by decide)
  refine WP.seq (WP.mono (count_ok P₃) fun u₄ ⟨C₄, m₄, K₄⟩ => ?_)
  have P₄ := P₃.keep K₄ (by decide) (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)
  have seedLt : 2 ^ (8 * (len - 1)) < M := by
    have hv := valid
    rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
    have hk := of_decide_eq_true hv.2
    rw [Nat.lt_iff_le_and_ne]
    refine ⟨by rw [← pow256_eq]; exact hk, fun e => ?_⟩
    have odd := facts.1
    rw [← e, show 8 * (len - 1) = (8 * (len - 1) - 1) + 1 by have := h.lower; omega, Nat.pow_succ] at odd
    simp at odd
  have hN : 0 < 65 * Spec.Rsa.modulusWords len + 8 - 8 * len := by have := dims.2.2; omega
  refine WP.mono (doublings_ok P₄ hN C₄ (by rw [m₄, V₃, ← n0, M₃]; exact seedLt))
    fun u₅ ⟨O₅, V₅, d₅, K₅⟩ => ?_
  rw [m₄, V₃, ← n0, M₃, ← Nat.pow_add] at V₅
  have K₅' := Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi]) K₅ d₅
  have P₅ := P₄.keep K₅' (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by omega))
  refine ⟨P₅, ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
    (K₄.mono (by decide))).trans K₅', ?_, ?_, ?_, ?_, ?_⟩
  · have H₅ : Frame [⟨off base 16, bytes - 16⟩] u₄.mem u₅.mem := frS O₅ (by rw [e4]; omega) (by omega)
    rw [m₄] at H₅
    exact (((frS O₁ (by rw [e0]; omega) (hfit 0 (by decide))).trans
      (frS O₂ (by simp only [invOff]; omega) (by simp only [invOff]; omega))).trans
      (frS O₃ (by rw [e4]; omega) (hfit 4 (by decide)))).trans H₅
  · rw [O₅.val32 (.inl (by rw [e4]; simp only [numOff]; omega)) (by omega), m₄, M₃]
  · rw [O₅.w32 (.inl (by rw [e4]; simp only [invOff]; omega)) (by decide), m₄, I₃]; exact I₂
  · rw [V₅]; exact Nat.mod_lt _ (by omega)
  · rw [V₅, Nat.mod_mod, ← Nat.pow_add]
    congr 2
    simp only [nw]
    have := dims.2.2
    have := h.lower
    omega

theorem pcFinish_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) (top : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) :
    WP isa PrecomputeFn.finish s fun t => t.gpr .eax = 1 ∧
      val32 t.mem (byteAddr (args 0)) 0 (nw len) = val32 s.mem base (numAt len 0) (nw len) ∧
      val32 t.mem (byteAddr (args 0)) (wb len) (nw len) = val32 s.mem base (numAt len 4) (nw len) ∧
      Frame [⟨byteAddr (args 0), 2 * wb len⟩] s.mem t.mem ∧ Keeps [.eax, .ecx, .ebp, .esi] s t := by
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have wbl := wb_le h.upper
  have hfit : ∀ j ≤ 7, numAt len j + wb len ≤ bytes := fun j hj => (h.fits hj).1
  unfold PrecomputeFn.finish
  refine WP.seq (WP.mono (copyOut_ok h (j := 0) (by decide) false) fun u₇ ⟨V₇, O₇, K₇⟩ => ?_)
  simp only [Bool.false_eq_true, ite_false] at V₇ O₇
  obtain ⟨P₇, F₇⟩ := h.keepOut K₇ (by decide) (by decide) top O₇ (by omega)
  have pA : Region.Disjoint ⟨off (byteAddr (args 0)) 0, wb len⟩ ⟨base, bytes⟩ :=
    h.outApart.sub_left (by
      have := sub_off (base := byteAddr (args 0)) (d := 0) (n := wb len) (e := 0) (k := 2 * wb len) (Nat.le_refl _)
        (by omega)
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this)
  have V₄₇ : val32 u₇.mem base (numAt len 4) (nw len) = val32 s.mem base (numAt len 4) (nw len) := by
    rw [← read_eq_val32, ← read_eq_val32]
    refine congrArg BitVec.toNat (F₇.read (r := ⟨off base (numAt len 4), 4 * nw len⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by omega))
    rw [List.mem_singleton.mp hr]
    exact (pA.sub_right (Offset.sub base (d := numAt len 4) (n := 4 * nw len) (e := 0) (k := bytes)
      (Nat.zero_le _) (by have := hfit 4 (by decide); omega) |> fun h => by
        simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h)).symm
  refine WP.seq (WP.mono (copyOut_ok P₇ (j := 4) (by decide) true) fun u₈ ⟨V₈, O₈, K₈⟩ => ?_)
  simp only [ite_true, V₄₇] at V₈ O₈
  have sp₇ : u₇.gpr .esp = s.gpr .esp := K₇.1 _ (by decide)
  obtain ⟨-, F₈⟩ := P₇.keepOut K₈ (by decide) (by decide) (by rw [sp₇]; exact top) O₈ (by omega)
  have pre : ∀ {o n : Nat}, o + n ≤ 2 * wb len →
      Region.Sub ⟨off (byteAddr (args 0)) o, n⟩ ⟨byteAddr (args 0), 2 * wb len⟩ := fun {o n} hon => by
    have := sub_off (base := byteAddr (args 0)) (d := o) (n := n) (e := 0) (k := 2 * wb len) (Nat.zero_le _)
      (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine wp_movS rfl fun t et _ => WP.block_nil ⟨by rw [et.gpr], ?_, ?_, ?_, ?_⟩
  · rw [et.mem, O₈.val32 (.inl (by omega)) (by omega), V₇]
  · rw [et.mem]; exact V₈
  · rw [et.mem]
    exact (F₇.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact pre (by omega)⟩).trans
      (F₈.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact pre (by omega)⟩)
  · exact ((K₇.trans K₈).trans (et.keeps.mono (by decide)))

/-- `compute` runs to its end from a valid modulus. -/
theorem pcCompute_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) (R : CallRoom (s.gpr .esp) base bytes) (top : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa PrecomputeFn.compute s fun _ => True := by
  have f5 : numAt len 5 + (3 * wb len + 56) ≤ bytes := (h.fits (j := 0) (by decide)).2
  have f4 := (h.fits (j := 4) (by decide)).1
  unfold PrecomputeFn.compute
  refine WP.seq (WP.mono (pcStart_ok h valid) fun u₅ S => ?_)
  have sp₅ : u₅.gpr .esp = s.gpr .esp := S.keep.1 _ (by decide)
  refine WP.seq (WP.mono (squares_ok S.pi (by rw [sp₅]; exact R) (by rw [sp₅]; exact top) S.mod S.inv S.lt S.val)
    fun u₆ ⟨_, F₆, K₆⟩ => ?_)
  rw [sp₅] at F₆
  have F₆s : Frame [⟨base, bytes⟩, below (s.gpr .esp) 96] u₅.mem u₆.mem := F₆.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have P₆ := S.pi.keepF K₆ (by decide) (by decide) (by rw [sp₅]; exact R) (by rw [sp₅]; exact top)
    (by rw [sp₅]; exact F₆s)
  exact WP.mono (pcFinish_ok P₆ (by rw [(K₆.1 _ (by decide)).trans sp₅]; exact top)) fun _ _ => trivial

theorem precomputeValid_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputeInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa PrecomputeFn.valid s fun t => PrecomputePost base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have R := h.room
  have top := h.top
  set M := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) with hMdef
  set W := Spec.Rsa.modulusWords len with hW
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have n0 : numOff = numAt len 0 := by simp [numAt]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  let Regs : List Region := [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), 16 * W⟩, below (s.gpr .esp) 96,
    ⟨addr (s.gpr .esp) 8, 4⟩]
  unfold PrecomputeFn.valid
  -- `n_len` into argument 1.
  refine WP.seq (WP.mono (pcSetWidth_ok h) fun u₀ ⟨P₀, F₀, K₀⟩ => ?_)
  have sp₀ : u₀.gpr .esp = s.gpr .esp := K₀.1 _ (by decide)
  have hfit : ∀ j ≤ 7, numAt len j + wb len ≤ bytes := fun j hj => (P₀.fits hj).1
  have f5 : numAt len 5 + (3 * wb len + 56) ≤ bytes := (P₀.fits (j := 0) (by decide)).2
  have G₀ : Frame Regs s.mem u₀.mem := F₀.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp [Regs]
  have N₀ : Spec.Rsa.bytesAt u₀.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len := by
    refine pcBytesAt_frame F₀ (fun r hr => ?_) (by omega)
    rw [List.mem_singleton.mp hr]
    have := h.nArg
    simpa only [stackAddress] using this
  have a2 : pcArgs len args 2 = args 2 := by simp [pcArgs]
  have a0 : pcArgs len args 0 = args 0 := by simp [pcArgs]
  -- `2^(65 W) mod M`, the squares and the copies.
  unfold PrecomputeFn.compute
  refine WP.seq (WP.mono (pcStart_ok P₀ (by rw [a2, N₀]; exact valid)) fun u₅ S => ?_)
  rw [a2, N₀] at S
  have sp₅ : u₅.gpr .esp = s.gpr .esp := (S.keep.1 _ (by decide)).trans sp₀
  refine WP.seq (WP.mono (squares_ok S.pi (by rw [sp₅]; exact R) (by rw [sp₅]; exact top) S.mod S.inv S.lt S.val)
    fun u₆ ⟨V₆, F₆, K₆⟩ => ?_)
  rw [sp₅] at F₆
  have F₆s : Frame [⟨base, bytes⟩, below (s.gpr .esp) 96] u₅.mem u₆.mem := F₆.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by have := hfit 4 (by decide); omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have P₆ := S.pi.keepF K₆ (by decide) (by decide) (by rw [sp₅]; exact R) (by rw [sp₅]; exact top)
    (by rw [sp₅]; exact F₆s)
  have M₆ : val32 u₆.mem base (numAt len 0) (nw len) = M := by
    rw [mulFrame_val32 R nw' F₆ (.inl (by rw [e0, e4]; omega)) (by simp only [numAt, numOff]; omega)
      (by have := hfit 0 (by decide); omega) (hfit 4 (by decide)) f5, ← n0, S.mod]
  have sp₆ : u₆.gpr .esp = s.gpr .esp := (K₆.1 _ (by decide)).trans sp₅
  refine WP.mono (pcFinish_ok P₆ (by rw [sp₆]; exact top)) fun t ⟨eax, V₀, V₄, F₈, K₈⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · rw [VG.Proof.Bignum.publicPrecompute_some (bytesAt_length _ _ _) valid]
    refine ⟨eax, ?_⟩
    rw [a0] at V₀ V₄
    refine VG.Proof.Bignum.wordsAt_two_reads ?_ ?_
    · rw [show 8 * Spec.Rsa.modulusWords len = 4 * nw len by simp only [nw]; omega,
        show byteAddr (args 0) = off (byteAddr (args 0)) 0 by simp [off], read_eq_val32, V₀, M₆]
    · rw [show 8 * Spec.Rsa.modulusWords len = 4 * nw len by simp only [nw]; omega, read_eq_val32]
      rw [wbe] at V₄
      rw [V₄, V₆]
      rfl
  · have H₆ : Frame Regs u₅.mem u₆.mem := F₆.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_off (by rw [e4]; omega) (by have := hfit 4 (by decide); omega)⟩
      · exact ⟨_, List.mem_cons_self .., sub_off (by simp only [numAt, numOff]; omega) (by omega)⟩
      · exact ⟨_, by simp [Regs], fun _ h => h⟩
    have H₈ : Frame Regs u₆.mem t.mem := F₈.sub fun r hr => by
      rw [List.mem_singleton.mp hr, a0]
      exact ⟨⟨byteAddr (args 0), 16 * W⟩, by simp [Regs], by
        rw [show 2 * wb len = 16 * W by simp only [wb]; omega]; exact fun _ h => h⟩
    exact ((G₀.trans (S.frame.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [Regs])).trans H₆).trans H₈
  · exact (((K₀.mono (by decide)).trans S.keep).trans (K₆.mono (by decide))).trans (K₈.mono (by decide))

end VG.Proof.Bignum.X86.PublicContext
