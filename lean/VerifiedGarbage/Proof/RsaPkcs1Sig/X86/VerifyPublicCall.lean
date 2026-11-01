module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicPre
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContext

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyLocal
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedABI
/-! # Calling checked public RSA retains every immutable verification input -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyCall.lean`, which only this module imported.
section

/-! # A verified nested call preserves the private wrapper's immutable inputs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Mont.X86

def callClobbers : List Reg := [.eax, .ecx, .edx]

theorem call_keeps {s t : State} (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : Keeps callClobbers s t := by
  refine ⟨?_, rd, wr⟩
  intro r hr
  apply regs r
  cases r <;> simp_all [callClobbers, calleeSaved]

theorem private_call_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s)
    {name : String} {code : Prog isa} {contract : Contract isa}
    (verified : Verified target code contract) (stack : stackUse code ≤ 96) (noSp : NoSp code)
    {rd wr : List Region} (pre : contract.pre (s.callEntry.withRegions rd wr))
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (sub : ∀ r ∈ wr, ∃ R ∈ bodyWrites g, r.Sub R) :
    WP isa (.call name code) s fun t => Context g bs t ∧
      Frame (wr ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧
      ∃ u : State, u.mem = t.mem ∧ (∀ r, r ≠ .esp → u.gpr r = t.gpr r) ∧
        contract.post (s.callEntry.withRegions rd wr) u := by
  refine VG.X86.WP.call verified.1 noSp
    (by rw [h.sp]; have := h.valid.stackLow; omega) pre read write ?_
  intro t rdT wrT regs frame _ post
  have K := call_keeps rdT wrT regs
  have SP := K.1 .esp (by decide)
  have F : Frame (wr ++ [g.calleeRegion]) s.mem t.mem := by
    apply frame.sub
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨g.calleeRegion, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [h.sp]
      exact VG.X86.below_sub (by omega : stackUse code + 4 ≤ 100) h.valid.stackLow
  have Fbody : Frame (bodyWrites g) s.mem t.mem := F.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact sub r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩)
  exact ⟨h.after Fbody K SP, F, K, post⟩

end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

structure PublicImpl where
  name : String
  code : Prog isa
  verified : Verified target code (Spec.Rsa.publicPrecomputedCheckedContract abi 96)
  stack : stackUse code ≤ 96
  noSp : NoSp code

theorem publicCovers {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    Covers (publicRd g ++ publicWr g) (s.rd ++ s.wr) ∧ Covers (publicWr g) s.wr := by
  have outgoing : InRegions s.wr (byteAddr g.stack) 40 := by
    have W := h.inner.write (d := 0) (n := 40) (by decide)
    simpa only [BitVec.add_zero] using W
  have wr : Covers (publicWr g) s.wr := (Covers.one h.em1Write).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one outgoing))
  exact ⟨Covers.append_left ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 1).read).pair (Covers.one (h.sources 3).read))) wr.right, wr⟩

theorem publicWrites_sub {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    ∀ r ∈ publicWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [publicWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], h.em1Sub⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩

theorem Context.callFrame {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : Frame [g.calleeRegion] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem, h.sp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (VG.X86.below_top (by decide : 4 ≤ 100) h.valid.stackLow (by decide : 4 ≤ 4))

theorem Context.callBytes {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (i : Fin 5) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources i)) (g.sourceLength i) = bs i :=
  (VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by have := (h.sources i).fits; omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm)).trans (h.sources i).bytes

theorem Context.callWords {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) :
    Spec.Rsa.wordsAt s.callEntry.mem (byteAddr (g.sources 4)) g.preLength =
      Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength :=
  VG.Proof.Rsa.wordsAt_frame h.callFrame (by
      have fit := h.valid.sourceFits 4
      change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
      omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources 4).sub_left h.valid.calleeSub).symm)

def PublicOut (g : Geometry) (bs : Fin 5 → List Byte) (s t : State) : Prop :=
  Spec.Rsa.publicPrecompute (bs 0) = some (Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength) →
    Spec.Rsa.written t.mem (byteAddr g.em1) g.length (t.gpr .eax)
      (Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 3))

theorem public_call (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (publicArgument g) 10 s) (siglen : g.signatureLength = g.length) :
    WP isa (.call v.name v.code) s fun t => Context g bs t ∧
      Frame (publicWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ PublicOut g bs s t := by
  refine WP.mono (private_call_ok h v.verified v.stack v.noSp (publicCall_pre h a siglen)
    (publicCovers h).1 (publicCovers h).2 (publicWrites_sub h)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  refine ⟨ht, F, K, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 10) => publicArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have pfit : g.preLength < 2 ^ 32 := by
    have fit := h.valid.sourceFits 4
    change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
    omega
  simp only [sa (by decide : 0 < 10), sa (by decide : 1 < 10), sa (by decide : 2 < 10),
    sa (by decide : 3 < 10), sa (by decide : 4 < 10), sa (by decide : 5 < 10), sa (by decide : 6 < 10),
    publicArgument, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  change ∀ nb : List Byte, nb.length = g.length →
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.wordsAt s.callEntry.mem (byteAddr (g.sources 4)) g.preLength) →
      Spec.Rsa.written t.mem (byteAddr g.em1) g.length (t.gpr .eax)
        (Spec.Rsa.publicOpChecked nb
          (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 1)) (g.sourceLength 1))
          (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 3)) g.length)) at post
  have sigBytes : Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 3)) g.length = bs 3 := by
    rw [← siglen]
    exact h.callBytes 3
  rw [h.callWords, h.callBytes 1, sigBytes] at post
  exact post (bs 0) (h.sources 0).length

end VG.Proof.RsaPkcs1Sig.X86.Ver
