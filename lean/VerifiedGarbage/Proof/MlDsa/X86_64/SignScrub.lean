module

public import VerifiedGarbage.Proof.MlDsa.X86_64.FnScrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Call
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Mask
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestRow
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp4
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top
public import VerifiedGarbage.Proof.MlDsa.X86_64.PkTr
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.ExternalMu
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Sat
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
public import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Scrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFns
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# ML-DSA's signing on x86-64, without secret residue

Each function as emitted (`Impl.MlDsa.X86_64.Fn`), over any implementation of
the polynomial arithmetic (`ArithImpl`), with its whole stack wiped by its
cleanup at the implementation's level: its code over the stub, but for the
call of the signing over the implementation, which is that over the stub with
the implementation's functions (`FnScrub`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.SignScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.FnScrub (stub stubStack)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)
open VG.Proof.MlDsa.X86_64.Message (signPrepared_sat)

/-! ## The body every variant shares

The body calls the polynomial arithmetic by the addresses its variant's entry
stores (`Impl.MlDsa.X86_64.Fn.signShared`): it is its code over the stub
with the implementation's functions as the candidates of its indirect calls
(`fillI`), which the kernel checks once for each parameter set
(`body44_eq`), so the cleanup's side conditions of it follow from those of
the stub's code, which the kernel evaluates once (`stub44_ins`,
`stub44_inames`), and of the implementation's functions (`ArithImpl.sides`). -/

/-- What the cleanup needs of an instruction: a vector instruction of at most
the level `k`, and no load of MXCSR. -/
abbrev Ins (k : Nat) : Instr → Bool := fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i

/-- The functions the body over `B` calls by their addresses, by the names
the body over the stub calls them by, with the names it calls them by. -/
def tableV (B : Impl.MlDsa.X86_64.Arith.Backend) (ℓ : Nat) : List (String × String × Prog isa) :=
  (Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) ℓ).zip
    ((Impl.MlDsa.X86_64.Sign.slotNames (primsWith B true) ℓ).zip
      [B.ntt, B.invNtt, (primsWith B true).dotInv ℓ, B.mul, B.add, B.sub, B.rej4, B.expandMask4,
        B.highBits, B.lowBits, B.normLt, B.makeHint])

/-- `tableV`, by the names the body over the stub calls its functions by. -/
def sigmaV (B : Impl.MlDsa.X86_64.Arith.Backend) (ℓ : Nat) (f : String) : Option (String × Prog isa) :=
  (tableV B ℓ).lookup f

theorem lookup_zip_isSome {β : Type} {n : String} :
    ∀ (l₁ : List String) (l₂ : List β), l₁.length ≤ l₂.length → n ∈ l₁ → (List.lookup n (l₁.zip l₂)).isSome
  | [], _, _, h => absurd h List.not_mem_nil
  | _ :: _, [], h, _ => absurd h (by simp)
  | a :: l₁, _ :: l₂, h, hn => by
    simp only [List.zip_cons_cons, List.lookup]
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp hn with rfl | hn
      · simp at hne
      · exact lookup_zip_isSome l₁ l₂ (by simpa using h) hn

theorem sigmaV_isSome (B : Impl.MlDsa.X86_64.Arith.Backend) (ℓ : Nat) {n : String}
    (hn : n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) ℓ) : (sigmaV B ℓ n).isSome :=
  lookup_zip_isSome _ _ (by simp [Impl.MlDsa.X86_64.Sign.slotNames]) hn

theorem sigmaV_side (v : ArithImpl) {ℓ : Nat} (hℓ : ℓ = 4 ∨ ℓ = 5 ∨ ℓ = 7) :
    ∀ f g d, sigmaV v.code ℓ f = some (g, d) →
      g ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith v.code true) ℓ ∧ calleeSide d v.level.level 24 = true := by
  intro f g d h
  have hm := FnScrub.mem_of_lookup h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := v.sides
  simp only [tableV, Impl.MlDsa.X86_64.Sign.slotNames, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals refine ⟨by simp [Impl.MlDsa.X86_64.Sign.slotNames], ?_⟩
  all_goals first
    | assumption
    | (rcases hℓ with rfl | rfl | rfl <;> simpa [Impl.MlDsa.X86_64.Sign.Prims.dotInv, primsWith])

/-- What the cleanup needs of the body over `v`, from what it needs of its
code over the stub. -/
theorem body_side (v : ArithImpl) {p : Spec.MlDsa.Params} (hℓ : p.ℓ = 4 ∨ p.ℓ = 5 ∨ p.ℓ = 7)
    (he : Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) p =
      fillI (sigmaV v.code p.ℓ) (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) p))
    (hs : (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) p).allInstrs (Ins VecLevel.sse.level) = true)
    (hn : (UpperLock.inames (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) p)).all
      (fun n => decide (n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) p.ℓ)) = true) :
    (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) p).allInstrs (Ins v.level.level) = true ∧
      ∀ n ∈ UpperLock.inames (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) p),
        n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith v.code true) p.ℓ := by
  have hsd : ∀ f g d, sigmaV v.code p.ℓ f = some (g, d) →
      d.allInstrs (Ins v.level.level) = true ∧ UpperLock.inames d = [] := fun f g d h => by
    have := (sigmaV_side v hℓ f g d h).2
    simp only [calleeSide, Bool.and_eq_true, List.isEmpty_iff] at this
    exact ⟨this.1.2, this.2⟩
  rw [he]
  refine ⟨fillI_allInstrs (fun f g d h => (hsd f g d h).1) _ (side_mono (Nat.zero_le _) hs),
    fillI_inames (fun f g d h => ⟨(sigmaV_side v hℓ f g d h).1, (hsd f g d h).2⟩) _ fun n hn' => ?_⟩
  exact .inr (sigmaV_isSome _ _ (of_decide_eq_true (List.all_eq_true.mp hn n hn')))

theorem body44_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) Spec.MlDsa.mlDsa44 =
      fillI (sigmaV v.code 4) (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa44) := by
  kernel_rfl

theorem stub44_ins : (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa44).allInstrs
    (Ins VecLevel.sse.level) = true := (by lit_decide : Sign.sign44V.allInstrs (Ins VecLevel.sse.level) = true)

theorem stub44_inames : (UpperLock.inames (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa44)).all
    (fun n => decide (n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) 4)) = true :=
  (by lit_decide : (UpperLock.inames Sign.sign44V).all
    (fun n => decide (n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) 4)) = true)

/-! ## Around the body -/

theorem fillSlots_ins {k : Nat} : ∀ (o : Nat) (ns : List String),
    (Code.block (Impl.MlDsa.X86_64.Sign.fillSlots o ns) : Prog isa).allInstrs (Ins k) = true
  | _, [] => rfl
  | o, _ :: ns => by
    have ih := fillSlots_ins (k := k) (o + 8) ns
    simp only [Impl.MlDsa.X86_64.Sign.fillSlots, Code.allInstrs] at ih ⊢
    rw [ih]; rfl

theorem fillSlots_inames : ∀ (o : Nat) (ns : List String),
    UpperLock.inames (Code.block (Impl.MlDsa.X86_64.Sign.fillSlots o ns) : Prog isa) = [] := fun _ _ => rfl

theorem shared_ins {k : Nat} {ns : List String} {b : String} {c : Prog isa} (hc : c.allInstrs (Ins k) = true) :
    (Impl.MlDsa.X86_64.Sign.signVia ns b c).allInstrs (Ins k) = true := by
  have hf := fillSlots_ins (k := k) 0 ns
  simp only [Impl.MlDsa.X86_64.Sign.signVia, Code.allInstrs] at hf ⊢
  rw [hf, hc]; rfl

theorem shared_inames {ns : List String} {b : String} {c : Prog isa} :
    UpperLock.inames (Impl.MlDsa.X86_64.Sign.signVia ns b c) = UpperLock.inames c := by
  simp only [Impl.MlDsa.X86_64.Sign.signVia, UpperLock.inames, List.nil_append]

theorem entry_ins {k : Nat} {n : String} {c : Prog isa} {flag : Nat} (hc : c.allInstrs (Ins k) = true) :
    (Impl.MlDsa.X86_64.Sign.entry n c flag).allInstrs (Ins k) = true := by
  simp only [Impl.MlDsa.X86_64.Sign.entry, Code.allInstrs, hc, Bool.and_true]
  rfl

theorem entry_inames {n : String} {c : Prog isa} {flag : Nat} :
    UpperLock.inames (Impl.MlDsa.X86_64.Sign.entry n c flag) = UpperLock.inames c := by
  simp only [Impl.MlDsa.X86_64.Sign.entry, UpperLock.inames, List.nil_append]

theorem entry_depth {n : String} {c : Prog isa} {flag : Nat} :
    (Impl.MlDsa.X86_64.Sign.entry n c flag).x86_64Depth = c.x86_64Depth + 8 := by
  simp only [Impl.MlDsa.X86_64.Sign.entry, Code.x86_64Depth, Nat.zero_max]

theorem kabs_ins : Impl.Sha3.X86_64.Stream.absorb.allInstrs (Ins VecLevel.sse.level) = true := by lit_decide
theorem kpad_ins : Impl.Sha3.X86_64.Stream.pad.allInstrs (Ins VecLevel.sse.level) = true := by lit_decide
theorem ksqz_ins : Impl.Sha3.X86_64.Stream.squeeze.allInstrs (Ins VecLevel.sse.level) = true := by lit_decide
theorem kabs_inames : UpperLock.inames Impl.Sha3.X86_64.Stream.absorb = [] := by lit_decide
theorem kpad_inames : UpperLock.inames Impl.Sha3.X86_64.Stream.pad = [] := by lit_decide
theorem ksqz_inames : UpperLock.inames Impl.Sha3.X86_64.Stream.squeeze = [] := by lit_decide
theorem kabs_depth : Impl.Sha3.X86_64.Stream.absorb.x86_64Depth ≤ 144 := by lit_decide
theorem kpad_depth : Impl.Sha3.X86_64.Stream.pad.x86_64Depth ≤ 144 := by lit_decide
theorem ksqz_depth : Impl.Sha3.X86_64.Stream.squeeze.x86_64Depth ≤ 144 := by lit_decide

theorem argMov_ins {k : Nat} (d : Reg) (hd : d ∈ Impl.MlDsa.X86_64.Message.argRegs6) (a : Impl.MlDsa.X86_64.Message.Arg) :
    (Code.block (a.mov d) : Prog isa).allInstrs (Ins k) = true := by
  simp only [Impl.MlDsa.X86_64.Message.argRegs6, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> rfl

theorem setArgs_ins {k : Nat} (as : List Impl.MlDsa.X86_64.Message.Arg) :
    (Code.block (Impl.MlDsa.X86_64.Message.setArgs as) : Prog isa).allInstrs (Ins k) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simp only [instrs, Impl.MlDsa.X86_64.Message.setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, hm, hi⟩ := hi
  have := argMov_ins (k := k) d (List.of_mem_zip hm).1 a
  rw [Code.allInstrs_eq, List.all_eq_true] at this
  exact this i (by simpa [instrs] using hi)

theorem signMessage_ins {k : Nat} (hk : VecLevel.sse.level ≤ k) {n : String} {c : Prog isa} {p : Spec.MlDsa.Params}
    (flag : Nat) (hc : c.allInstrs (Ins k) = true) :
    (Impl.MlDsa.X86_64.Message.signMessage n c p flag).allInstrs (Ins k) = true := by
  have ha := side_mono hk kabs_ins
  have hp' := side_mono hk kpad_ins
  have hs := side_mono hk ksqz_ins
  have hsa : ∀ as, (Code.block (Impl.MlDsa.X86_64.Message.setArgs as) : Prog isa).allInstrs (Ins k) = true :=
    setArgs_ins
  have hmv : ∀ a : Impl.MlDsa.X86_64.Message.Arg, (Code.block (a.mov .rdi) : Prog isa).allInstrs (Ins k) = true :=
    fun a => argMov_ins .rdi (by decide) a
  simp only [Impl.MlDsa.X86_64.Message.signMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.zeroSt, Impl.MlDsa.X86_64.Message.kabs,
    Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz, Impl.MlDsa.X86_64.Message.callA,
    Code.allInstrs] at hsa hmv ⊢
  simp only [hc, ha, hp', hs, hsa, hmv, Bool.and_true, Bool.true_and]
  rfl

theorem signMessage_inames {n : String} {c : Prog isa} {p : Spec.MlDsa.Params} {flag : Nat} :
    UpperLock.inames (Impl.MlDsa.X86_64.Message.signMessage n c p flag) = UpperLock.inames c := by
  simp only [Impl.MlDsa.X86_64.Message.signMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.zeroSt, Impl.MlDsa.X86_64.Message.kabs,
    Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz, Impl.MlDsa.X86_64.Message.callA,
    UpperLock.inames, kabs_inames, kpad_inames, ksqz_inames, List.nil_append, List.append_nil]

theorem signMessage_depth {n : String} {c : Prog isa} {p : Spec.MlDsa.Params} {flag : Nat}
    (hc : c.x86_64Depth ≤ 144) : (Impl.MlDsa.X86_64.Message.signMessage n c p flag).x86_64Depth ≤ 224 := by
  simp only [Impl.MlDsa.X86_64.Message.signMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.zeroSt, Impl.MlDsa.X86_64.Message.kabs,
    Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz, Impl.MlDsa.X86_64.Message.callA,
    Impl.MlDsa.X86_64.Message.signRegs, Code.x86_64Depth, Instr.frameBytes,
    List.length_cons, List.length_nil, Nat.zero_max, Nat.max_zero]
  have := kabs_depth; have := kpad_depth; have := ksqz_depth
  omega

/-- What the cleanup needs of the entry of `v`'s variant of ML-DSA-44's signing, which calls the body `b`. -/
theorem shared44 (v : ArithImpl) (b : String) :
    (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa44).allInstrs (Ins v.level.level) = true ∧
      ∀ n ∈ UpperLock.inames (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa44),
        n ∈ Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa44 := by
  obtain ⟨h1, h2⟩ := body_side v (p := Spec.MlDsa.mlDsa44) (by decide) (body44_eq v) stub44_ins stub44_inames
  exact ⟨shared_ins h1, by rw [Impl.MlDsa.X86_64.Fn.signShared, shared_inames]; exact h2⟩

theorem shared44_sp (v : ArithImpl) (b : String) :
    (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa44).all (fun i => !isa.writesSp i) = true :=
  Proof.MlDsa.X86_64.Message.signVia_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl) true)

/-- `Spec.MlDsa.sign44Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem sign44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 0)
      ((Spec.MlDsa.sign44Api).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa44)) 152) 32 := by
  have hs := shared44 v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (entry_ins (n := (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)) (flag := 0) hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signEntryV_verified v (List.mem_cons_self ..) _ _)
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.signOut Spec.MlDsa.mlDsa44 _)) (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 0)
    (by rw [entry_depth]; have := (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_self ..) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")).depth; omega_using [this]) hlv (mxSame_of_noLoad hmx) (by rw [entry_inames]; exact hs.2)

theorem sign44_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 0).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 0)

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSign44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 1)
      (((Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa44)) 152) 32 := by
  have hs := shared44 v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (entry_ins (n := (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)) (flag := 1) hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signPreparedEntryV_verified v (List.mem_cons_self ..) _ _)
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.preparedSignOut Spec.MlDsa.mlDsa44 _)) (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 1)
    (by rw [entry_depth]; have := (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_self ..) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")).depth; omega_using [this]) hlv (mxSame_of_noLoad hmx) (by rw [entry_inames]; exact hs.2)

theorem preparedSign44_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 1).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 1)

/-- `Spec.MlDsa.signMessage44Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem signMessage44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 0)
      ((Spec.MlDsa.signMessage44Api).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa44)) 224) 32 := by
  have hs := shared44 v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (signMessage_ins (Nat.zero_le _) (n := (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)) 0 hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signMessage_verifiedF (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_self ..) _) (List.mem_cons_self ..))
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.signMessageOut Spec.MlDsa.mlDsa44 _)) (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 0)
    (signMessage_depth (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_self ..) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")).depth) hlv (mxSame_of_noLoad hmx) (by rw [signMessage_inames]; exact hs.2)

theorem signMessage44_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 0).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 0)

/-- `(Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSignMessage44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 1)
      (((Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa44)) 224) 32 := by
  have hs := shared44 v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (signMessage_ins (Nat.zero_le _) (n := (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)) 1 hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signMessagePrepared_verifiedF (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_self ..) _) (List.mem_cons_self ..) (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..)))
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.preparedSignMessageOut Spec.MlDsa.mlDsa44 _)) (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 1)
    (signMessage_depth (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_self ..) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")).depth) hlv (mxSame_of_noLoad hmx) (by rw [signMessage_inames]; exact hs.2)

theorem preparedSignMessage44_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa44 1).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared44_sp v (Proof.MlDsa.signWithCacheName "mldsa44" ++ "_body")) 1)

theorem body65_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) Spec.MlDsa.mlDsa65 =
      fillI (sigmaV v.code 5) (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa65) := by
  kernel_rfl

theorem stub65_ins : (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa65).allInstrs
    (Ins VecLevel.sse.level) = true := (by lit_decide : Sign.sign65V.allInstrs (Ins VecLevel.sse.level) = true)

theorem stub65_inames : (UpperLock.inames (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa65)).all
    (fun n => decide (n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) 5)) = true :=
  (by lit_decide : (UpperLock.inames Sign.sign65V).all
    (fun n => decide (n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) 5)) = true)

/-- What the cleanup needs of the entry of `v`'s variant of ML-DSA-65's signing, which calls the body `b`. -/
theorem shared65 (v : ArithImpl) (b : String) :
    (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa65).allInstrs (Ins v.level.level) = true ∧
      ∀ n ∈ UpperLock.inames (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa65),
        n ∈ Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa65 := by
  obtain ⟨h1, h2⟩ := body_side v (p := Spec.MlDsa.mlDsa65) (by decide) (body65_eq v) stub65_ins stub65_inames
  exact ⟨shared_ins h1, by rw [Impl.MlDsa.X86_64.Fn.signShared, shared_inames]; exact h2⟩

theorem shared65_sp (v : ArithImpl) (b : String) :
    (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa65).all (fun i => !isa.writesSp i) = true :=
  Proof.MlDsa.X86_64.Message.signVia_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl)) true)

/-- `Spec.MlDsa.sign65Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem sign65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 0)
      ((Spec.MlDsa.sign65Api).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa65)) 152) 32 := by
  have hs := shared65 v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (entry_ins (n := (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)) (flag := 0) hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signEntryV_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ _)
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.signOut Spec.MlDsa.mlDsa65 _)) (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 0)
    (by rw [entry_depth]; have := (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")).depth; omega_using [this]) hlv (mxSame_of_noLoad hmx) (by rw [entry_inames]; exact hs.2)

theorem sign65_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 0).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 0)

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSign65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 1)
      (((Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa65)) 152) 32 := by
  have hs := shared65 v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (entry_ins (n := (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)) (flag := 1) hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signPreparedEntryV_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ _)
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.preparedSignOut Spec.MlDsa.mlDsa65 _)) (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 1)
    (by rw [entry_depth]; have := (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")).depth; omega_using [this]) hlv (mxSame_of_noLoad hmx) (by rw [entry_inames]; exact hs.2)

theorem preparedSign65_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 1).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 1)

/-- `Spec.MlDsa.signMessage65Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem signMessage65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 0)
      ((Spec.MlDsa.signMessage65Api).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa65)) 224) 32 := by
  have hs := shared65 v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (signMessage_ins (Nat.zero_le _) (n := (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)) 0 hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signMessage_verifiedF (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.signMessageOut Spec.MlDsa.mlDsa65 _)) (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 0)
    (signMessage_depth (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")).depth) hlv (mxSame_of_noLoad hmx) (by rw [signMessage_inames]; exact hs.2)

theorem signMessage65_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 0).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 0)

/-- `(Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSignMessage65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 1)
      (((Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa65)) 224) 32 := by
  have hs := shared65 v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (signMessage_ins (Nat.zero_le _) (n := (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)) 1 hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signMessagePrepared_verifiedF (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.preparedSignMessageOut Spec.MlDsa.mlDsa65 _)) (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 1)
    (signMessage_depth (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")).depth) hlv (mxSame_of_noLoad hmx) (by rw [signMessage_inames]; exact hs.2)

theorem preparedSignMessage65_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa65 1).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared65_sp v (Proof.MlDsa.signWithCacheName "mldsa65" ++ "_body")) 1)

theorem body87_eq (v : ArithImpl) :
    Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) Spec.MlDsa.mlDsa87 =
      fillI (sigmaV v.code 7) (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa87) := by
  kernel_rfl

theorem stub87_ins : (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa87).allInstrs
    (Ins VecLevel.sse.level) = true := (by lit_decide : Sign.sign87V.allInstrs (Ins VecLevel.sse.level) = true)

theorem stub87_inames : (UpperLock.inames (Impl.MlDsa.X86_64.Sign.sign (primsWith stub true) Spec.MlDsa.mlDsa87)).all
    (fun n => decide (n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) 7)) = true :=
  (by lit_decide : (UpperLock.inames Sign.sign87V).all
    (fun n => decide (n ∈ Impl.MlDsa.X86_64.Sign.slotNames (primsWith stub true) 7)) = true)

/-- What the cleanup needs of the entry of `v`'s variant of ML-DSA-87's signing, which calls the body `b`. -/
theorem shared87 (v : ArithImpl) (b : String) :
    (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa87).allInstrs (Ins v.level.level) = true ∧
      ∀ n ∈ UpperLock.inames (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa87),
        n ∈ Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa87 := by
  obtain ⟨h1, h2⟩ := body_side v (p := Spec.MlDsa.mlDsa87) (by decide) (body87_eq v) stub87_ins stub87_inames
  exact ⟨shared_ins h1, by rw [Impl.MlDsa.X86_64.Fn.signShared, shared_inames]; exact h2⟩

theorem shared87_sp (v : ArithImpl) (b : String) :
    (Impl.MlDsa.X86_64.Fn.signShared b (primsWith v.code true) Spec.MlDsa.mlDsa87).all (fun i => !isa.writesSp i) = true :=
  Proof.MlDsa.X86_64.Message.signVia_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl)) true)

/-- `Spec.MlDsa.sign87Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem sign87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 0)
      ((Spec.MlDsa.sign87Api).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa87)) 152) 32 := by
  have hs := shared87 v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (entry_ins (n := (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)) (flag := 0) hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signEntryV_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _ _)
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.signOut Spec.MlDsa.mlDsa87 _)) (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 0)
    (by rw [entry_depth]; have := (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")).depth; omega_using [this]) hlv (mxSame_of_noLoad hmx) (by rw [entry_inames]; exact hs.2)

theorem sign87_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 0).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 0)

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSign87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 1)
      (((Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa87)) 152) 32 := by
  have hs := shared87 v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (entry_ins (n := (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)) (flag := 1) hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signPreparedEntryV_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _ _)
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.preparedSignOut Spec.MlDsa.mlDsa87 _)) (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 1)
    (by rw [entry_depth]; have := (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")).depth; omega_using [this]) hlv (mxSame_of_noLoad hmx) (by rw [entry_inames]; exact hs.2)

theorem preparedSign87_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 1).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 1)

/-- `Spec.MlDsa.signMessage87Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem signMessage87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 0)
      ((Spec.MlDsa.signMessage87Api).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa87)) 224) 32 := by
  have hs := shared87 v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (signMessage_ins (Nat.zero_le _) (n := (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)) 0 hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signMessage_verifiedF (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.signMessageOut Spec.MlDsa.mlDsa87 _)) (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 0)
    (signMessage_depth (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")).depth) hlv (mxSame_of_noLoad hmx) (by rw [signMessage_inames]; exact hs.2)

theorem signMessage87_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 0).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 0)

/-- `(Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSignMessage87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 1)
      (((Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).contract (X86_64.abi.withFns (Proof.MlDsa.X86_64.Message.viaNames v Spec.MlDsa.mlDsa87)) 224) 32 := by
  have hs := shared87 v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) (signMessage_ins (Nat.zero_le _) (n := (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)) 1 hs.1)
  exact verifiedScrubbedAllFns v.level (Proof.MlDsa.X86_64.Message.signMessagePrepared_verifiedF (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    (PostOut.withFns (VG.Proof.MlDsa.X86_64.Scrub.preparedSignMessageOut Spec.MlDsa.mlDsa87 _)) (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 1)
    (signMessage_depth (Proof.MlDsa.X86_64.Message.signViaFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")).depth) hlv (mxSame_of_noLoad hmx) (by rw [signMessage_inames]; exact hs.2)

theorem preparedSignMessage87_spSafe (v : ArithImpl) :
    (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body") (primsWith v.code true) Spec.MlDsa.mlDsa87 1).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signMessage_spSafe (shared87_sp v (Proof.MlDsa.signWithCacheName "mldsa87" ++ "_body")) 1)

end VG.Proof.MlDsa.X86_64.SignScrub
