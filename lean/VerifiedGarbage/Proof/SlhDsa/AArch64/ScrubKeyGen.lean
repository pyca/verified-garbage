module

-- separate module: key generation's cleanup, which the registration file and sign's cleanup import

public import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenCT
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Impl
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Fn
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.SlhDsa.AArch64.XmssCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64: key generation without secret residue

Key generation as emitted (`Impl.SlhDsa.AArch64.Fn.keyGen`), over any
implementation `T` of `thash4`: its code with every register the calling
convention does not preserve cleared (`scrubAll 0 0 Clear.all`), as it uses
no stack. What the cleanup needs of the code (no frames, no write of
PSTATE.DIT, no indirect call) is evaluated by the kernel once, of the code
with `thash4`'s calls holes (`stubOf`), whatever the names of the functions
(`keyGen_fill`), and `T` gives it of its own code (`Thash4Impl.side`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.KeyGen

open VG VG.AArch64 VG.AArch64.Scrub
open VG.Spec.SlhDsa
open VG.Impl.Scrub.AArch64 (scrubAll Clear)

/-- The functions key generation over `T` calls, for the parameter set named `set`. -/
abbrev fnsOf {n : Nat} (p : Params) (T : Thash4Impl n) (set : String) : Impl.SlhDsa.AArch64.Shake.Fns :=
  Impl.SlhDsa.AArch64.Shake.Fns.ofVariant p T.sha3 T.sfx set

/-- The functions `f`, with `thash4`'s code a hole. -/
def stubOf (f : Impl.SlhDsa.AArch64.Shake.Fns) : Impl.SlhDsa.AArch64.Shake.Fns := { f with t4 := .block [] }

theorem keyGen_fill (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    Impl.SlhDsa.AArch64.Shake.keyGen p f =
      Code.fillCalls f.t4name f.t4 (Impl.SlhDsa.AArch64.Shake.keyGen p (stubOf f)) := by
  kernel_rfl

theorem xmss_fill (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    Impl.SlhDsa.AArch64.Shake.xmssCode p f =
      Code.fillCalls f.t4name f.t4 (Impl.SlhDsa.AArch64.Shake.xmssCode p (stubOf f)) := by
  kernel_rfl

theorem noFrames_fillCalls {n : String} {b e : Prog isa} (hb : b.noFrames = true) (he : e.noFrames = true) :
    (Code.fillCalls n b e).noFrames = true := by
  induction e with
  | block is => exact he
  | seq x y ihx ihy =>
    simp only [Code.fillCalls, Code.noFrames, Bool.and_eq_true] at he ⊢
    exact ⟨ihx he.1, ihy he.2⟩
  | ite cd t e iht ihe =>
    simp only [Code.fillCalls, Code.noFrames, Bool.and_eq_true] at he ⊢
    exact ⟨iht he.1, ihe he.2⟩
  | loop x cd ih => simp only [Code.fillCalls, Code.noFrames] at he ⊢; exact ih he
  | call m body ih =>
    cases body with
    | block is =>
      cases is with
      | nil => exact hb
      | cons i is => exact he
    | _ => simp only [Code.fillCalls, Code.noFrames] at he ⊢; exact ih he
  | frame i x j ih => simp only [Code.noFrames, Bool.false_eq_true] at he
  | icall i m x y => simp only [Code.fillCalls]; exact he

/-- What the kernel evaluates of key generation, for each parameter set:
with `thash4` a hole, it has no frames and writes no PSTATE.DIT. -/
theorem stub_ok {p : Params} (hp : Shake6 p) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Shake.keyGen p (stubOf f)) = true ∧
      (Impl.SlhDsa.AArch64.Shake.keyGen p (stubOf f)).aarch64Depth = 0 ∧
      (Impl.SlhDsa.AArch64.Shake.xmssCode p (stubOf f)).noFrames = true := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

theorem t4_side {p : Params} (T : Thash4Impl p.n) (set : String) :
    sideAll (fun i => !i.writesDit) (fnsOf p T set).t4 = true ∧ (fnsOf p T set).t4.aarch64Depth = 0 ∧
      (fnsOf p T set).t4.noFrames = true := by
  have e : (fnsOf p T set).t4 = T.code := T.code_eq.symm
  rw [e]
  exact ⟨T.side, T.depth, T.noFrames⟩

/-- `xmssTree` over `T` has no frames. -/
theorem xmss_noFrames {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    (Impl.SlhDsa.AArch64.Shake.xmssCode p (fnsOf p T set)).noFrames = true := by
  rw [xmss_fill]
  exact noFrames_fillCalls (t4_side T set).2.2 (stub_ok hp _).2.2

theorem keyGen_side {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Shake.keyGen p (fnsOf p T set)) = true ∧
      (Impl.SlhDsa.AArch64.Shake.keyGen p (fnsOf p T set)).aarch64Depth = 0 := by
  have h := stub_ok hp (fnsOf p T set)
  have ht := t4_side T set
  rw [keyGen_fill]
  refine ⟨sideAll_fillCalls ht.1 h.1, ?_⟩
  have := Code.aarch64Depth_fillCalls_le (fnsOf p T set).t4name (fnsOf p T set).t4
    (Impl.SlhDsa.AArch64.Shake.keyGen p (stubOf (fnsOf p T set)))
  rw [h.2.1, ht.2.1] at this
  omega

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [this, hi, hn]

theorem keyGenOk (p : Params) :
    ScrubAllOk (keyGenContract p AArch64.abi 0) 0 ((keyGenSig p).retBits AArch64.abi.ptrBits) :=
  scrubAllOk_regs0 (sig := keyGenSig p) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seeds, sk, pk, sc], _ =>
      simp only [keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show (Spec.Sha3.bytesAt m₂ sk p.skLen, Spec.Sha3.bytesAt m₂ pk p.pkLen) = _
      rw [bytesAt_of (Nat.le_refl _) hb.2.1, bytesAt_of (Nat.le_refl _) hb.2.2.1]
      exact h

/-- `vg_slhdsa_shake_*_keygen` as emitted, over any implementation `T` of
`thash4` and an `xmssTree` over it verified against its contract, meets its
contract in constant time and returns without secret residue. -/
theorem keyGen_scrubbed {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (module name set : String)
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p (fnsOf p T set)) (xmssContract p)) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.keyGen p (fnsOf p T set))
      ((keyGenApi p module name).contract AArch64.abi 0) 0 := by
  have hv := keyGen_verified hp hx (xmss_noFrames hp T set)
  have hs := keyGen_side hp T set
  exact ⟨Verified.scrubAll0 clearAll_wf hv (by decide) (keyGenOk p),
    noResidue_scrubAll0 clearAll_wf (clearAll_keeps _) hv hs.2
      (Code.all_of_allInstrs (allInstrs_of_sideAll hs.1)) (by decide), fun ty _ h => by cases ty <;> cases h⟩

theorem keyGen_spSafe (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    (Impl.SlhDsa.AArch64.Fn.keyGen p f).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

/-- `xmssTree` over `T`, as key generation and signing call it. -/
theorem xmssV {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p (fnsOf p T set)) (xmssContract p) := by
  have e : Impl.SlhDsa.AArch64.Shake.xmssCode p (fnsOf p T set) =
      Impl.SlhDsa.AArch64.Xmss.xmssTree ⟨p.n, p.len⟩ p.hp (fnsOf p T set).t4name
        (fnsOf p T set).wotsName (fnsOf p T set).levelsName T.code := by
    rw [T.code_eq]; rfl
  rw [e]
  exact Xmss.xmss_verified hp.sz hp.hps T _ _ _

/-! The parameter sets, as their registrations name them. -/

theorem keyGen128s_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.keyGen shake_128s (fnsOf shake_128s T "128s"))
      (keyGenShake_128sApi.contract AArch64.abi 0) 0 :=
  keyGen_scrubbed (.inl rfl) T _ _ "128s" (xmssV (.inl rfl) T "128s")

theorem keyGen128s_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.AArch64.Fn.keyGen shake_128s (fnsOf shake_128s T "128s")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafe _ _

theorem keyGen128f_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.keyGen shake_128f (fnsOf shake_128f T "128f"))
      (keyGenShake_128fApi.contract AArch64.abi 0) 0 :=
  keyGen_scrubbed (.inr (.inl rfl)) T _ _ "128f" (xmssV (.inr (.inl rfl)) T "128f")

theorem keyGen128f_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.AArch64.Fn.keyGen shake_128f (fnsOf shake_128f T "128f")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafe _ _

theorem keyGen192s_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.keyGen shake_192s (fnsOf shake_192s T "192s"))
      (keyGenShake_192sApi.contract AArch64.abi 0) 0 :=
  keyGen_scrubbed (.inr (.inr (.inl rfl))) T _ _ "192s" (xmssV (.inr (.inr (.inl rfl))) T "192s")

theorem keyGen192s_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.AArch64.Fn.keyGen shake_192s (fnsOf shake_192s T "192s")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafe _ _

theorem keyGen192f_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.keyGen shake_192f (fnsOf shake_192f T "192f"))
      (keyGenShake_192fApi.contract AArch64.abi 0) 0 :=
  keyGen_scrubbed (.inr (.inr (.inr (.inl rfl)))) T _ _ "192f" (xmssV (.inr (.inr (.inr (.inl rfl)))) T "192f")

theorem keyGen192f_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.AArch64.Fn.keyGen shake_192f (fnsOf shake_192f T "192f")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafe _ _

theorem keyGen256s_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.keyGen shake_256s (fnsOf shake_256s T "256s"))
      (keyGenShake_256sApi.contract AArch64.abi 0) 0 :=
  keyGen_scrubbed (.inr (.inr (.inr (.inr (.inl rfl))))) T _ _ "256s" (xmssV (.inr (.inr (.inr (.inr (.inl rfl))))) T "256s")

theorem keyGen256s_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.AArch64.Fn.keyGen shake_256s (fnsOf shake_256s T "256s")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafe _ _

theorem keyGen256f_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.keyGen shake_256f (fnsOf shake_256f T "256f"))
      (keyGenShake_256fApi.contract AArch64.abi 0) 0 :=
  keyGen_scrubbed (.inr (.inr (.inr (.inr (.inr rfl))))) T _ _ "256f" (xmssV (.inr (.inr (.inr (.inr (.inr rfl))))) T "256f")

theorem keyGen256f_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.AArch64.Fn.keyGen shake_256f (fnsOf shake_256f T "256f")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafe _ _

end VG.Proof.SlhDsa.AArch64.KeyGen
