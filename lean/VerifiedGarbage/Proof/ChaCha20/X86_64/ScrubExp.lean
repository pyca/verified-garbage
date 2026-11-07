module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.Stream
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.AddrArith
public meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT
public meta import VerifiedGarbage.Proof.ChaCha20.Stream
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.Framework.Registration
public meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
public meta import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Proof.Framework.Mem
public meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Experiment: ChaCha20's `apply` without secret residue (x86-64)

`vg_chacha20_apply`, `vg_chacha20_apply_avx2` and `vg_chacha20_apply_avx512`,
scrubbed (`X86_64.Scrub.scrubReg`), named with `_scrub`, for measuring. The residue analysis starts with the 8 bytes of
the state that hold the number of bytes of keystream left (`leftAt`) public:
the contract declares that number as leaked, so two runs that agree on what
is public agree on those bytes (`pubOk`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.ScrubExp

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.X86_64.RScrub VG.Spec.ChaCha20
open VG.X86_64.Taint (byteAddr region)

/-- The bytes of keystream left: bytes 128–135 of the state (buffer 0). -/
def pubs : List (Nat × Nat × Nat) := [(0, 128, 8)]

theorem applyOut (stack : Nat) : PostOut (applyContract X86_64.abi stack) (applySig.retBits 64) := by
  unfold applyContract
  refine postOut_of_local ScrubAbi.plain ?_
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [applySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  have hd : Spec.ChaCha20.bytesAt m₂ dt ln.toNat = Spec.ChaCha20.bytesAt m₁ dt ln.toNat := by
    simp only [Spec.ChaCha20.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  obtain ⟨k, rs, -⟩ := Proof.ChaCha20.stream_congr hs
  show keyAt m₂ st = _ ∧ _
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [k]; exact h1, ?_⟩
  have e64 : (ArgWord.int X86_64.abi.ptrBits).ofRaw ln = ln := BitVec.setWidth_eq ln
  rw [e64] at h2 ⊢
  split at h2 <;> split <;> rename_i h₁ h₂
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩
  · exact absurd h₁ h₂
  · exact absurd h₂ h₁
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩

theorem rdi_base : (Reg.rdi, 0, 0) ∈ basesAux (wrInfo applySig.params 0) 0 := by decide

theorem pubOk (stack : Nat) : PubOk (applyContract X86_64.abi stack) pubs := by
  intro s₁ s₂ h₁ h₂ hp ho sl hsl j hj₁ hj₂
  simp only [pubs, List.mem_singleton] at hsl
  subst hsl
  simp only at hj₁ hj₂
  have hb : ∀ s, (applyContract X86_64.abi stack).pre s → byteAddr s 0 j = s.gpr .rdi + BitVec.ofNat 64 j :=
    fun s h => by
      have := (init_wf (sig := applySig) (pubs := []) ScrubAbi.plain h).1.2 (.rdi, 0, 0) rdi_base
      simp only [BitVec.add_zero] at this
      simp only [byteAddr, ← this]
  rw [hb s₁ h₁, hb s₂ h₂]
  obtain ⟨-, -, hg, -⟩ := ho
  have hdi : s₁.gpr .rdi = s₂.gpr .rdi := hg .rdi (by decide)
  have hl : leftAt s₁.mem (s₁.gpr .rdi) = leftAt s₂.mem (s₂.gpr .rdi) := by
    simp only [applyContract, Sig.contract, abi, argRegs] at hp
    have := hp.1.2
    change [leftAt s₁.mem (s₁.gpr .rdi)] = [leftAt s₂.mem (s₂.gpr .rdi)] at this
    exact (List.cons.inj this).1
  have hw : s₁.mem.readW (s₁.gpr .rdi + 128) 64 = s₂.mem.readW (s₂.gpr .rdi + 128) 64 :=
    BitVec.eq_of_toNat_eq hl
  have e : ∀ (m : Mem) (p : Addr), m (p + BitVec.ofNat 64 j) =
      (m.readW (p + 128) 64).extractLsb' (8 * (j - 128)) 8 := fun m p => by
    show _ = ((m.read (p + 128) 8).setWidth 64).extractLsb' (8 * (j - 128)) 8
    rw [BitVec.setWidth_eq, Mem.extractLsb'_read m _ (by omega),
      show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, Offset.add_add, Nat.add_sub_cancel' hj₁]
  rw [e s₁.mem, e s₂.mem, hw]

/-- `apply` over the implementation `v` of `vg_chacha20_xor`, with suffix `sfx`. -/
def applyR (v : XorImpl) (sfx : String) : Registration Spec.ChaCha20.applyApi X86_64.target where
  suffix := sfx
  code := Impl.ChaCha20.X86_64.Stream.apply v.callee
  stack := 24
  verified := Proof.ChaCha20.X86_64.Stream.apply_verified v
  spSafe := Proof.ChaCha20.X86_64.Stream.apply_spSafe v
  features := v.features

def scalarR := applyR .scalar "_scrub"
def avx2R := applyR .avx2 "_avx2_scrub"
def avx512R := applyR .avx512 "_avx512_scrub"

def scalarKs : List Nat := keep_for% Spec.ChaCha20.applyApi.sig scalarR.stack scalarR.code pubs
def avx2Ks : List Nat := keep_for% Spec.ChaCha20.applyApi.sig avx2R.stack avx2R.code pubs
def avx512Ks : List Nat := keep_for% Spec.ChaCha20.applyApi.sig avx512R.stack avx512R.code pubs

theorem scalarRes : ResOk scalarR.code scalarR.contract scalarR.stack scalarKs (chunks scalarR.stack) :=
  resOk_reg scalarR scalarKs (pubs := pubs) (by decide) (pubOk _) (by taint_decide)
theorem avx2Res : ResOk avx2R.code avx2R.contract avx2R.stack avx2Ks (chunks avx2R.stack) :=
  resOk_reg avx2R avx2Ks (pubs := pubs) (by decide) (pubOk _) (by taint_decide)
theorem avx512Res : ResOk avx512R.code avx512R.contract avx512R.stack avx512Ks (chunks avx512R.stack) :=
  resOk_reg avx512R avx512Ks (pubs := pubs) (by decide) (pubOk _) (by taint_decide)

def applyScalar := scrubReg scalarR .sse scalarKs (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (applyOut _) scalarRes rfl
def applyAvx2 := scrubReg avx2R .avx avx2Ks (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (applyOut _) avx2Res rfl
def applyAvx512 := scrubReg avx512R .avx avx512Ks (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (applyOut _) avx512Res rfl

theorem applyScalar_noResidue : NoResidue applyScalar.code scalarR.contract (applySig.retBits 64) :=
  scrubReg_noResidue scalarR .sse scalarKs _ _ _ _ _ _ scalarRes rfl
theorem applyAvx2_noResidue : NoResidue applyAvx2.code avx2R.contract (applySig.retBits 64) :=
  scrubReg_noResidue avx2R .avx avx2Ks _ _ _ _ _ _ avx2Res rfl
theorem applyAvx512_noResidue : NoResidue applyAvx512.code avx512R.contract (applySig.retBits 64) :=
  scrubReg_noResidue avx512R .avx avx512Ks _ _ _ _ _ _ avx512Res rfl

end VG.Proof.ChaCha20.X86_64.ScrubExp
