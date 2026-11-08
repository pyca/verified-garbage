module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.Stream
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ChaCha20's `apply` without secret residue (x86-64)

`vg_chacha20_apply`, for each implementation of `vg_chacha20_xor`, scrubbed
where the residue analysis allows it (`X86_64.RScrub.autoScrub`). The
analysis starts with the 8 bytes of the state that hold the number of bytes of keystream left (`leftAt`) public:
the contract declares that number as leaked, so two runs that agree on what
is public agree on those bytes (`pubOk`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.X86_64.RScrub VG.Spec.ChaCha20
open VG.X86_64.Taint (byteAddr region)


/-- A state whose first 136 bytes are unchanged represents the same key and
keystream. -/
theorem stream_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 136, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    keyAt m' p = keyAt m p ∧ restAt m' p = restAt m p ∧ leftAt m' p = leftAt m p := by
  have hb : ∀ a n, a + n ≤ 136 → bytesAt m' (p + BitVec.ofNat 64 a) n = bytesAt m (p + BitVec.ofNat 64 a) n :=
    fun a n hn => List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      simpa only [Offset.add_add] using h (a + i) (by omega_using [hn, this])
  have hw : ∀ a w, a + w / 8 ≤ 136 → m'.readW (p + BitVec.ofNat 64 a) w = m.readW (p + BitVec.ofNat 64 a) w :=
    fun a w hn => Mem.readW_congr fun i hi => by
      simpa only [Offset.add_add] using h (a + i) (by omega_using [hn, hi])
  have hl : leftAt m' p = leftAt m p := by
    simp only [leftAt]; rw [show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, hw _ _ (by decide)]
  have hs : stateAt m' p = stateAt m p := by
    apply Vector.ext; intro i hi
    simp only [stateAt, Vector.getElem_ofFn]
    exact hw _ _ (by omega_using [hi])
  refine ⟨by simp only [keyAt]; exact hb 16 32 (by decide), ?_, hl⟩
  simp only [restAt, hl, hs]
  rw [hb _ _ (by omega_using [])]

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
  obtain ⟨k, rs, -⟩ := stream_congr hs
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

theorem pubOk (stack : Nat) : PubOk (applyContract X86_64.abi stack) applyPubs := by
  intro s₁ s₂ h₁ h₂ hp ho sl hsl j hj₁ hj₂
  simp only [applyPubs, List.mem_singleton] at hsl
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

/-- `vg_chacha20_apply` over the implementation `v` of `vg_chacha20_xor`,
without secret residue where `v` gives its analysis (`XorImpl.apply`), with
the bytes left public (`pubOk`). -/
def applyReg (v : XorImpl) : Registration Spec.ChaCha20.applyApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.ChaCha20.X86_64.Stream.apply v.callee
    stack := 24
    verified := Proof.ChaCha20.X86_64.Stream.apply_verified v
    spSafe := Proof.ChaCha20.X86_64.Stream.apply_spSafe v
    features := v.features } (applyOut _) applyPubs (pubOk _) v.apply

end VG.Proof.ChaCha20.X86_64.Scrub
